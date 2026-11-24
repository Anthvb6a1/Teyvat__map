"""
Teyvat Interactive Map Viewer
─────────────────────────────
• Tiles: lazy-load theo viewport, cache RAM + disk
• Markers: hiển thị icon từ local folder, tự tải từ URL nếu thiếu
• Bộ lọc: lưới icon để tìm kiếm, bật/tắt từng loại điểm
• Anchors: tên vùng đất (parent + child)
• Cache: tiles / anchors đều có TTL 24h
• Robust: đọc được file JSON bị cắt cụt, có BOM, nhiều format

Phím tắt:
    H  - bật/tắt markers
    U  - bật/tắt markers underground
    K  - bật/tắt tên vùng đất
    R  - nạp lại markers từ spot_kinds.json + refresh anchors
    Home - fit toàn map
"""
import sys, math, json, time, gzip, re, argparse, unicodedata, marshal
from collections import Counter, OrderedDict
from io import BytesIO
from pathlib import Path

import requests
from PySide6.QtCore import Qt, QSize, QObject, QRunnable, Signal, Slot, QThread, QThreadPool, QTimer
from PySide6.QtGui import QPixmap, QImage, QPainter, QColor, QFont, QPen, QIcon
from PySide6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QLabel, QLineEdit, QPushButton, QScrollArea, QToolButton,
)


# ============================================================
# CONFIG
# ============================================================
MAP_ID = 2
TILE_SIZE = 256
TILE_FORMAT = "webp"

HEADERS = {
    "Referer": "https://act.hoyolab.com/",
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                  "AppleWebKit/537.36 (KHTML, like Gecko) "
                  "Chrome/122.0 Safari/537.36",
}

API_BASE = "https://sg-public-api-static.hoyolab.com/common/map_user/ys_obc"
API_INFO = f"{API_BASE}/v1/map/info"
API_ANCHORS = f"{API_BASE}/v1/map/map_anchor/list"
TILE_BASE_FMT = "https://act-webstatic.hoyoverse.com/map_manage/map/{map_id}/{version}/"

CACHE_ROOT = Path.home() / ".cache" / "teyvat_map"
TILE_CACHE_DIR = CACHE_ROOT / str(MAP_ID)
ANCHORS_CACHE = CACHE_ROOT / "anchors_cache.json.gz"
MARKERS_CACHE = CACHE_ROOT / "markers_cache.bin"
LABELS_CACHE = CACHE_ROOT / "labels_cache.bin"
CACHE_TTL = 24 * 3600
USER_SETTINGS_FILE = CACHE_ROOT / "user_settings.json"

BASE_DIR = Path(__file__).parent
SPOT_KINDS_LOCAL = BASE_DIR / "spot_kinds.json"
ICONS_FOLDER = BASE_DIR / "icons_data" / "icons"
MARKER_PIN_PATH = BASE_DIR / "icons_data" / "marker_pin.png"
UNDERGROUND_MARKER_URL = (
    "https://webstatic.hoyoverse.com/upload/static-resource/2022/12/29/"
    "65eebf6b7a8b5f4a86302f4c0ac9deca_5775722703419134293.png"
)
UNDERGROUND_MARKER_PATH = CACHE_ROOT / "underground_marker.png"
MARKER_PIN_TIP_Y = 0.97
MARKER_PIN_ICON_CENTER_Y = 0.38
MARKER_PIN_ICON_SCALE = 0.52
UNDERGROUND_MARKER_TIP_Y = 1.0
UNDERGROUND_MARKER_ICON_CENTER_Y = 0.45
UNDERGROUND_MARKER_ICON_SCALE = 0.50

FALLBACK_VERSION = "bd70cde160dbd523926208d9fa8961a1"
FALLBACK_TOTAL = (16384, 16384)
FALLBACK_MIN_Z = -6
FALLBACK_MAX_Z = 0

ICON_SIZES = {"far": 32, "mid": 48, "near": 64, "hi": 96}
MARKER_SCALE = 0.85


def load_user_settings():
    try:
        if USER_SETTINGS_FILE.exists():
            data = json.loads(USER_SETTINGS_FILE.read_text(encoding="utf-8"))
            return data if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError) as exc:
        print(f"⚠️ Không đọc được cấu hình: {exc}")
    return {}


def save_user_settings(settings):
    try:
        USER_SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
        USER_SETTINGS_FILE.write_text(
            json.dumps(settings, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
    except OSError as exc:
        print(f"⚠️ Không lưu được cấu hình: {exc}")


# ============================================================
# MARKER + INDEX
# ============================================================
class Marker:
    __slots__ = ("id", "label_id", "x", "y", "area_id", "icon_sign",
                 "point_group", "underground")
    def __init__(self, d):
        self.id = d.get("id")
        self.label_id = d.get("label_id", 0)
        self.x = float(d.get("x_pos", 0))
        self.y = float(d.get("y_pos", 0))
        self.area_id = d.get("area_id", 0)
        self.icon_sign = d.get("icon_sign", 0)
        self.point_group = d.get("point_group")
        ext_attrs = d.get("ext_attrs_map") or {}
        if not isinstance(ext_attrs, dict):
            ext_attrs = {}
        underground_value = (
            d.get("Underground")
            if "Underground" in d else d.get("underground")
        )
        if underground_value is None:
            underground_value = ext_attrs.get("Underground",
                                              ext_attrs.get("underground"))
        self.underground = (
            underground_value is True
            or str(underground_value).strip().lower() == "true"
            or self.point_group is not None
        )


class MarkerIndex:
    def __init__(self, markers, cell=500):
        self.cell = cell
        self.grid = {}
        for m in markers:
            key = (int(m.x // cell), int(m.y // cell))
            self.grid.setdefault(key, []).append(m)

    def query(self, x0, y0, x1, y1):
        cs = self.cell
        cx0 = int(math.floor(x0 / cs))
        cy0 = int(math.floor(y0 / cs))
        cx1 = int(math.floor(x1 / cs))
        cy1 = int(math.floor(y1 / cs))
        out = []
        for cx in range(cx0, cx1 + 1):
            for cy in range(cy0, cy1 + 1):
                out.extend(self.grid.get((cx, cy), []))
        return out


def _label_color(label_id):
    hue = (label_id * 137) % 360
    c = QColor()
    c.setHsl(hue, 210, 155)
    return c


# ============================================================
# ANCHOR
# ============================================================
class Anchor:
    __slots__ = ("id", "name", "l_x", "l_y", "r_x", "r_y", "parent_id", "children")
    def __init__(self, d):
        self.id = str(d.get("id", ""))
        self.name = d.get("name", "")
        self.l_x = float(d.get("l_x", 0))
        self.l_y = float(d.get("l_y", 0))
        self.r_x = float(d.get("r_x", 0))
        self.r_y = float(d.get("r_y", 0))
        self.parent_id = str(d.get("parent_id", "0"))
        self.children = [Anchor(c) for c in (d.get("children") or [])]

    def to_dict(self):
        return {
            "id": self.id, "name": self.name,
            "l_x": self.l_x, "l_y": self.l_y,
            "r_x": self.r_x, "r_y": self.r_y,
            "parent_id": self.parent_id,
            "children": [c.to_dict() for c in self.children],
        }


# ============================================================
# ROBUST JSON PARSER (cho spot_kinds.json)
# ============================================================
def _extract_labels_from_parsed(data):
    if isinstance(data, list):
        return data
    if not isinstance(data, dict):
        return []

    root = data.get("data", data)
    if isinstance(root, dict):
        if isinstance(root.get("label_list"), list):
            return root["label_list"]
        if isinstance(root.get("tree"), list):
            items = []
            for p in root["tree"]:
                items.extend(p.get("children", []))
            return items
        if "id" in root and ("icon" in root or "icon_url" in root):
            return [root]
    elif isinstance(root, list):
        return root
    return []


def _parse_spot_kinds_json(raw_text):
    """Parse text JSON — chấp nhận file bị cắt cụt, có BOM, nhiều format."""
    if raw_text.startswith("\ufeff"):
        raw_text = raw_text[1:]
    raw_text = raw_text.strip()
    if not raw_text:
        raise ValueError("File rỗng")

    def try_extract(text):
        try:
            return _extract_labels_from_parsed(json.loads(text))
        except json.JSONDecodeError:
            return None

    # 1) Parse nguyên
    r = try_extract(raw_text)
    if r:
        return r

    # 2) Thử bọc ngoặc
    for w in [
        "{" + raw_text + "}",
        '{"data": {' + raw_text + "}}",
        '{"label_list": ' + raw_text + "}",
        '{"data": {"label_list": ' + raw_text + "}}",
        '{"data": {"tree": [{"children": ' + raw_text + "}]}}",
    ]:
        r = try_extract(w)
        if r:
            return r

    # 3) File bị cắt/rác → trích từng object qua raw_decode
    dec = json.JSONDecoder()
    labels = []
    seen = set()
    for m in re.finditer(r'\{\s*"id"\s*:', raw_text):
        try:
            obj, _ = dec.raw_decode(raw_text, m.start())
        except json.JSONDecodeError:
            continue
        if not isinstance(obj, dict):
            continue
        if "icon" not in obj and "icon_url" not in obj:
            continue
        oid = obj.get("id")
        if oid in seen:
            continue
        seen.add(oid)
        labels.append(obj)

    if labels:
        print(f"⚠️ File JSON bị cắt/rác — trích được {len(labels)} label hợp lệ")
        print(f"   → Khuyến nghị: tải lại file spot_kinds.json đầy đủ")
        return labels

    preview = raw_text[:200].replace("\n", "\\n")
    raise ValueError(f"Không parse được. Đầu file: {preview}")


# ============================================================
# BUILD ICON MAP (label_id → {file, url, name})
# ============================================================
def build_label_icon_map():
    if not SPOT_KINDS_LOCAL.exists():
        print(f"⚠️ Thiếu {SPOT_KINDS_LOCAL} → chấm màu")
        return {}

    source_stat = SPOT_KINDS_LOCAL.stat()
    source_signature = (source_stat.st_size, source_stat.st_mtime_ns)
    raw_items = None
    labels_cache_hit = False
    if LABELS_CACHE.exists():
        try:
            cached = marshal.loads(LABELS_CACHE.read_bytes())
            cached_items = cached.get("labels") if isinstance(cached, dict) else None
            if (isinstance(cached, dict)
                    and cached.get("signature") == source_signature
                    and isinstance(cached_items, list)
                    and all(isinstance(item, dict) for item in cached_items)):
                raw_items = cached_items
                labels_cache_hit = True
        except (OSError, EOFError, TypeError, ValueError) as exc:
            print(f"⚠️ Labels cache không dùng được, đọc nguồn: {exc}")

    if raw_items is None:
        try:
            raw = SPOT_KINDS_LOCAL.read_text(encoding="utf-8-sig")
        except UnicodeDecodeError:
            try:
                raw = SPOT_KINDS_LOCAL.read_text(encoding="utf-16")
            except Exception as e:
                print(f"⚠️ Đọc file fail: {e}")
                return {}

        try:
            raw_items = _parse_spot_kinds_json(raw)
        except Exception as e:
            print(f"⚠️ Parse lỗi: {e}")
            return {}

        if not raw_items:
            print("⚠️ Parse OK nhưng 0 label")
            return {}

        try:
            LABELS_CACHE.parent.mkdir(parents=True, exist_ok=True)
            temp_cache = LABELS_CACHE.with_suffix(".bin.tmp")
            temp_cache.write_bytes(marshal.dumps({
                "signature": source_signature,
                "labels": raw_items,
            }))
            temp_cache.replace(LABELS_CACHE)
        except (OSError, ValueError) as exc:
            print(f"⚠️ Không lưu được labels cache: {exc}")

    if labels_cache_hit:
        print(f"📦 Labels cache: {len(raw_items)}")
    else:
        print(f"📂 Parsed {len(raw_items)} label từ spot_kinds.json")

    local_files = {}
    if ICONS_FOLDER.exists():
        for f in ICONS_FOLDER.iterdir():
            if f.is_file() and f.suffix.lower() in (".png", ".webp", ".jpg", ".jpeg"):
                local_files[f.name] = f
    print(f"📁 Icons trên disk: {len(local_files)} file")

    result = {}
    have_local = need_dl = no_url = 0
    missing_samples = []

    for item in raw_items:
        if not isinstance(item, dict):
            continue
        lid = item.get("id")
        if lid is None:
            continue
        name = item.get("name", "")
        url = item.get("icon") or item.get("icon_url") or ""
        if not url:
            no_url += 1
            continue

        clean_url = url.split("?")[0]
        filename = clean_url.rsplit("/", 1)[-1]
        local_path = local_files.get(filename)

        if local_path:
            result[lid] = {
                "file": local_path, "url": clean_url, "name": name,
                "parent_id": item.get("parent_id"),
            }
            have_local += 1
        else:
            result[lid] = {
                "file": None, "url": clean_url, "name": name,
                "parent_id": item.get("parent_id"),
            }
            need_dl += 1
            if len(missing_samples) < 3:
                missing_samples.append(filename)

    print(f"✅ Label→Icon: {len(result)} label "
          f"(local={have_local}, cần tải={need_dl}, thiếu URL={no_url})")
    if missing_samples:
        print(f"   VD file thiếu: {missing_samples}")
    return result


# ============================================================
# FETCH HELPERS
# ============================================================
def fetch_anchors(force=False):
    if not force and ANCHORS_CACHE.exists():
        age = time.time() - ANCHORS_CACHE.stat().st_mtime
        if age < CACHE_TTL:
            try:
                with gzip.open(ANCHORS_CACHE, "rt", encoding="utf-8") as f:
                    data = json.load(f)
                anchors = [Anchor(a) for a in data]
                print(f"📦 Anchors cache: {len(anchors)} parents")
                return anchors
            except Exception:
                pass

    try:
        r = requests.get(API_ANCHORS,
                         params={"map_id": MAP_ID, "app_sn": "ys_obc", "lang": "vi-vn"},
                         headers=HEADERS, timeout=20)
        d = r.json()
        if d.get("retcode") != 0:
            print(f"⚠️ anchors retcode={d.get('retcode')}")
            return []
        anchors = [Anchor(a) for a in d.get("data", {}).get("list", [])]
        ANCHORS_CACHE.parent.mkdir(parents=True, exist_ok=True)
        with gzip.open(ANCHORS_CACHE, "wt", encoding="utf-8") as f:
            json.dump([a.to_dict() for a in anchors], f)
        print(f"✅ Anchors fetched: {len(anchors)} parents")
        return anchors
    except Exception as e:
        print(f"⚠️ fetch anchors fail: {e}")
        return []


def fetch_markers():
    if not SPOT_KINDS_LOCAL.exists():
        raise FileNotFoundError(f"Thiếu file markers: {SPOT_KINDS_LOCAL}")

    source_stat = SPOT_KINDS_LOCAL.stat()
    source_signature = (source_stat.st_size, source_stat.st_mtime_ns)
    if MARKERS_CACHE.exists():
        try:
            cached = marshal.loads(MARKERS_CACHE.read_bytes())
            cached_markers = cached.get("markers") if isinstance(cached, dict) else None
            if (isinstance(cached, dict)
                    and cached.get("signature") == source_signature
                    and isinstance(cached_markers, list)
                    and all(isinstance(marker, dict) for marker in cached_markers)):
                print(f"📦 Markers cache: {len(cached_markers)} (spot_kinds.json không đổi)")
                return cached_markers
        except (OSError, EOFError, TypeError, ValueError) as exc:
            print(f"⚠️ Markers cache không dùng được, đọc nguồn: {exc}")

    try:
        data = json.loads(SPOT_KINDS_LOCAL.read_text(encoding="utf-8-sig"))
    except UnicodeDecodeError:
        data = json.loads(SPOT_KINDS_LOCAL.read_text(encoding="utf-16"))

    root = data.get("data", data) if isinstance(data, dict) else data
    if not isinstance(root, dict) or not isinstance(root.get("point_list"), list):
        raise ValueError(f"Không tìm thấy data.point_list trong {SPOT_KINDS_LOCAL}")

    markers = root["point_list"]
    if not all(isinstance(marker, dict) for marker in markers):
        raise ValueError(f"point_list chứa marker không hợp lệ trong {SPOT_KINDS_LOCAL}")
    required_fields = ("x_pos", "y_pos", "label_id")
    if any(any(field not in marker for field in required_fields) for marker in markers):
        raise ValueError(f"Marker thiếu x_pos, y_pos hoặc label_id trong {SPOT_KINDS_LOCAL}")

    try:
        MARKERS_CACHE.parent.mkdir(parents=True, exist_ok=True)
        temp_cache = MARKERS_CACHE.with_suffix(".bin.tmp")
        temp_cache.write_bytes(marshal.dumps({
            "signature": source_signature,
            "markers": markers,
        }))
        temp_cache.replace(MARKERS_CACHE)
    except (OSError, ValueError) as exc:
        print(f"⚠️ Không lưu được markers cache: {exc}")

    print(f"📂 Đọc markers nguồn: {len(markers)} (spot_kinds.json)")
    return markers


# ============================================================
# WORKERS
# ============================================================
class MetaWorker(QThread):
    result = Signal(object, object, str, int, int)
    def run(self):
        try:
            r = requests.get(API_INFO,
                             params={"map_id": MAP_ID, "app_sn": "ys_obc", "lang": "vi-vn"},
                             headers=HEADERS, timeout=15)
            info = r.json()["data"]["info"]["detail_v2"]
            self.result.emit(
                tuple(info["total_size"]),
                tuple(info.get("origin", [0, 0])),
                info["map_version"],
                info.get("min_zoom", FALLBACK_MIN_Z),
                info.get("max_zoom", FALLBACK_MAX_Z),
            )
        except Exception as e:
            print(f"⚠️ meta fail: {e}")
            self.result.emit(None, (0, 0), FALLBACK_VERSION,
                             FALLBACK_MIN_Z, FALLBACK_MAX_Z)


class MarkerWorker(QThread):
    result = Signal(list)
    def run(self):
        try:
            self.result.emit(fetch_markers())
        except Exception as e:
            print(f"❌ markers fail: {e}")
            self.result.emit([])


class AnchorWorker(QThread):
    result = Signal(list)
    def __init__(self, force=False):
        super().__init__()
        self.force = force
    def run(self):
        try:
            self.result.emit(fetch_anchors(force=self.force))
        except Exception as e:
            print(f"❌ anchors fail: {e}")
            self.result.emit([])


class TileSignals(QObject):
    done = Signal(int, int, int, bytes)


class TileWorker(QRunnable):
    def __init__(self, url, tx, ty, tz, cache_path):
        super().__init__()
        self.url, self.tx, self.ty, self.tz = url, tx, ty, tz
        self.cache_path = cache_path
        self.signals = TileSignals()

    def run(self):
        try:
            r = requests.get(self.url, headers=HEADERS, timeout=15)
            if r.ok and len(r.content) > 100:
                try:
                    self.cache_path.parent.mkdir(parents=True, exist_ok=True)
                    self.cache_path.write_bytes(r.content)
                except Exception:
                    pass
                self.signals.done.emit(self.tx, self.ty, self.tz, r.content)
                return
        except Exception:
            pass
        self.signals.done.emit(self.tx, self.ty, self.tz, b"")


class IconSignals(QObject):
    done = Signal(int, str, bytes)  # label_id, filename, data


class IconWorker(QRunnable):
    def __init__(self, url, label_id, save_path):
        super().__init__()
        self.url = url
        self.label_id = label_id
        self.save_path = save_path
        self.signals = IconSignals()

    def run(self):
        try:
            r = requests.get(self.url, headers=HEADERS, timeout=15)
            if r.ok and len(r.content) > 50:
                try:
                    self.save_path.parent.mkdir(parents=True, exist_ok=True)
                    self.save_path.write_bytes(r.content)
                except Exception:
                    pass
                self.signals.done.emit(self.label_id, self.save_path.name, r.content)
                return
        except Exception:
            pass
        self.signals.done.emit(self.label_id, self.save_path.name, b"")


# ============================================================
# MAP WIDGET
# ============================================================
class MapWidget(QWidget):
    MAX_TILE_CACHE = 800
    ZOOM_STEP = 0.25

    def __init__(self, tile_base, total_size, origin, min_z, max_z, markers,
                 settings=None):
        super().__init__()
        settings = settings or {}
        self.tile_base = tile_base
        self.total_size = total_size
        self.origin = origin

        self.tile_min_z = min_z
        self.tile_max_z = max_z
        self.min_zoom_ui = -10.0
        self.max_zoom_ui = max_z + 4.0

        self.zoom = -3.0
        self.center = (total_size[0] / 2 - origin[0],
                       total_size[1] / 2 - origin[1])

        # Markers
        self.markers = markers
        self.marker_index = MarkerIndex(markers) if markers else None
        self.marker_pin = QPixmap(str(MARKER_PIN_PATH))
        if self.marker_pin.isNull():
            raise RuntimeError(f"Không tải được ảnh khung marker: {MARKER_PIN_PATH}")
        self.underground_marker = QPixmap(str(UNDERGROUND_MARKER_PATH))
        if self.underground_marker.isNull():
            try:
                UNDERGROUND_MARKER_PATH.parent.mkdir(parents=True, exist_ok=True)
                r = requests.get(
                    UNDERGROUND_MARKER_URL,
                    headers=HEADERS,
                    timeout=20,
                )
                r.raise_for_status()
                UNDERGROUND_MARKER_PATH.write_bytes(r.content)
                self.underground_marker = QPixmap(
                    str(UNDERGROUND_MARKER_PATH))
            except Exception as exc:
                print(f"⚠️ Không tải được icon Underground: {exc}")
        self.icon_file_map = {}          # label_id → {file, url, name}
        self.icon_pixmap_cache = {}      # (label_id, size) → QPixmap
        self.marker_pixmap_cache = {}    # (label_id, size) → QPixmap
        self.underground_pixmap_cache = {}
        self.icon_pending = set()        # label_id đang tải
        self.icon_failed = set()         # label_id tải fail
        self.label_color_cache = {}
        self.visible_label_ids = None
        self.show_markers = settings.get("show_markers", True)
        self.show_underground = settings.get("show_underground", False)
        self.hovered_marker = None
        self.visible_marker_count = 0

        # Anchors
        self.anchors_parent = []
        self.anchors_child = []
        self.show_anchors = settings.get("show_anchors", True)
        self._font_cache = {}

        # Tiles
        self.tile_cache = OrderedDict()
        self.tile_pending = set()
        self.tile_failed = set()

        self.cache_dir = TILE_CACHE_DIR
        self.cache_dir.mkdir(parents=True, exist_ok=True)

        self.pool = QThreadPool.globalInstance()
        self.pool.setMaxThreadCount(8)

        self._dragging = False
        self._last_mouse = None

        self._retry_timer = QTimer(self)
        self._retry_timer.timeout.connect(self.tile_failed.clear)
        self._retry_timer.timeout.connect(self.icon_failed.clear)
        self._retry_timer.start(30000)

        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMinimumSize(900, 600)

    # ---------- Setup ----------
    def set_markers(self, markers):
        self.markers = markers
        self.marker_index = MarkerIndex(markers) if markers else None
        self.hovered_marker = None
        self.update()

    def set_visible_label_ids(self, label_ids):
        self.visible_label_ids = None if label_ids is None else set(label_ids)
        if (self.hovered_marker and self.visible_label_ids is not None
                and self.hovered_marker.label_id not in self.visible_label_ids):
            self.hovered_marker = None
        self.update()

    def set_icon_map(self, mapping):
        self.icon_file_map = mapping or {}
        self.icon_pixmap_cache.clear()
        self.marker_pixmap_cache.clear()
        self.icon_pending.clear()
        self.icon_failed.clear()
        have = sum(1 for v in self.icon_file_map.values() if v.get("file"))
        need = len(self.icon_file_map) - have
        print(f"✅ MapWidget: {len(self.icon_file_map)} icon "
              f"(local={have}, sẽ tải={need})")
        self.update()

    def set_anchors(self, anchors):
        parents, children = [], []
        def walk(a, top=False):
            (parents if top else children).append(a)
            for c in a.children:
                walk(c, False)
        for a in anchors:
            walk(a, True)
        self.anchors_parent = parents
        self.anchors_child = children
        print(f"✅ Anchors: {len(parents)} parents, {len(children)} children")
        self.update()

    # ---------- View ----------
    def clamped_tile_zoom(self):
        tz = int(math.floor(self.zoom + 0.5))
        return max(self.tile_min_z, min(self.tile_max_z, tz))

    def viewport_bounds(self):
        W, H = self.width(), self.height()
        s = 2 ** self.zoom
        hw, hh = W / (2 * s), H / (2 * s)
        cx, cy = self.center
        return (cx - hw, cy - hh, cx + hw, cy + hh)

    def update_min_zoom(self):
        if self.total_size[0] <= 0 or self.width() <= 0:
            return
        fit = min(math.log2(self.width() / self.total_size[0]),
                  math.log2(self.height() / self.total_size[1]))
        self.min_zoom_ui = fit
        if self.zoom < fit:
            self.zoom = fit
            self.update()

    def fit_to_window(self):
        self.update_min_zoom()
        self.zoom = self.min_zoom_ui
        ox, oy = self.origin
        self.center = (self.total_size[0] / 2 - ox,
                       self.total_size[1] / 2 - oy)
        self.update()

    def resizeEvent(self, ev):
        super().resizeEvent(ev)
        self.update_min_zoom()

    # ---------- Tiles ----------
    def _tile_cache_path(self, tx, ty, tz):
        return self.cache_dir / str(tz) / f"{tx}_{ty}.{TILE_FORMAT}"

    def _load_tile(self, tx, ty, tz):
        key = (tx, ty, tz)
        if key in self.tile_cache:
            self.tile_cache.move_to_end(key)
            return self.tile_cache[key]
        path = self._tile_cache_path(tx, ty, tz)
        if path.exists():
            pix = QPixmap(str(path))
            if not pix.isNull():
                self.tile_cache[key] = pix
                while len(self.tile_cache) > self.MAX_TILE_CACHE:
                    self.tile_cache.popitem(last=False)
                return pix
            try: path.unlink()
            except: pass
        return None

    def _request_tile(self, tx, ty, tz):
        key = (tx, ty, tz)
        if key in self.tile_cache or key in self.tile_pending or key in self.tile_failed:
            return
        z_str = ("N" if tz < 0 else "P") + str(abs(tz))
        url = f"{self.tile_base}{tx}_{ty}_{z_str}.{TILE_FORMAT}"
        self.tile_pending.add(key)
        w = TileWorker(url, tx, ty, tz, self._tile_cache_path(tx, ty, tz))
        w.signals.done.connect(self._on_tile_done)
        self.pool.start(w)

    @Slot(int, int, int, bytes)
    def _on_tile_done(self, tx, ty, tz, data):
        key = (tx, ty, tz)
        self.tile_pending.discard(key)
        if not data:
            self.tile_failed.add(key)
            return
        img = QImage.fromData(data)
        if img.isNull():
            try:
                from PIL import Image
                pil = Image.open(BytesIO(data)).convert("RGBA")
                w, h = pil.size
                img = QImage(pil.tobytes("raw", "RGBA"), w, h,
                             QImage.Format_RGBA8888).copy()
            except Exception:
                self.tile_failed.add(key)
                return
        self.tile_cache[key] = QPixmap.fromImage(img)
        while len(self.tile_cache) > self.MAX_TILE_CACHE:
            self.tile_cache.popitem(last=False)
        self.update()

    def _find_tile_fallback(self, tx, ty, tz):
        for n in (1, 2, 3):
            pz = tz - n
            if pz < self.tile_min_z - 1:
                break
            factor = 2 ** n
            px, py = tx // factor, ty // factor
            pix = self._load_tile(px, py, pz)
            if pix:
                sub = TILE_SIZE // factor
                return (pix, (tx % factor) * sub, (ty % factor) * sub, sub, sub)
        cz = tz + 1
        if cz <= self.tile_max_z + 1:
            fx, fy = tx * 2, ty * 2
            tls = [self._load_tile(fx, fy, cz),
                   self._load_tile(fx + 1, fy, cz),
                   self._load_tile(fx, fy + 1, cz),
                   self._load_tile(fx + 1, fy + 1, cz)]
            if all(tls):
                comp = QPixmap(TILE_SIZE, TILE_SIZE)
                comp.fill(Qt.transparent)
                cp = QPainter(comp)
                h = TILE_SIZE // 2
                cp.drawPixmap(0, 0, h, h, tls[0], 0, 0, TILE_SIZE, TILE_SIZE)
                cp.drawPixmap(h, 0, h, h, tls[1], 0, 0, TILE_SIZE, TILE_SIZE)
                cp.drawPixmap(0, h, h, h, tls[2], 0, 0, TILE_SIZE, TILE_SIZE)
                cp.drawPixmap(h, h, h, h, tls[3], 0, 0, TILE_SIZE, TILE_SIZE)
                cp.end()
                return (comp, 0, 0, TILE_SIZE, TILE_SIZE)
        return None

    # ---------- Icons ----------
    def _pick_icon_size(self):
        z = self.zoom
        if z <= -4: size = ICON_SIZES["far"]
        elif z <= -2: size = ICON_SIZES["mid"]
        elif z <= 0: size = ICON_SIZES["near"]
        else: size = ICON_SIZES["hi"]
        return max(1, round(size * MARKER_SCALE))

    def _get_icon_pixmap(self, label_id, size):
        info = self.icon_file_map.get(label_id)
        if not info:
            return None

        key = (label_id, size)
        if key in self.icon_pixmap_cache:
            return self.icon_pixmap_cache[key]

        # 1) Thử file local
        path = info.get("file")
        if path and path.exists():
            pix = QPixmap(str(path))
            if not pix.isNull():
                pix = pix.scaled(size, size, Qt.KeepAspectRatio,
                                 Qt.SmoothTransformation)
                self.icon_pixmap_cache[key] = pix
                return pix
            try: path.unlink()
            except: pass
            info["file"] = None

        # 2) Chưa có → tải từ URL
        if label_id in self.icon_failed:
            return None
        if label_id not in self.icon_pending:
            url = info.get("url")
            if url:
                filename = url.rsplit("/", 1)[-1]
                save_path = ICONS_FOLDER / filename
                self.icon_pending.add(label_id)
                w = IconWorker(url, label_id, save_path)
                w.signals.done.connect(self._on_icon_done)
                self.pool.start(w)

        return None  # chấm màu tạm

    @Slot(int, str, bytes)
    def _on_icon_done(self, label_id, filename, data):
        self.icon_pending.discard(label_id)
        if not data:
            self.icon_failed.add(label_id)
            return
        img = QImage.fromData(data)
        if img.isNull():
            self.icon_failed.add(label_id)
            return
        info = self.icon_file_map.get(label_id)
        if info:
            info["file"] = ICONS_FOLDER / filename
        # Xoá cache pixmap label này để render lại
        for k in list(self.icon_pixmap_cache.keys()):
            if k[0] == label_id:
                del self.icon_pixmap_cache[k]
        for k in list(self.marker_pixmap_cache.keys()):
            if k[0] == label_id:
                del self.marker_pixmap_cache[k]
        self.underground_pixmap_cache.clear()
        self.update()

    def _get_fallback_pixmap(self, label_id, size):
        key = (label_id, size, "fallback")
        if key in self.icon_pixmap_cache:
            return self.icon_pixmap_cache[key]
        color = self.label_color_cache.get(label_id)
        if color is None:
            color = _label_color(label_id)
            self.label_color_cache[label_id] = color
        pix = QPixmap(size, size)
        pix.fill(Qt.transparent)
        pp = QPainter(pix)
        pp.setRenderHint(QPainter.Antialiasing, True)
        pp.setBrush(color)
        pp.setPen(QPen(Qt.white, max(1, size // 10)))
        m = max(1, size // 10)
        pp.drawEllipse(m, m, size - 2 * m, size - 2 * m)
        pp.end()
        self.icon_pixmap_cache[key] = pix
        return pix

    def _get_marker_pixmap(self, label_id, size):
        key = (label_id, size)
        if key in self.marker_pixmap_cache:
            return self.marker_pixmap_cache[key]

        pin_width = max(1, round(size * self.marker_pin.width()
                                  / self.marker_pin.height()))
        icon_size = max(1, round(pin_width * MARKER_PIN_ICON_SCALE))
        icon = self._get_icon_pixmap(label_id, icon_size)
        has_icon = icon is not None
        if icon is None:
            icon = self._get_fallback_pixmap(label_id, max(6, icon_size // 2))

        marker = QPixmap(pin_width, size)
        marker.fill(Qt.transparent)
        painter = QPainter(marker)
        painter.setRenderHint(QPainter.SmoothPixmapTransform, True)
        painter.drawPixmap(0, 0, pin_width, size, self.marker_pin)
        icon_x = (pin_width - icon.width()) // 2
        icon_y = round(size * MARKER_PIN_ICON_CENTER_Y - icon.height() / 2)
        painter.drawPixmap(icon_x, icon_y, icon)
        painter.end()

        if has_icon:
            self.marker_pixmap_cache[key] = marker
        return marker

    def _get_underground_marker_pixmap(self, label_id, size):
        key = (label_id, size)
        if key in self.underground_pixmap_cache:
            return self.underground_pixmap_cache[key]
        if self.underground_marker.isNull():
            return None

        frame = self.underground_marker.scaled(
            size,
            size,
            Qt.KeepAspectRatio,
            Qt.SmoothTransformation,
        )
        icon_size = max(1, round(frame.width() * UNDERGROUND_MARKER_ICON_SCALE))
        icon = self._get_icon_pixmap(label_id, icon_size)
        has_icon = icon is not None
        if icon is None:
            icon = self._get_fallback_pixmap(
                label_id, max(6, icon_size // 2))

        marker = QPixmap(frame.size())
        marker.fill(Qt.transparent)
        painter = QPainter(marker)
        painter.setRenderHint(QPainter.SmoothPixmapTransform, True)
        painter.drawPixmap(0, 0, frame)
        icon_x = (frame.width() - icon.width()) // 2
        icon_y = round(
            frame.height() * UNDERGROUND_MARKER_ICON_CENTER_Y
            - icon.height() / 2
        )
        painter.drawPixmap(icon_x, icon_y, icon)
        painter.end()

        if has_icon:
            self.underground_pixmap_cache[key] = marker
        return marker

    # ---------- Paint markers ----------
    def _paint_markers(self, p, left, top, s):
        if not self.marker_index or not self.show_markers:
            self.visible_marker_count = 0
            return

        x0, y0, x1, y1 = self.viewport_bounds()
        candidates = self.marker_index.query(x0, y0, x1, y1)
        if not self.show_underground:
            candidates = [m for m in candidates if not m.underground]
        if self.visible_label_ids is not None:
            candidates = [m for m in candidates
                          if m.label_id in self.visible_label_ids]

        n = len(candidates)
        self.visible_marker_count = n
        if n > 8000:
            return

        icon_size = self._pick_icon_size()
        if n > 3000: icon_size = min(icon_size, round(24 * MARKER_SCALE))
        elif n > 1500: icon_size = min(icon_size, round(32 * MARKER_SCALE))
        elif n > 600:  icon_size = min(icon_size, round(40 * MARKER_SCALE))

        W, H = self.width(), self.height()
        for m in candidates:
            sx = (m.x - left) * s
            sy = (m.y - top) * s
            if m.underground:
                underground_pix = self._get_underground_marker_pixmap(
                    m.label_id, icon_size)
                if underground_pix is not None:
                    pin_width = underground_pix.width()
                    pin_left = sx - pin_width / 2
                    pin_top = sy - underground_pix.height()
                    if (pin_left > W or pin_left + pin_width < 0
                            or pin_top > H or pin_top + underground_pix.height() < 0):
                        continue
                    p.drawPixmap(int(pin_left), int(pin_top), underground_pix)
                    continue
            pin_width = max(1, round(icon_size * self.marker_pin.width()
                                      / self.marker_pin.height()))
            pin_left = sx - pin_width / 2
            pin_top = sy - icon_size * MARKER_PIN_TIP_Y
            if (pin_left > W or pin_left + pin_width < 0
                    or pin_top > H or pin_top + icon_size < 0):
                continue
            pix = self._get_marker_pixmap(m.label_id, icon_size)
            p.drawPixmap(int(pin_left), int(pin_top), pix)

        # Hover
        if self.hovered_marker and self.hovered_marker in candidates:
            hm = self.hovered_marker
            sx = (hm.x - left) * s
            sy = (hm.y - top) * s
            icon_center_y = sy - icon_size * (
                MARKER_PIN_TIP_Y - MARKER_PIN_ICON_CENTER_Y)
            p.setBrush(Qt.NoBrush)
            p.setPen(QPen(Qt.white, 2))
            r = max(16, pin_width // 2 + 4)
            p.drawEllipse(int(sx - r), int(icon_center_y - r), 2 * r, 2 * r)
            self._draw_tooltip(p, hm, int(sx), int(icon_center_y))

    def _draw_tooltip(self, p, m, sx, sy):
        lines = [f"ID: {m.id}", f"Label: {m.label_id}",
                 f"Area: {m.area_id}", f"Pos: ({m.x:.0f}, {m.y:.0f})"]
        if m.underground:
            lines.append("Underground: True")
        if m.point_group:
            lines.append(f"Floor: {m.point_group.get('floor_id')}")
        info = self.icon_file_map.get(m.label_id)
        if info and info.get("name"):
            lines.insert(0, f"Tên: {info['name']}")

        font = QFont(); font.setPointSize(9); p.setFont(font)
        fm = p.fontMetrics()
        w = max(fm.horizontalAdvance(l) for l in lines) + 16
        h = len(lines) * (fm.height() + 2) + 8
        tx = min(max(5, sx + 18), self.width() - w - 5)
        ty = min(max(5, sy - h // 2), self.height() - h - 50)
        p.fillRect(tx, ty, w, h, QColor(0, 0, 0, 225))
        p.setPen(QPen(QColor(120, 160, 220), 1))
        p.drawRect(tx, ty, w - 1, h - 1)
        p.setPen(Qt.white)
        for i, line in enumerate(lines):
            p.drawText(tx + 8, ty + 8 + (i + 1) * (fm.height() + 2) - 2, line)

    # ---------- Paint anchors ----------
    def _get_anchor_font(self, size, bold):
        key = (size, bold)
        if key not in self._font_cache:
            f = QFont()
            f.setPointSize(size)
            if bold:
                f.setWeight(QFont.Bold)
            self._font_cache[key] = f
        return self._font_cache[key]

    def _paint_anchors(self, p, left, top, s):
        if not self.show_anchors:
            return
        W, H = self.width(), self.height()
        for a in self.anchors_parent:
            self._draw_anchor(p, a, left, top, s, W, H, True)
        for a in self.anchors_child:
            self._draw_anchor(p, a, left, top, s, W, H, False)

    def _draw_anchor(self, p, a, left, top, s, W, H, is_parent):
        sx1 = (a.l_x - left) * s
        sy1 = (a.l_y - top) * s
        sx2 = (a.r_x - left) * s
        sy2 = (a.r_y - top) * s

        if sx2 < 0 or sy2 < 0 or sx1 > W or sy1 > H:
            return

        w_px = abs(sx2 - sx1)
        h_px = abs(sy2 - sy1)

        if is_parent:
            if w_px < 50 or h_px < 25:
                return
            size = int(max(11, min(28, min(w_px, h_px) * 0.12)))
            color = QColor(255, 235, 180, 245)
        else:
            if w_px < 70 or h_px < 30:
                return
            size = int(max(9, min(18, min(w_px, h_px) * 0.18)))
            color = QColor(215, 225, 250, 235)

        if size < 8:
            return

        cx = (sx1 + sx2) / 2
        cy = (sy1 + sy2) / 2

        font = self._get_anchor_font(size, is_parent)
        p.setFont(font)
        fm = p.fontMetrics()
        tw = fm.horizontalAdvance(a.name)
        if tw > w_px * 1.4:
            return

        tx = int(cx - tw / 2)
        ty = int(cy + fm.ascent() / 2 - 2)

        p.setPen(QColor(0, 0, 0, 220))
        for dx, dy in [(-2, 0), (2, 0), (0, -2), (0, 2),
                       (-1, -1), (1, -1), (-1, 1), (1, 1)]:
            p.drawText(tx + dx, ty + dy, a.name)

        p.setPen(color)
        p.drawText(tx, ty, a.name)

    # ---------- Paint main ----------
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.SmoothPixmapTransform, True)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.setRenderHint(QPainter.TextAntialiasing, True)
        p.fillRect(self.rect(), QColor(15, 18, 25))

        tz = self.clamped_tile_zoom()
        s = 2 ** self.zoom
        tile_map_size = TILE_SIZE / (2 ** tz)
        draw_size = TILE_SIZE * 2 ** (self.zoom - tz)
        ox, oy = self.origin
        left, top, right, bottom = self.viewport_bounds()

        tx_min = max(0, math.floor((left + ox) / tile_map_size))
        tx_max = max(0, math.floor((right + ox) / tile_map_size))
        ty_min = max(0, math.floor((top + oy) / tile_map_size))
        ty_max = max(0, math.floor((bottom + oy) / tile_map_size))
        max_tx = math.ceil(self.total_size[0] / TILE_SIZE * 2 ** tz)
        max_ty = math.ceil(self.total_size[1] / TILE_SIZE * 2 ** tz)
        tx_max = min(tx_max, max_tx)
        ty_max = min(ty_max, max_ty)

        count = max(0, tx_max - tx_min + 1) * max(0, ty_max - ty_min + 1)
        if count > 600:
            p.setPen(Qt.white)
            p.drawText(20, 30, f"Zoom in ({count} tiles)")
            self._paint_anchors(p, left, top, s)
            self._paint_markers(p, left, top, s)
            self._draw_info_bar(p, tz, 0, 0)
            return

        drawn = missing = 0
        for tx in range(tx_min, tx_max + 1):
            for ty in range(ty_min, ty_max + 1):
                tile_marker_x = tx * tile_map_size - ox
                tile_marker_y = ty * tile_map_size - oy
                sx = int((tile_marker_x - left) * s)
                sy = int((tile_marker_y - top) * s)
                tw = int(draw_size) + 1

                pix = self._load_tile(tx, ty, tz)
                if pix:
                    p.drawPixmap(sx, sy, tw, tw, pix,
                                 0, 0, TILE_SIZE, TILE_SIZE)
                    drawn += 1
                else:
                    fb = self._find_tile_fallback(tx, ty, tz)
                    if fb:
                        fpix, fsx, fsy, fsw, fsh = fb
                        p.drawPixmap(sx, sy, tw, tw, fpix,
                                     fsx, fsy, fsw, fsh)
                        drawn += 1
                    else:
                        p.fillRect(sx, sy, tw, tw, QColor(25, 30, 40))
                        missing += 1
                    self._request_tile(tx, ty, tz)

        self._paint_anchors(p, left, top, s)
        self._paint_markers(p, left, top, s)
        self._draw_info_bar(p, tz, drawn, missing)

    def _draw_info_bar(self, p, tz, drawn, missing):
        W, H = self.width(), self.height()
        p.fillRect(0, H - 46, W, 46, QColor(0, 0, 0, 185))
        p.setPen(Qt.white)
        f = QFont(); f.setPointSize(9); p.setFont(f)
        l1 = (f"zoom {self.zoom:.2f} | tile_z {tz} "
              f"[{self.tile_min_z}..{self.tile_max_z}] "
              f"| drawn {drawn} | missing {missing} | "
              f"cache {len(self.tile_cache)} | pending {len(self.tile_pending)} "
              f"| icons pending {len(self.icon_pending)}")
        l2 = (f"markers: {self.visible_marker_count}/{len(self.markers)} "
              f"[H:{'ON' if self.show_markers else 'OFF'}]  "
              f"anchors [K:{'ON' if self.show_anchors else 'OFF'}]  "
              f"[U:{'under' if self.show_underground else 'surface'}]  "
              f"| R:refresh  Home:fit")
        p.drawText(8, H - 28, l1)
        p.setPen(QColor(160, 200, 255))
        p.drawText(8, H - 10, l2)

    # ---------- Input ----------
    def _update_hovered(self, pos):
        if not self.marker_index or not self.show_markers:
            if self.hovered_marker is not None:
                self.hovered_marker = None
                self.update()
            return
        x0, y0, x1, y1 = self.viewport_bounds()
        cand = self.marker_index.query(x0, y0, x1, y1)
        if not self.show_underground:
            cand = [m for m in cand if not m.underground]
        if len(cand) > 8000:
            return
        s = 2 ** self.zoom
        mx, my = pos.x(), pos.y()
        best = None
        best_d2 = 18 ** 2
        for m in cand:
            sx = (m.x - x0) * s
            sy = (m.y - y0) * s
            d2 = (sx - mx) ** 2 + (sy - my) ** 2
            if d2 < best_d2:
                best_d2 = d2
                best = m
        if best != self.hovered_marker:
            self.hovered_marker = best
            self.update()

    def mousePressEvent(self, ev):
        if ev.button() == Qt.LeftButton:
            self._dragging = True
            self._last_mouse = ev.position()
            self.setCursor(Qt.ClosedHandCursor)

    def mouseMoveEvent(self, ev):
        if self._dragging and self._last_mouse is not None:
            d = ev.position() - self._last_mouse
            self._last_mouse = ev.position()
            s = 2 ** self.zoom
            self.center = (self.center[0] - d.x() / s,
                           self.center[1] - d.y() / s)
            self.update()
        else:
            self._update_hovered(ev.position())

    def mouseReleaseEvent(self, ev):
        if ev.button() == Qt.LeftButton:
            self._dragging = False
            self.setCursor(Qt.ArrowCursor)
            self._update_hovered(ev.position())

    def wheelEvent(self, ev):
        d = ev.angleDelta().y()
        if d == 0:
            return
        step = self.ZOOM_STEP if d > 0 else -self.ZOOM_STEP
        self._zoom_at(ev.position(), step)

    def _zoom_at(self, pos, step):
        new = max(self.min_zoom_ui, min(self.max_zoom_ui, self.zoom + step))
        if new == self.zoom:
            return
        mx, my = pos.x(), pos.y()
        W, H = self.width(), self.height()
        left, top, _, _ = self.viewport_bounds()
        s_old = 2 ** self.zoom
        map_x = left + mx / s_old
        map_y = top + my / s_old
        s_new = 2 ** new
        self.center = (map_x + (W / 2 - mx) / s_new,
                       map_y + (H / 2 - my) / s_new)
        self.zoom = new
        self.update()

    def keyPressEvent(self, ev):
        k = ev.key()
        if k in (Qt.Key_Plus, Qt.Key_Equal):
            self._zoom_at(self.rect().center(), self.ZOOM_STEP * 2)
        elif k == Qt.Key_Minus:
            self._zoom_at(self.rect().center(), -self.ZOOM_STEP * 2)
        elif k == Qt.Key_Home:
            self.fit_to_window()
        elif k == Qt.Key_H:
            self.show_markers = not self.show_markers
            print(f"Markers: {'ON' if self.show_markers else 'OFF'}")
            self.update()
            w = self.window()
            if hasattr(w, "save_settings"):
                w.save_settings()
        elif k == Qt.Key_U:
            self.show_underground = not self.show_underground
            print(f"Underground: {self.show_underground}")
            self.update()
            w = self.window()
            if hasattr(w, "save_settings"):
                w.save_settings()
        elif k == Qt.Key_K:
            self.show_anchors = not self.show_anchors
            print(f"Anchors: {'ON' if self.show_anchors else 'OFF'}")
            self.update()
            w = self.window()
            if hasattr(w, "save_settings"):
                w.save_settings()
        elif k == Qt.Key_R:
            print("🔄 Refreshing...")
            w = self.window()
            if hasattr(w, "refresh_all"):
                w.refresh_all()


# ============================================================
# MAIN WINDOW
# ============================================================
class MapWindow(QWidget):
    def __init__(self, force_refresh=False):
        super().__init__()
        self.setWindowTitle("Teyvat Interactive Map Viewer")
        self.settings = load_user_settings()
        window_state = self.settings.get("window")
        if (isinstance(window_state, list) and len(window_state) == 4
                and all(isinstance(v, (int, float)) for v in window_state)):
            x, y, width, height = window_state
            self.resize(max(400, int(width)), max(300, int(height)))
            self.move(int(x), int(y))
        else:
            self.resize(1440, 900)

        self.force_refresh = force_refresh
        self.meta_data = None
        self.markers_data = None
        self.anchors_data = None
        self.map_widget = None
        self.visible_label_ids = set()
        self.all_marker_label_ids = set()
        self.icon_filter_buttons = {}
        self.icon_filter_status = None

        self._layout = QHBoxLayout(self)
        self._layout.setContentsMargins(0, 0, 0, 0)

        self._start_workers()

    def save_settings(self):
        if self.map_widget is not None:
            self.settings["show_markers"] = self.map_widget.show_markers
            self.settings["show_underground"] = self.map_widget.show_underground
            self.settings["show_anchors"] = self.map_widget.show_anchors
            self.settings["zoom"] = self.map_widget.zoom
            self.settings["center"] = list(self.map_widget.center)
        self.settings["visible_label_ids"] = sorted(self.visible_label_ids)
        pos = self.pos()
        size = self.size()
        self.settings["window"] = [pos.x(), pos.y(), size.width(), size.height()]
        save_user_settings(self.settings)

    def closeEvent(self, event):
        self.save_settings()
        super().closeEvent(event)

    def _start_workers(self):
        self.meta_worker = MetaWorker()
        self.meta_worker.result.connect(self._on_meta)
        self.meta_worker.start()

        self.markers_worker = MarkerWorker()
        self.markers_worker.result.connect(self._on_markers)
        self.markers_worker.start()

        self.anchors_worker = AnchorWorker(force=self.force_refresh)
        self.anchors_worker.result.connect(self._on_anchors)
        self.anchors_worker.start()

    @Slot(object, object, str, int, int)
    def _on_meta(self, total, origin, version, min_z, max_z):
        self.meta_data = (total, origin, version, min_z, max_z)
        self._try_build()

    @Slot(list)
    def _on_markers(self, pts):
        self.markers_data = pts
        self._try_build()

    @Slot(list)
    def _on_anchors(self, anchors):
        self.anchors_data = anchors
        self._try_build()

    def _try_build(self):
        if self.map_widget is not None:
            return
        if (self.meta_data is None or self.markers_data is None
                or self.anchors_data is None):
            return

        total, origin, version, min_z, max_z = self.meta_data
        if total is None:
            total = FALLBACK_TOTAL

        markers = [Marker(m) for m in self.markers_data
                   if m.get("display_state", 1) == 1]

        # Auto-origin nếu cần
        if origin == (0, 0) and markers:
            min_x = min(m.x for m in markers)
            min_y = min(m.y for m in markers)
            max_x = max(m.x for m in markers)
            max_y = max(m.y for m in markers)
            if min_x < 0 or min_y < 0:
                ox = math.ceil(-min_x / 256) * 256
                oy = math.ceil(-min_y / 256) * 256
                total = (max(total[0], math.ceil((max_x + ox) / 256) * 256),
                         max(total[1], math.ceil((max_y + oy) / 256) * 256))
                origin = (ox, oy)
                print(f"⚠️ Auto-origin: {origin} total={total}")

        icon_map = build_label_icon_map()

        print(f"✅ total={total} origin={origin} version={version} "
              f"zoom=[{min_z},{max_z}]")
        print(f"✅ {len(markers)} markers, {len(icon_map)} icons, "
              f"{len(self.anchors_data)} anchors")

        tile_base = TILE_BASE_FMT.format(map_id=MAP_ID, version=version)
        self.map_widget = MapWidget(tile_base, total, origin,
                                    min_z, max_z, markers, self.settings)
        self.map_widget.set_icon_map(icon_map)
        self.map_widget.set_anchors(self.anchors_data)
        self.all_marker_label_ids = {marker.label_id for marker in markers}
        saved_ids = self.settings.get("visible_label_ids")
        if isinstance(saved_ids, list):
            saved_set = {int(v) for v in saved_ids if str(v).lstrip("-").isdigit()}
            self.visible_label_ids = saved_set & self.all_marker_label_ids
        else:
            self.visible_label_ids = set(self.all_marker_label_ids)
        self.map_widget.set_visible_label_ids(self.visible_label_ids)
        self._layout.addWidget(self._build_icon_filter_panel(icon_map, markers))
        self._layout.addWidget(self.map_widget, 1)
        self.map_widget.setFocus()
        saved_zoom = self.settings.get("zoom")
        saved_center = self.settings.get("center")
        if (isinstance(saved_zoom, (int, float))
                and isinstance(saved_center, list)
                and len(saved_center) == 2
                and all(isinstance(v, (int, float)) for v in saved_center)):
            self.map_widget.zoom = max(
                self.map_widget.min_zoom_ui,
                min(self.map_widget.max_zoom_ui, float(saved_zoom)),
            )
            self.map_widget.center = (float(saved_center[0]), float(saved_center[1]))
            self.map_widget.update()
        else:
            QTimer.singleShot(50, self.map_widget.fit_to_window)

    def _build_icon_filter_panel(self, icon_map, markers):
        panel = QWidget(self)
        panel.setObjectName("iconFilterPanel")
        panel.setFixedWidth(336)
        panel.setStyleSheet("""
            QWidget#iconFilterPanel {
                background: #111821;
                color: #e8edf5;
            }
            QLabel#filterTitle {
                color: #f3f6fb;
                font-size: 16px;
                font-weight: 700;
            }
            QLabel#filterSubtitle {
                color: #93a2b5;
                font-size: 10px;
            }
            QLabel#filterStatus {
                background: #1b2835;
                color: #b9d8e8;
                border: 1px solid #2a4050;
                border-radius: 7px;
                padding: 8px;
                font-weight: 600;
            }
            QLineEdit {
                background: #1a232e;
                color: #f3f6fb;
                border: 1px solid #303d4b;
                border-radius: 7px;
                padding: 9px 10px;
                selection-background-color: #287c91;
            }
            QLineEdit:focus { border-color: #54bfd0; }
            QPushButton {
                background: #1c2733;
                color: #dce5ef;
                border: 1px solid #344454;
                border-radius: 7px;
                padding: 8px 6px;
                font-weight: 600;
            }
            QPushButton:hover {
                background: #263545;
                border-color: #5d8ca0;
            }
            QPushButton#showAllButton {
                background: #174b55;
                border-color: #267582;
                color: #e2fbff;
            }
            QPushButton#showAllButton:hover { background: #20616c; }
            QToolButton {
                background: #1a232e;
                color: #dce5ef;
                border: 1px solid #2c3947;
                border-radius: 7px;
                padding: 4px 2px;
            }
            QToolButton:checked {
                background: #203b47;
                border: 1px solid #58bdcc;
                color: #f4fdff;
            }
            QToolButton:hover { border-color: #7898aa; }
            QToolButton:focus { border: 1px solid #8bd9e4; }
            QLabel#filterGroupTitle {
                color: #9eafc1;
                font-size: 10px;
                font-weight: 700;
                padding: 5px 2px 2px;
            }
            QWidget#filterGroup {
                border-bottom: 1px solid #26323e;
            }
            QScrollArea { border: none; background: transparent; }
            QScrollBar:vertical {
                background: #151d27;
                width: 9px;
                margin: 2px;
                border-radius: 4px;
            }
            QScrollBar::handle:vertical {
                background: #3a4b5c;
                min-height: 28px;
                border-radius: 4px;
            }
            QScrollBar::handle:vertical:hover { background: #587186; }
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
                height: 0;
            }
        """)

        layout = QVBoxLayout(panel)
        layout.setContentsMargins(12, 14, 10, 10)
        layout.setSpacing(9)

        title = QLabel("Bộ lọc bản đồ")
        title.setObjectName("filterTitle")
        layout.addWidget(title)

        subtitle = QLabel("Chọn loại điểm muốn hiển thị")
        subtitle.setObjectName("filterSubtitle")
        layout.addWidget(subtitle)

        self.icon_filter_status = QLabel()
        self.icon_filter_status.setObjectName("filterStatus")
        layout.addWidget(self.icon_filter_status)

        controls = QHBoxLayout()
        controls.setSpacing(7)
        select_all = QPushButton("Hiện tất cả")
        select_all.setObjectName("showAllButton")
        clear_all = QPushButton("Ẩn tất cả")
        select_all.clicked.connect(
            lambda: self._set_all_icon_filters(True))
        clear_all.clicked.connect(
            lambda: self._set_all_icon_filters(False))
        controls.addWidget(select_all)
        controls.addWidget(clear_all)
        layout.addLayout(controls)

        search = QLineEdit()
        search.setClearButtonEnabled(True)
        search.setPlaceholderText("Tìm tên hoặc mã loại điểm...")
        search.textChanged.connect(self._filter_icon_buttons)
        search.textChanged.connect(
            lambda text: self._save_filter_search(text))
        saved_search = self.settings.get("filter_search", "")
        layout.addWidget(search)

        scroll = QScrollArea(panel)
        scroll.setWidgetResizable(True)
        grid_widget = QWidget(scroll)
        groups = {}
        for label_id, info in icon_map.items():
            parent_id = info.get("parent_id")
            try:
                parent_id = int(parent_id)
            except (TypeError, ValueError):
                parent_id = str(parent_id) if parent_id is not None else "Không rõ"
            groups.setdefault(parent_id, []).append((label_id, info))

        def parent_sort_key(parent_id):
            try:
                return (0, int(parent_id))
            except (TypeError, ValueError):
                return (1, str(parent_id))

        grid_layout = QVBoxLayout(grid_widget)
        grid_layout.setContentsMargins(2, 2, 2, 2)
        grid_layout.setSpacing(8)
        grid_layout.setAlignment(Qt.AlignTop)

        marker_counts = Counter(marker.label_id for marker in markers)
        self.icon_filter_marker_counts = marker_counts
        self.icon_filter_buttons = {}
        self.icon_filter_groups = []
        for parent_id, group_items in sorted(
                groups.items(), key=lambda group: parent_sort_key(group[0])):
            section = QWidget(grid_widget)
            section.setObjectName("filterGroup")
            section_layout = QVBoxLayout(section)
            section_layout.setContentsMargins(0, 3, 0, 5)
            section_layout.setSpacing(4)
            group_title = QLabel(f"NHÓM  {parent_id}")
            group_title.setObjectName("filterGroupTitle")
            section_layout.addWidget(group_title)

            group_grid = QGridLayout()
            group_grid.setContentsMargins(0, 0, 0, 0)
            group_grid.setHorizontalSpacing(5)
            group_grid.setVerticalSpacing(5)
            group_label_ids = []

            for index, (label_id, info) in enumerate(group_items):
                name = str(info.get("name") or f"ID {label_id}")
                display_name = name if len(name) <= 8 else f"{name[:7]}…"
                count = marker_counts.get(label_id, 0)

                button = QToolButton(section)
                button.setCheckable(True)
                button.setChecked(label_id in self.visible_label_ids)
                button.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
                button.setIconSize(QSize(36, 36))
                button.setFixedSize(70, 82)
                button.setCursor(Qt.PointingHandCursor)
                button.setText(f"{display_name}\n{count}")
                button.setToolTip(
                    f"{name}\nĐiểm trên bản đồ: {count}\n"
                    f"ID: {label_id}\nParent ID: {parent_id}")

                icon_path = info.get("file")
                if icon_path and icon_path.exists():
                    pixmap = QPixmap(str(icon_path))
                    if not pixmap.isNull():
                        button.setIcon(QIcon(pixmap.scaled(
                            QSize(36, 36), Qt.KeepAspectRatio,
                            Qt.SmoothTransformation)))

                button.toggled.connect(
                    lambda checked, lid=label_id:
                    self._on_icon_filter_toggled(lid, checked))
                row, column = divmod(index, 4)
                group_grid.addWidget(button, row, column)
                search_name = unicodedata.normalize("NFC", name).casefold()
                self.icon_filter_buttons[label_id] = (button, search_name)
                group_label_ids.append(label_id)

            section_layout.addLayout(group_grid)
            grid_layout.addWidget(section)
            self.icon_filter_groups.append((section, group_label_ids))

        if isinstance(saved_search, str) and saved_search:
            search.setText(saved_search)

        grid_layout.addStretch(1)

        scroll.setWidget(grid_widget)
        layout.addWidget(scroll, 1)
        self._update_icon_filter_status()
        return panel

    def _on_icon_filter_toggled(self, label_id, checked):
        if checked:
            self.visible_label_ids.add(label_id)
        else:
            self.visible_label_ids.discard(label_id)
        if self.map_widget is not None:
            self.map_widget.set_visible_label_ids(self.visible_label_ids)
        self._update_icon_filter_status()
        self.save_settings()

    def _set_all_icon_filters(self, checked):
        self.visible_label_ids = (
            set(self.all_marker_label_ids) if checked else set())
        for button, _ in self.icon_filter_buttons.values():
            was_blocked = button.blockSignals(True)
            button.setChecked(checked)
            button.blockSignals(was_blocked)
        if self.map_widget is not None:
            self.map_widget.set_visible_label_ids(self.visible_label_ids)
        self._update_icon_filter_status()
        self.save_settings()

    def _save_filter_search(self, text):
        self.settings["filter_search"] = text
        save_user_settings(self.settings)

    def _filter_icon_buttons(self, text):
        query = unicodedata.normalize("NFC", text.strip()).casefold()
        for section, label_ids in self.icon_filter_groups:
            has_match = False
            for label_id in label_ids:
                button, name = self.icon_filter_buttons[label_id]
                matches = query in name
                button.setVisible(matches)
                has_match = has_match or matches
            section.setVisible(has_match)

    def _update_icon_filter_status(self):
        if self.icon_filter_status is None:
            return
        selected = sum(
            1 for button, _ in self.icon_filter_buttons.values()
            if button.isChecked())
        visible_markers = sum(
            self.icon_filter_marker_counts.get(label_id, 0)
            for label_id in self.visible_label_ids)
        self.icon_filter_status.setText(
            f"{selected}/{len(self.icon_filter_buttons)} loại đang bật"
            f"  ·  {visible_markers:,} điểm")

    def refresh_all(self):
        if self.map_widget is None:
            return
        print("🔄 Refresh all (force)...")

        def do_markers():
            pts = fetch_markers()
            if pts:
                self.map_widget.set_markers(
                    [Marker(m) for m in pts if m.get("display_state", 1) == 1]
                )

        def do_anchors():
            anchors = fetch_anchors(force=True)
            if anchors:
                self.map_widget.set_anchors(anchors)

        w1 = _RefreshThread(do_markers)
        w2 = _RefreshThread(do_anchors)
        w1.start()
        w1.wait()
        w2.start()


class _RefreshThread(QThread):
    def __init__(self, fn):
        super().__init__()
        self.fn = fn
    def run(self):
        try:
            self.fn()
        except Exception as e:
            print(f"⚠️ refresh: {e}")


# ============================================================
# MAIN
# ============================================================
def main():
    parser = argparse.ArgumentParser(description="Teyvat Interactive Map Viewer")
    parser.add_argument("--no-cache", action="store_true",
                        help="Bỏ qua cache anchors và tải lại")
    args = parser.parse_args()

    app = QApplication(sys.argv)
    w = MapWindow(force_refresh=args.no_cache)
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()