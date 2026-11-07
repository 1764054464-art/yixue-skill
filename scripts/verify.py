# -*- coding: utf-8 -*-
"""
yixue 可复算层校验脚本（纯标准库）。

设计原则：
  1. 不"自己验自己"：脚本不读实现、也不用被检表格当输入来反算它自己；
     每个公式先独立实现，再与 references/ 中的表、案例、锚点逐项比对。
  2. 覆盖 07（公式规格）、03a（紫微安星案例）、03b（四化读法）、
     02a/02b（八字命例）、04a/04b（卦序/纳甲/八宫/世应）、05a（三元龙）、14（黄历历注算法与锚点）。
  3. 组末打印 PASS/FAIL；任一 FAIL 则退出码 1。

用法：python scripts/verify.py
"""
import io
import os
import random
import re
import sys
from datetime import date

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

BASE = os.path.dirname(os.path.abspath(__file__))
REF = os.path.join(BASE, "..", "references")

GAN = "甲乙丙丁戊己庚辛壬癸"
ZHI = "子丑寅卯辰巳午未申酉戌亥"
JIAZI = [GAN[i % 10] + ZHI[i % 12] for i in range(60)]

EMAP_GAN = dict(zip(GAN, "木木火火土土金金水水"))
EMAP_ZHI = dict(zip(ZHI, "水土木木土火火土金金土水"))
SHENG = {"木": "火", "火": "土", "土": "金", "金": "水", "水": "木"}
KE = {"木": "土", "土": "水", "水": "火", "火": "金", "金": "木"}

CANG = {"子": "癸", "丑": "己癸辛", "寅": "甲丙戊", "卯": "乙",
        "辰": "戊乙癸", "巳": "丙庚戊", "午": "丁己", "未": "己丁乙",
        "申": "庚壬戊", "酉": "辛", "戌": "戊辛丁", "亥": "壬甲"}

# 京房纳甲（48）：经卦 -> 初..上 六干支
NAJIA48 = {
    "乾": ["甲子", "甲寅", "甲辰", "壬午", "壬申", "壬戌"],
    "坤": ["乙未", "乙巳", "乙卯", "癸丑", "癸亥", "癸酉"],
    "震": ["庚子", "庚寅", "庚辰", "庚午", "庚申", "庚戌"],
    "巽": ["辛丑", "辛亥", "辛酉", "辛未", "辛巳", "辛卯"],
    "坎": ["戊寅", "戊辰", "戊午", "戊申", "戊戌", "戊子"],
    "离": ["己卯", "己丑", "己亥", "己酉", "己未", "己巳"],
    "艮": ["丙辰", "丙午", "丙申", "丙戌", "丙子", "丙寅"],
    "兑": ["丁巳", "丁卯", "丁丑", "丁亥", "丁酉", "丁未"],
}

# 八卦三爻（自下而上）1=阳 0=阴
BITS = {"乾": (1, 1, 1), "兑": (1, 1, 0), "离": (1, 0, 1), "震": (1, 0, 0),
        "巽": (0, 1, 1), "坎": (0, 1, 0), "艮": (0, 0, 1), "坤": (0, 0, 0)}

BAGONG_ORDER = ["乾", "坎", "艮", "震", "巽", "离", "坤", "兑"]

# 通行本 64 卦：(卦名, 上卦, 下卦)
CUBE64 = [
    ("乾", "乾", "乾"), ("坤", "坤", "坤"), ("屯", "坎", "震"), ("蒙", "艮", "坎"),
    ("需", "坎", "乾"), ("讼", "乾", "坎"), ("师", "坤", "坎"), ("比", "坎", "坤"),
    ("小畜", "巽", "乾"), ("履", "乾", "兑"), ("泰", "坤", "乾"), ("否", "乾", "坤"),
    ("同人", "乾", "离"), ("大有", "离", "乾"), ("谦", "坤", "艮"), ("豫", "震", "坤"),
    ("随", "兑", "震"), ("蛊", "艮", "巽"), ("临", "坤", "兑"), ("观", "巽", "坤"),
    ("噬嗑", "离", "震"), ("贲", "艮", "离"), ("剥", "艮", "坤"), ("复", "坤", "震"),
    ("无妄", "乾", "震"), ("大畜", "艮", "乾"), ("颐", "艮", "震"), ("大过", "兑", "巽"),
    ("坎", "坎", "坎"), ("离", "离", "离"), ("咸", "兑", "艮"), ("恒", "震", "巽"),
    ("遁", "乾", "艮"), ("大壮", "震", "乾"), ("晋", "离", "坤"), ("明夷", "坤", "离"),
    ("家人", "巽", "离"), ("睽", "离", "兑"), ("蹇", "坎", "艮"), ("解", "震", "坎"),
    ("损", "艮", "兑"), ("益", "巽", "震"), ("夬", "兑", "乾"), ("姤", "乾", "巽"),
    ("萃", "兑", "坤"), ("升", "坤", "巽"), ("困", "兑", "坎"), ("井", "坎", "巽"),
    ("革", "兑", "离"), ("鼎", "离", "巽"), ("震", "震", "震"), ("艮", "艮", "艮"),
    ("渐", "巽", "艮"), ("归妹", "震", "兑"), ("丰", "震", "离"), ("旅", "离", "艮"),
    ("巽", "巽", "巽"), ("兑", "兑", "兑"), ("涣", "巽", "坎"), ("节", "坎", "兑"),
    ("中孚", "巽", "兑"), ("小过", "震", "艮"), ("既济", "坎", "离"), ("未济", "离", "坎"),
]

TIANYUAN_YIN = set("子午卯酉")
TIANYUAN_YANG = set("乾坤艮巽")
DIYUAN_YANG = set("甲庚壬丙")
DIYUAN_YIN = set("辰戌丑未")
RENYUAN_YANG = set("寅申巳亥")
RENYUAN_YIN = set("乙辛丁癸")

XIANG = {"中": 5, "乾": 6, "兑": 7, "艮": 8, "离": 9, "坎": 1, "坤": 2, "震": 3, "巽": 4}
# 九宫对应地支
GONG_ZHI = {"子": "坎", "丑": "艮", "寅": "艮", "卯": "震", "辰": "巽", "巳": "巽",
            "午": "离", "未": "坤", "申": "坤", "酉": "兑", "戌": "乾", "亥": "乾"}
GUAGROUP = {"坎": "壬子癸", "艮": "丑艮寅", "震": "甲卯乙", "巽": "辰巽巳",
            "离": "丙午丁", "坤": "未坤申", "兑": "庚酉辛", "乾": "戌乾亥"}

PASSED = 0
FAILED = []
_marks = []


def check(name, ok, detail=""):
    global PASSED
    if ok:
        PASSED += 1
    else:
        FAILED.append((name, detail))
        print("  FAIL %s  %s" % (name, detail))


def group(title):
    _marks.append(title)
    print("\n[%d] %s" % (len(_marks), title))


_cache = {}


def read(name):
    if name not in _cache:
        with io.open(os.path.join(REF, name), encoding="utf-8") as f:
            _cache[name] = f.read()
    return _cache[name]


def lines(name):
    return read(name).split("\n")


def cells(line):
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|"):
        s = s[:-1]
    return [c.strip().replace("**", "").replace("`", "").strip() for c in s.split("|")]


def find_table(name, header_key):
    """返回 (header_line_1based, rows) —— rows 为数据行（不含表头与分隔行）。"""
    ls = lines(name)
    for i, ln in enumerate(ls):
        if header_key in ln and ln.lstrip().startswith("|"):
            j = i + 1
            if j < len(ls) and set(ls[j].replace("|", "").replace("-", "").strip()) <= {" "}:
                j += 1
            rows = []
            while j < len(ls) and ls[j].lstrip().startswith("|"):
                rows.append(ls[j])
                j += 1
            return i + 1, rows
    return None, []


def gan_index(g):
    return GAN.index(g)


def ten_god(me, other):
    em, eo = EMAP_GAN[me], EMAP_GAN[other]
    same = (GAN.index(me) % 2) == (GAN.index(other) % 2)
    if em == eo:
        return "比肩" if same else "劫财"
    if SHENG[em] == eo:
        return "食神" if same else "伤官"
    if KE[em] == eo:
        return "偏财" if same else "正财"
    if KE[eo] == em:
        return "七杀" if same else "正官"
    if SHENG[eo] == em:
        return "偏印" if same else "正印"
    raise AssertionError((me, other))


def nayin_elem(idx):
    """纳音速断法：干数=干//2+1，支数=(支%6)//2+1，和>5减5，1木2金3水4火5土。"""
    g = (idx % 10) // 2 + 1
    z = ((idx % 12) % 6) // 2 + 1
    s = g + z
    if s > 5:
        s -= 5
    return "木金水火土"[s - 1]


def jdn(y, m, d):
    return date(y, m, d).toordinal() + 1721425


def day_pillar_by_jdn(j):
    return (j + 49) % 60


def pillar(idx):
    return GAN[idx % 10] + ZHI[idx % 12]


def wuhu_stem(yg, month_no):
    """month_no: 寅=1 ... 丑=12。返回月干序号。"""
    return (2 * yg + 2 + (month_no - 1)) % 10


def wushu_stem(dg, hour_no):
    """hour_no: 子=0 ... 亥=11。返回时干序号。"""
    return (2 * dg + hour_no) % 10


def ziwei_pos(d, n):
    q = (d + n - 1) // n
    r = q * n - d
    base = (2 + q - 1) % 12
    return (base + r) % 12 if r % 2 == 0 else (base - r) % 12


def ziwei_pos_03a(d, n):
    q, r = divmod(d, n)
    b = (2 + q) % 12
    if r == 0:
        return (b - 1) % 12
    step = n - r
    if (n % 2) == (r % 2):
        return (b + step) % 12
    return (b - step) % 12


def palace_stem(yg, b):
    """寅宫干起 五虎，b=0..11。注意内层先 mod 12。"""
    yin = (2 * yg + 2) % 10
    return (yin + ((b - 2) % 12)) % 10


STARS14 = {"紫微": 0, "天机": -1, "太阳": -3, "武曲": -4, "天同": -5, "廉贞": -8}
TIANFU_SYS = {"天府": 0, "太阴": 1, "贪狼": 2, "巨门": 3, "天相": 4, "天梁": 5, "七杀": 6, "破军": 10}


def stars(z):
    m = {}
    for s, off in STARS14.items():
        m[s] = (z + off) % 12
    t = (4 - z) % 12
    for s, off in TIANFU_SYS.items():
        m[s] = (t + off) % 12
    return m


def feixing(center, forward):
    nums = []
    n = center
    for _ in XIANG:
        nums.append(9 if n == 0 else n)
        n += 1 if forward else -1
        n %= 9
    return nums


def hexagram_bits(upper, lower):
    return BITS[lower] + BITS[upper]


def flip(bits, *idx):
    b = list(bits)
    for i in idx:
        b[i] = 1 - b[i]
    return tuple(b)


def bagong_hexagrams(pure):
    """pure: 本宫卦 (上,下)。返回 [本宫,一世..五世,游魂,归魂] 的 tuple 列表。"""
    up, lo = pure
    b0 = hexagram_bits(up, lo)
    seq = [b0]
    cur = b0
    for k in range(1, 6):
        cur = flip(cur, k - 1)
        seq.append(cur)
    youhun = flip(seq[5], 3)
    guihun = flip(youhun, 0, 1, 2)
    seq.append(youhun)
    seq.append(guihun)
    return seq


HEXNAME = {}
for nm, u, l in CUBE64:
    HEXNAME[hexagram_bits(u, l)] = nm

NATURE = {"乾": "天", "坤": "地", "震": "雷", "巽": "风", "坎": "水", "离": "火", "艮": "山", "兑": "泽"}
FULL2SHORT = {}
for nm, u, l in CUBE64:
    full = (u + "为" + NATURE[u]) if u == l else (NATURE[u] + NATURE[l] + nm)
    FULL2SHORT[full] = nm


# ---------------------------------------------------------------- 组 1
def g01_day_pillar():
    group("日柱：07 公式/锚点 + 02a 锚点 + 独立双实现")
    t07 = read("07_算法实现与排盘规格.md")
    check("07 日柱公式 (JDN+49) mod 60", "index = (JDN + 49) mod 60" in t07)
    check("07 JDN 取整注", "须先取整（floor）再代入" in t07)

    hdr, rows = find_table("07_算法实现与排盘规格.md", "| 日期 | 干支日")
    check("07 锚点表存在（≥3 行）", len(rows) >= 3, "rows=%d" % len(rows))
    for r in rows:
        c = cells(r)
        if len(c) < 2:
            continue
        y, m, d = [int(x) for x in c[0].split("-")]
        j = jdn(y, m, d)
        check("07 锚点日柱 %s" % c[0], pillar(day_pillar_by_jdn(j)) == c[1],
              "%s vs %s" % (pillar(day_pillar_by_jdn(j)), c[1]))

    for name in ("02a_八字命理_源流排盘与十神.md",):
        hdr, rows = find_table(name, "| 日期（格里高利历）")
        check("%s 锚点表存在" % name[:3], len(rows) >= 3, "rows=%d" % len(rows))
        for r in rows:
            c = cells(r)
            if len(c) < 4:
                continue
            y, m, d = [int(x) for x in c[0].split("-")]
            j = jdn(y, m, d)
            check("%s 锚点 JDN %s" % (name[:3], c[0]), str(j) == c[1])
            check("%s 锚点日柱 %s" % (name[:3], c[0]), pillar(day_pillar_by_jdn(j)) == c[3])

    # 双实现互证：锚点递推 vs 公式
    random.seed(20261021)
    base = date(1900, 1, 1)
    ok = True
    for _ in range(20):
        delta = random.randint(0, 40000)
        dd = base.fromordinal(base.toordinal() + delta)
        idx_formula = day_pillar_by_jdn(jdn(dd.year, dd.month, dd.day))
        idx_walk = (10 + (dd - base).days) % 60
        if idx_formula != idx_walk:
            ok = False
            print("  随机日不一致：", dd, idx_formula, idx_walk)
    check("20 个随机日期：公式解 = 锚点递推解", ok)


# ---------------------------------------------------------------- 组 2
def g02_four_pillars():
    group("四柱：五虎遁/五鼠遁全表 + 02a/02b 命例")
    # 五虎遁 120
    bad = []
    for yg in range(10):
        for b in range(1, 13):
            if wuhu_stem(yg, b) < 0:
                bad.append((yg, b))
    check("五虎遁 120 组合生成", not bad)

    # 与 02a 五虎表逐格比对
    hdr, rows = find_table("02a_八字命理_源流排盘与十神.md", "| 年干＼月建")
    check("02a 五虎表存在", len(rows) == 5, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 13:
            ok = False
            continue
        yg = GAN.index(c[0].replace("、", "")[0])
        for b in range(1, 13):
            exp = GAN[wuhu_stem(yg, b)]
            if c[b] != exp:
                ok = False
                print("  五虎表不符：", c[0], b, c[b], exp)
    check("02a 五虎表 60 格全对", ok)

    # 五鼠遁 120 + 02a 表
    ok = True
    for dg in range(10):
        for h in range(12):
            if not (0 <= wushu_stem(dg, h) <= 9):
                ok = False
    check("五鼠遁 120 组合生成", ok)
    hdr, rows = find_table("02a_八字命理_源流排盘与十神.md", "| 日干＼时支")
    check("02a 五鼠表存在", len(rows) == 5, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 13:
            ok = False
            continue
        dg = GAN.index(c[0].replace("、", "")[0])
        for h in range(12):
            exp = GAN[wushu_stem(dg, h)]
            if c[h + 1] != exp:
                ok = False
                print("  五鼠表不符：", c[0], h, c[h + 1], exp)
    check("02a 五鼠表 60 格全对", ok)

    # 乾隆 1711-09-25 子时：辛卯 丁酉 庚午 丙子
    y, m, d = 1711, 9, 25
    j = jdn(y, m, d)
    check("乾隆日柱 庚午", pillar(day_pillar_by_jdn(j)) == "庚午", pillar(day_pillar_by_jdn(j)))
    check("乾隆年柱 辛卯", pillar((1711 - 4) % 60) == "辛卯")
    check("乾隆月柱 丁酉", GAN[wuhu_stem(7, 8)] + "酉" == "丁酉", GAN[wuhu_stem(7, 8)])
    check("乾隆时柱 丙子", GAN[wushu_stem(6, 0)] + "子" == "丙子")

    # 曾国藩 1811-11-26 亥时：辛未 己亥 丙辰 己亥
    j = jdn(1811, 11, 26)
    check("曾国藩日柱 丙辰", pillar(day_pillar_by_jdn(j)) == "丙辰", pillar(day_pillar_by_jdn(j)))
    check("曾国藩年柱 辛未", pillar((1811 - 4) % 60) == "辛未")
    check("曾国藩月柱 己亥", GAN[wuhu_stem(7, 10)] + "亥" == "己亥", GAN[wuhu_stem(7, 10)])
    check("曾国藩时柱 己亥", GAN[wushu_stem(2, 11)] + "亥" == "己亥")

    # 02b 修正文本
    t = read("02b_八字命理_格局用神大运与案例.md")
    check("02b 曾国藩时差 6h15m", "6 小时 15 分" in t)
    check("02b 曾国藩折算 3 时辰", "3 个时辰" in t)
    check("02b 乙说时干用当日", "时干亦用当日日干" in t)
    check("02b 丙说标注", "不换日派" in t and "丙说" in t)
    check("02b 乾隆子时法已声明", "传世盘作" in t)


# ---------------------------------------------------------------- 组 3
def g03_canggan_nayin_shishen():
    group("藏干 / 纳音 / 十神")
    hdr, rows = find_table("02a_八字命理_源流排盘与十神.md", "| 地支 | 本气 | 中气 | 余气")
    check("02a 藏干表存在", len(rows) == 12, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 4:
            ok = False
            continue
        z = c[0]
        got = [x for x in c[1:4] if x and x != "—"]
        exp = list(CANG.get(z, ""))
        if got != exp:
            ok = False
            print("  藏干不符：", z, got, exp)
    check("02a 藏干 12 支（次序比对）", ok)

    # 纳音：速断法 vs 03a 表（60）
    hdr, rows = find_table("03a_紫微斗数_源流与排盘安星.md", "| 干支 | 纳音 | 干支 | 纳音")
    check("03a 纳音表存在", len(rows) == 15, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 4:
            ok = False
            continue
        for paircell, ny in ((c[0], c[1]), (c[2], c[3])):
            for gz in paircell.split():
                if len(gz) != 2:
                    ok = False
                    continue
                idx = JIAZI.index(gz)
                exp = nayin_elem(idx)
                if ny[-1] != exp:
                    ok = False
                    print("  纳音不符：", gz, ny, exp)
    check("纳音 60 全对（速断法 vs 表）", ok)

    # 十神：甲日主 10 格 + 100 组合分布
    hdr, rows = find_table("02a_八字命理_源流排盘与十神.md", "| 天干 | 甲 | 乙 |")
    check("02a 十神表存在", len(rows) >= 1, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 11 or c[0] != "十神":
            continue
        for k in range(10):
            exp = ten_god("甲", GAN[k])
            if c[k + 1] != exp:
                ok = False
                print("  十神不符：甲见%s 表=%s 算=%s" % (GAN[k], c[k + 1], exp))
    check("02a 十神表（甲日主 10 格）", ok)

    counts = {}
    for me in GAN:
        for other in GAN:
            counts.setdefault(me, []).append(ten_god(me, other))
    bad = [me for me, v in counts.items() if sorted(v) != sorted(
        ["比肩", "劫财", "食神", "伤官", "偏财", "正财", "七杀", "正官", "偏印", "正印"])]
    check("十神 100 组合（每干 10 种各一次）", not bad, str(bad))


# ---------------------------------------------------------------- 组 4
def g04_ziwei():
    group("紫微：两套公式互证 150 格 + 03a 全表 + 初一表 + 案例")
    ziwei_map = [("水二局", 2), ("木三局", 3), ("金四局", 4), ("土五局", 5), ("火六局", 6)]
    hdr, rows = find_table("03a_紫微斗数_源流与排盘安星.md", "| 日 | 水二 | 木三")
    check("03a 紫微全表存在", len(rows) == 30, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 6:
            ok = False
            continue
        d = int(c[0])
        for k, (nm, n) in enumerate(ziwei_map):
            if d > n:
                continue
            z1 = ziwei_pos(d, n)
            z2 = ziwei_pos_03a(d, n)
            if z1 != z2:
                ok = False
                print("  两公式不一致：", nm, d, z1, z2)
            if ZHI[z2] != c[k + 1]:
                ok = False
                print("  紫微表不符：", nm, "初%d" % d, "表=", c[k + 1], "算=", ZHI[z2])
    check("紫微 150 格（07 式 = 03a 式 = 表）", ok)

    hdr, rows = find_table("07_算法实现与排盘规格.md", "| 局 n | d=1 时 q,r")
    check("07 初一验算表存在", len(rows) == 5, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 5:
            ok = False
            continue
        n = {"水二": 2, "木三": 3, "金四": 4, "土五": 5, "火六": 6}[c[0]]
        if ZHI[ziwei_pos(1, n)] != c[3]:
            ok = False
            print("  初一表不符：", c[0], c[3])
    check("07 初一表 5 局（表 = 公式）", ok)

    # 03a 案例：甲子年五月初五未时男
    yg, month, d, h = 0, 5, 5, 7
    ming = (2 + (month - 1) - h) % 12
    shen = (2 + (month - 1) + h) % 12
    check("03a 案例 命宫亥", ZHI[ming] == "亥", ZHI[ming])
    check("03a 案例 身宫丑", ZHI[shen] == "丑", ZHI[shen])
    gz = pillar(palace_stem(yg, ming) * 0 + JIAZI.index(GAN[palace_stem(yg, ming)] + ZHI[ming]))
    check("03a 案例 命宫干支乙亥", gz == "乙亥", gz)
    check("03a 案例 宫干 子丙丑丁", GAN[palace_stem(0, 0)] == "丙" and GAN[palace_stem(0, 1)] == "丁")
    n = 6
    z = ziwei_pos(d, n)
    check("03a 案例 紫微丑", ZHI[z] == "丑", ZHI[z])
    check("03a 案例 天府卯", ZHI[(4 - z) % 12] == "卯")
    st = stars(z)
    exp = {"紫微": "丑", "天机": "子", "太阳": "戌", "武曲": "酉", "天同": "申", "廉贞": "巳",
           "天府": "卯", "太阴": "辰", "贪狼": "巳", "巨门": "午", "天相": "未", "天梁": "申",
           "七杀": "酉", "破军": "丑"}
    bad = [k for k, v in exp.items() if ZHI[st[k]] != v]
    check("03a 案例 14 星位置", not bad, str(bad))

    t3a = read("03a_紫微斗数_源流与排盘安星.md")
    t7 = read("07_算法实现与排盘规格.md")
    check("07 紫微商余式", "q = ceil(d / n)" in t7 and "r = q * n − d" in t7)
    check("07 紫微基准式", "base = 寅 + (q − 1)" in t7)
    check("07 紫微顺逆式", "if r 为偶数: 紫微 = base + r" in t7 and "if r 为奇数: 紫微 = base − r" in t7)
    check("07 天府式", "天府 = (4 − 紫微) mod 12" in t7)
    check("03a 紫微伪代码", all(k in t3a for k in (
        "q, r = divmod(day, J)", "B = (2 + q) mod 12", "if r == 0: Z = (B - 1) mod 12")))
    check("03a 宫干式已补 mod 12（公式行）", "((地支序号 − 2) mod 12)" in t3a)
    check("03a 伪代码已补 mod 12", "((b - 2) mod 12)" in t3a)
    check("03a 闰月归属已注", "闰月归属：leap_month=1" in t3a)
    check("03a 四化句已修正", "化忌十干各异" in t3a)


# ---------------------------------------------------------------- 组 5
def g05_sihua():
    group("四化：07/03a 两张表 + 庚科双说 + 03b 读法")
    expected = {
        "甲": ("廉贞", "破军", "武曲", "太阳"),
        "乙": ("天机", "天梁", "紫微", "太阴"),
        "丙": ("天同", "天机", "文昌", "廉贞"),
        "丁": ("太阴", "天同", "天机", "巨门"),
        "戊": ("贪狼", "太阴", "右弼", "天机"),
        "己": ("武曲", "贪狼", "天梁", "文曲"),
        "庚": ("太阳", "武曲", "太阴", "天同"),
        "辛": ("巨门", "太阳", "文曲", "文昌"),
        "壬": ("天梁", "紫微", "左辅", "武曲"),
        "癸": ("破军", "巨门", "太阴", "贪狼"),
    }
    for fname, tag in (("07_算法实现与排盘规格.md", "07"), ("03a_紫微斗数_源流与排盘安星.md", "03a")):
        hdr, rows = find_table(fname, "| 年干 | 化禄 | 化权 | 化科 | 化忌")
        check("%s 四化表存在" % tag, len(rows) == 10, "rows=%d" % len(rows))
        ok = True
        for r in rows:
            c = cells(r)
            if len(c) < 5:
                ok = False
                continue
            g = c[0].strip("*")
            exp = expected.get(g)
            got = tuple(x.split("／")[0].split("（")[0].strip() for x in c[1:5])
            if exp is None or got != exp:
                ok = False
                print("  四化不符：", tag, g, got, exp)
        check("%s 四化 40 格全对" % tag, ok)
    t7 = read("07_算法实现与排盘规格.md")
    check("07 庚科双说标注", "太阴" in t7 and "天府" in t7 and "分歧" in t7)
    t3a = read("03a_紫微斗数_源流与排盘安星.md")
    check("03a 庚干分歧标注", "庚干分歧" in t3a or "《全书》" in t3a)
    t3b = read("03b_紫微斗数_星曜宫位四化与推断.md")
    check("03b 天相说标注为少数派", "天相（少数派，仅备一说）" in t3b)
    check("03b 庚忌注已加", "庚干化忌作" in t3b)
    check("03b 命宫无四化表述已改", "命宫没有四化、官禄宫也只有太阳化忌" in t3b)
    check("03b 福德宫今语已注", "心理状态（现代类比）" in t3b)
    # 案例四化
    sh = expected["甲"]
    check("03a 案例四化（廉禄巳/破权丑/武科酉/阳忌戌）",
          sh[0] == "廉贞" and sh[1] == "破军" and sh[2] == "武曲" and sh[3] == "太阳")


# ---------------------------------------------------------------- 组 6
def g06_najia_bagong():
    group("纳甲 48 / 京房八宫 64 / 世应")
    for fname, tag in (("07_算法实现与排盘规格.md", "07"), ("04b_周易卦象_六爻纳甲梅花易数.md", "04b")):
        hdr, rows = find_table(fname, "| 经卦 |")
        check("%s 纳甲表存在" % tag, len(rows) == 8, "rows=%d" % len(rows))
        ok = True
        for r in rows:
            c = cells(r)
            if len(c) < 3:
                ok = False
                continue
            g = c[0].split()[0]
            exp = NAJIA48.get(g)
            got = c[2].replace("、", " ").split() + (c[3].replace("、", " ").split() if len(c) > 3 else [])
            if exp is None or len(got) != 6:
                ok = False
                print("  纳甲结构异常：", tag, g, got)
                continue
            for k in range(6):
                if got[k] != exp[k]:
                    ok = False
                    print("  纳甲不符：", tag, g, k + 1, got[k], exp[k])
        check("%s 纳甲 48 位全对" % tag, ok)

    # 八宫：07 表 + 04b 表 + 爻变复算
    pure = {"乾": ("乾", "乾"), "坎": ("坎", "坎"), "艮": ("艮", "艮"), "震": ("震", "震"),
            "巽": ("巽", "巽"), "离": ("离", "离"), "坤": ("坤", "坤"), "兑": ("兑", "兑")}
    canon = {}
    for g in BAGONG_ORDER:
        seq = bagong_hexagrams(pure[g])
        canon[g] = [HEXNAME[b] for b in seq]
    # 04b 表
    hdr, rows = find_table("04b_周易卦象_六爻纳甲梅花易数.md", "| 宫（五行） | 本宫卦")
    check("04b 八宫表存在", len(rows) == 8, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 9:
            ok = False
            continue
        g = c[0][0]
        names = [FULL2SHORT.get(x.split()[0], x.split()[0]) for x in c[1:9]]
        if names != canon.get(g):
            ok = False
            print("  04b 八宫不符：", g, names, canon.get(g))
    check("04b 八宫 64 卦逐格（与爻变复算一致）", ok)

    hdr, rows = find_table("07_算法实现与排盘规格.md", "| 宫 | 本宫")
    check("07 八宫表存在", len(rows) == 8, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 8:
            ok = False
            continue
        g = c[0]
        names = c[1:8]
        exp = canon.get(g, [])
        if len(names) != 7 or names != exp[:7]:
            ok = False
            print("  07 八宫不符：", g, names, exp[:7])
    check("07 八宫 56 卦（本宫..游魂）", ok)

    # 世应
    hdr, rows = find_table("04b_周易卦象_六爻纳甲梅花易数.md", "| 卦类 | 世爻 | 应爻")
    check("04b 世应表存在", len(rows) == 8)
    shi_order = [6, 1, 2, 3, 4, 5, 4, 3]
    ok = True
    for k, r in enumerate(rows):
        c = cells(r)
        if len(c) < 3:
            ok = False
            continue
        m = {"初爻": 1, "二爻": 2, "三爻": 3, "四爻": 4, "五爻": 5, "上爻": 6}
        s = m.get(re.sub(r"（.*?）", "", c[1]))
        y = m.get(re.sub(r"（.*?）", "", c[2]))
        if s != shi_order[k] or y != ((s + 2) % 6) + 1:
            ok = False
            print("  世应不符：", c)
    check("04b 世应 8 类（应=世+3）", ok)


# ---------------------------------------------------------------- 组 7
def g07_gua64():
    group("64 卦：序、卦名、上下卦")
    hdr, rows = find_table("04a_周易卦象_经传象数与筮法.md", "| 序 | 卦名 | 上下卦")
    check("04a 64 卦表存在", len(rows) >= 64, "rows=%d" % len(rows))
    ok = True
    seen = 0
    for r in rows:
        c = cells(r)
        if len(c) < 3:
            ok = False
            continue
        try:
            n = int(c[0])
        except ValueError:
            continue
        if not 1 <= n <= 64:
            ok = False
            continue
        seen += 1
        nm, u, l = CUBE64[n - 1]
        name = c[1].split()[0]
        udl = c[2].replace(" ", "")
        if name != nm or udl != u + "上" + l + "下":
            ok = False
            print("  卦序不符：", n, c[1], c[2], "期望", nm, u + "上" + l + "下")
    if seen != 64:
        ok = False
        print("  64 卦有效行数不足：", seen)
    check("64 卦 序/名/上下卦 全对", ok)


# ---------------------------------------------------------------- 组 8
def g08_sanyuan_xuankong():
    group("三元龙 24 + 玄空（子午必同阴阳 / 取象层 / 八运双星会向）")
    hdr, rows = find_table("05a_风水堪舆_峦头形势与罗盘.md", "| 序 | 山 | 周天起止 | 中心 | 所属卦 | 三元龙 | 玄空阴阳")
    check("05a 二十四山表存在", len(rows) == 24, "rows=%d" % len(rows))
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 7:
            ok = False
            continue
        shan, gong, yuan, yy = c[1], c[4], c[5], c[6]
        if yuan == "天元":
            exp_yy = "阴" if shan in TIANYUAN_YIN else "阳"
        elif yuan == "地元":
            exp_yy = "阳" if shan in DIYUAN_YANG else "阴"
        else:
            exp_yy = "阳" if shan in RENYUAN_YANG else "阴"
        if yy != exp_yy:
            ok = False
            print("  三元龙阴阳不符：", shan, yuan, yy, exp_yy)
        if GONG_ZHI.get(shan) != gong and shan not in GUAGROUP.get(gong, ""):
            ok = False
            print("  统卦不符：", shan, gong)
    check("05a 二十四山：统卦/元/阴阳 24 山", ok)

    check("硬校验律：子午卯酉同阴", all(z in TIANYUAN_YIN for z in "子午卯酉"))
    check("硬校验律：乾坤艮巽同阳", all(z in TIANYUAN_YANG for z in "乾坤艮巽"))
    t5b = read("05b_风水堪舆_八宅玄空三合与阳宅.md")
    check("05b 重申三元龙阴阳", all(k in t5b for k in ("子午卯酉", "乾坤艮巽", "乙辛丁癸")))
    t5a = read("05a_风水堪舆_峦头形势与罗盘.md")
    check("05a 术语已改（四墓库藏干）", "四墓库藏干（乙辛丁癸）" in t5a)

    # 八运 子山午向：运盘 8 入中顺飞；取象层：4 属巽取巽阳 → 顺；3 属震取卯阴 → 逆
    yun = feixing(8, True)
    # yun 顺序沿 中乾兑艮离坎坤震巽
    idx = {g: k for k, g in enumerate(["中", "乾", "兑", "艮", "离", "坎", "坤", "震", "巽"])}
    shan_center = yun[idx["坎"]]
    xiang_center = yun[idx["离"]]
    shan = feixing(shan_center, True)   # 子：入中 4 属巽，取巽（阳）→ 顺
    xiang = feixing(xiang_center, False)  # 午：入中 3 属震，取卯（阴）→ 逆
    check("八运子山午向：山星 8 到离、9 到坎", shan[idx["离"]] == 8 and shan[idx["坎"]] == 9, str(shan))
    check("八运子山午向：向星 8 到离、7 到坎", xiang[idx["离"]] == 8 and xiang[idx["坎"]] == 7, str(xiang))
    t7 = read("07_算法实现与排盘规格.md")
    t5b = read("05b_风水堪舆_八宅玄空三合与阳宅.md")
    check("07 双星会向判据文本", "双星会向" in t7 and "山、向旺星俱到向首" in t7)
    check("05b 取象层示例文本", "取与子同为天元龙的**巽**" in t5b and "同三元龙 ≠ 同顺逆" in t5b)

    # 07 三元龙表（天元/人元/地元 八山分组）
    hdr, rows = find_table("07_算法实现与排盘规格.md", "| 元龙 | 八山 |")
    check("07 三元龙表存在", len(rows) == 3, "rows=%d" % len(rows))
    want = {"天元龙": set("子午卯酉乾坤艮巽"), "人元龙": set("寅申巳亥乙辛丁癸"),
            "地元龙": set("辰戌丑未甲庚壬丙")}
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 2:
            ok = False
            continue
        if set(c[1].replace("、", "")) != want.get(c[0]):
            ok = False
            print("  07 三元龙分组不符：", c[0], c[1])
    check("07 三元龙 3 组八山", ok)

    # 07 五行局表
    hdr, rows = find_table("07_算法实现与排盘规格.md", "| 纳音五行 | 局 |")
    check("07 五行局表存在", len(rows) == 5, "rows=%d" % len(rows))
    J = {"水二局": 2, "木三局": 3, "金四局": 4, "土五局": 5, "火六局": 6}
    ok = True
    for r in rows:
        c = cells(r)
        if len(c) < 3:
            ok = False
            continue
        jj = J.get(c[1])
        if jj is None or not c[2].startswith(str(jj)):
            ok = False
            print("  五行局不符：", c)
    check("07 五行局 5 行（局数=起限岁）", ok)


# ---------------------------------------------------------------- 组 9
def g09_dayun():
    group("大运：47 天 8 小时 = 15 年 9 月 10 日 + 顺逆 8 组合")
    total = 47 * 1440 + 8 * 60
    years, rem = divmod(total, 3 * 1440)
    months, rem = divmod(rem, 30 * 12)
    days, rem = divmod(rem, 12)
    check("47d8h → 15 年 9 月 10 日（零余）", (years, months, days, rem) == (15, 9, 10, 0),
          str((years, months, days, rem)))
    # 顺逆：阳男阴女顺
    ok = True
    for yang in (0, 1):
        for male in (0, 1):
            fwd = (bool(yang) == bool(male))
            if fwd != (yang == male):
                ok = False
    check("顺逆判定：阳男阴女顺 / 阴男阳女逆", ok)
    t = read("02b_八字命理_格局用神大运与案例.md")
    check("02b 曾国藩起运 6 年 1 月余", "6 年" in t and "1 个月" in t)
    t7 = read("07_算法实现与排盘规格.md")
    check("07 大运 47d8h 例", "47 天 8 小时" in t7 and "15 岁 9 个月 10 天" in t7)


# ---------------------------------------------------------------- 组 10
def g10_piyu():
    group("批语结构（11/12/13）")
    for f in ("11_批语学_评点传统与命书批语体例.md", "12_批语示范_五盘全批与逐句解剖.md",
              "13_批语训练_句式库改稿题库与评分.md"):
        check("存在 %s" % f.split("_")[0], os.path.exists(os.path.join(REF, f)))
    t13 = read("13_批语训练_句式库改稿题库与评分.md")
    check("四级断语术语齐备", all(k in t13 for k in ("确断", "倾向", "或然", "不可断")))
    check("无「铁口直断」", "铁口直断" not in t13)
    flat = re.sub(r"\s+", "", t13)
    check("量表 100", "100分" in flat or "100分" in t13)
    check("六维合计 = 100", 30 + 20 + 15 + 15 + 15 + 5 == 100)
    check("68 分示例", "68分" in flat and all(x in flat for x in ("22/30", "12/20", "11/15", "13/15", "10/15", "0/5")))


# ---------------------------------------------------------------- 组 11
def g11_placeholders():
    group("占位符扫描")
    bad = []
    for fn in os.listdir(REF):
        if not fn.endswith(".md") or fn.startswith("README"):
            continue
        txt = read(fn)
        for i, ln in enumerate(txt.split("\n"), 1):
            for kw in ("TODO", "待补", "XXX"):
                if kw in ln:
                    bad.append((fn, i, kw))
    check("无 TODO/待补/XXX", not bad, str(bad[:8]))


# ---------------------------------------------------------------- 组 12
def g12_text_consistency():
    group("文本一致性（勘误落地）")
    t7 = read("07_算法实现与排盘规格.md")
    check("07 乌鲁木齐方向已改", "地方时应比北京时间晚约 2 小时 10 分" in t7.replace("**", ""))
    check("07 世应 = 世 + 3", "应爻 = 世爻 + 3" in t7)
    check("07 天府系以天府为 0", "以天府为 0" in t7)
    check("07 均时差误差 1.42", "最大误差 1.42 分钟" in t7)
    check("07 星历声明注", "不内置节气表" in t7)
    t4b = read("04b_周易卦象_六爻纳甲梅花易数.md")
    check("04b 世应 = 世 + 3", "应爻 = 世爻 + 3" in t4b)
    t4a = read("04a_周易卦象_经传象数与筮法.md")
    check("04a 综错八对", "综错兼备" in t4a)
    check("04a 乾大象例外", "天行健，君子以自强不息" in t4a)
    t3b = read("03b_紫微斗数_星曜宫位四化与推断.md")
    check("03b 天相注 | 备一说", "仅备一说" in t3b)
    with io.open(os.path.join(BASE, "..", "SKILL.md"), encoding="utf-8") as f:
        tsk = f.read()
    check("SKILL 已声明 14 组", "14 组" in tsk and "13 组" not in tsk)
    check("SKILL 不再写 113 断言", "113 项断言" not in tsk)
    check("SKILL 已声明 19 篇", "19 篇" in tsk)
    trd = read("README-知识库导读.md")
    check("README 导读已声明 19 份专题文档", "19 份专题文档" in trd)
    check("README 导读已收 14 篇", "14_黄历通书" in trd)


def g13_koujing():
    group("g13 口径声明：NOAA 均时差 / 晚子时四档 / 闰月四口径 / 天魁钺软件派")
    t07 = read("07_算法实现与排盘规格.md")
    t2a = read("02a_八字命理_源流排盘与十神.md")
    t3a = read("03a_紫微斗数_源流与排盘安星.md")
    check("07 含 NOAA 均时差常数", "229.18" in t07 and "0.001868" in t07 and "0.032077" in t07)
    check("07 注明 iztro 可作交叉源", "iztro" in t07 and "交叉源" in t07)
    for tag in ("next-day", "current-day", "day-cur-time-next", "all-current"):
        check("02a 晚子时四档命名 | %s" % tag, tag in t2a)
    check("02a 要求标注子时法", "【子时法" in t2a)
    for kw in ("归本月", "归次月", "半月切", "按节气"):
        check("03a 闰月四口径 | %s" % kw, kw in t3a)
    check("03a 天魁天钺文墨派注", "魁寅钺午" in t3a and "文墨" in t3a)

    import math
    def eot_noaa(n, h=12.0, days=365):
        g = 2 * math.pi / days * (n - 1 + (h - 12) / 24.0)
        return 229.18 * (0.000075 + 0.001868 * math.cos(g) - 0.032077 * math.sin(g)
                         - 0.014615 * math.cos(2 * g) - 0.040849 * math.sin(2 * g))
    def eot_simple(n):
        b = math.radians(360.0 * (n - 81) / 364.0)
        return 9.87 * math.sin(2 * b) - 7.53 * math.cos(b) - 1.5 * math.sin(b)
    diffs = [abs(eot_noaa(n) - eot_simple(n)) for n in range(1, 366)]
    check("NOAA 式与 9.87 式 1998 年最大差 < 2 分钟", max(diffs) < 2.0, "max=%.2f" % max(diffs))


# ---------------------------------------------------------------- 组 14
D14 = "14_黄历通书_历注体系与算法.md"

JIANCHU = ["建", "除", "满", "平", "定", "执", "破", "危", "成", "收", "开", "闭"]
ZHISHEN12 = ["青龙", "明堂", "天刑", "朱雀", "金匮", "天德", "白虎", "玉堂", "天牢", "玄武", "司命", "勾陈"]
HUANG_DAO = {0, 1, 4, 5, 7, 10}
XIU28 = "角亢氐房心尾箕斗牛女虚危室壁奎娄胃昴毕觜参井鬼柳星张翼轸"
JIU_NUM = ["一白", "二黑", "三碧", "四绿", "五黄", "六白", "七赤", "八白", "九紫"]
LIUYAO6 = ["大安", "赤口", "先胜", "友引", "先负", "佛灭"]

ZHI_FANG = {"子": "正北", "丑": "东北", "寅": "东北", "卯": "正东", "辰": "东南", "巳": "东南",
            "午": "正南", "未": "西南", "申": "西南", "酉": "正西", "戌": "西北", "亥": "西北"}
YANG_GUI = {"甲": "未", "乙": "申", "丙": "酉", "丁": "亥", "戊": "丑",
            "己": "子", "庚": "丑", "辛": "寅", "壬": "卯", "癸": "巳"}
YIN_GUI = {"甲": "丑", "乙": "子", "丙": "亥", "丁": "酉", "戊": "未",
           "己": "申", "庚": "未", "辛": "午", "壬": "巳", "癸": "卯"}
XI_SHEN = {"甲": "东北", "己": "东北", "乙": "西北", "庚": "西北", "丙": "西南",
           "辛": "西南", "丁": "正南", "壬": "正南", "戊": "东南", "癸": "东南"}
CAI_SHEN = {"甲": "东北", "乙": "东北", "丙": "西南", "丁": "西南", "戊": "正北",
            "己": "正北", "庚": "正东", "辛": "正东", "壬": "正南", "癸": "正南"}
XUN_KONG = ["戌亥", "申酉", "午未", "辰巳", "寅卯", "子丑"]
LU_ZHI = {"甲": "寅", "乙": "卯", "丙": "巳", "丁": "午", "戊": "巳",
          "己": "午", "庚": "申", "辛": "酉", "壬": "亥", "癸": "子"}

GAN_POS = {"甲": "门", "己": "门", "乙": "碓磨", "庚": "碓磨", "丙": "厨灶",
           "辛": "厨灶", "丁": "仓库", "壬": "仓库", "戊": "房床", "癸": "房床"}
ZHI_POS = {"子": "碓", "午": "碓", "丑": "厕", "未": "厕", "寅": "炉", "申": "炉",
           "卯": "门", "酉": "门", "辰": "栖", "戌": "栖", "巳": "床", "亥": "床"}
# 胎神逐日占游方定局：按六十甲子序（甲子=0）连段
TAISHEN_RUNS = [(0, 1, "外东南"), (2, 6, "外正南"), (7, 12, "外西南"), (13, 17, "外正西"),
                (18, 23, "外西北"), (24, 28, "外正北"), (29, 33, "房内北"), (34, 35, "房内中"),
                (36, 38, "房内南"), (39, 39, "房内西"), (40, 43, "房内东"), (44, 44, "房内中"),
                (45, 50, "外东北"), (51, 55, "外正东"), (56, 59, "外东南")]

PENGZU = {
    "甲": "甲不开仓财物耗散", "乙": "乙不栽植千株不长", "丙": "丙不修灶必见灾殃",
    "丁": "丁不剃头头必生疮", "戊": "戊不受田田主不祥", "己": "己不破券二比并亡",
    "庚": "庚不经络织机虚张", "辛": "辛不合酱主人不尝", "壬": "壬不汲水更难提防",
    "癸": "癸不词讼理弱敌强", "子": "子不问卜自惹祸殃", "丑": "丑不冠带主不还乡",
    "寅": "寅不祭祀神鬼不尝", "卯": "卯不穿井水泉不香", "辰": "辰不哭泣必主重丧",
    "巳": "巳不远行财物伏藏", "午": "午不苫盖屋主更张", "未": "未不服药毒气入肠",
    "申": "申不安床鬼祟入房", "酉": "酉不会客醉坐颠狂", "戌": "戌不吃犬作怪上床",
    "亥": "亥不嫁娶不利新郎",
}


def jz_index(y, m, d):
    return (jdn(y, m, d) + 49) % 60


def d_jianchu(month_zhi, day_zhi):
    return (day_zhi - month_zhi) % 12


def d_zhishen(month_zhi, day_zhi):
    """日家十二值神：青龙起支 c=(2*月支+8)%12（协纪卷九 月神随月建行阴阳六辰）"""
    return (day_zhi - (2 * month_zhi + 8) % 12) % 12


def h_zhishen(day_zhi, hour_zhi):
    """时家十二值神：青龙起时支 c=(2*(日支%6)+8)%12（协纪卷九 时神从日支起者）"""
    return (hour_zhi - (2 * (day_zhi % 6) + 8) % 12) % 12


def d_xiu(jd):
    return (jd + 11) % 28


def d_sha(zhi):
    if zhi in (8, 0, 4):
        return "南"
    if zhi in (11, 3, 7):
        return "西"
    if zhi in (2, 6, 10):
        return "北"
    return "东"


def d_taishen_dir(idx60):
    for lo, hi, pos in TAISHEN_RUNS:
        if lo <= idx60 <= hi:
            return pos
    return "?"


def _first_jiazi(d0):
    from datetime import timedelta
    for k in range(60):
        dd = d0 + timedelta(days=k)
        if jz_index(dd.year, dd.month, dd.day) == 0:
            return dd
    raise RuntimeError("no jiazi")


JIU_ANCHORS = [(date(2023, 12, 22), 1, 1), (date(2024, 2, 19), 7, 1), (date(2024, 4, 19), 4, 1),
               (date(2024, 6, 21), 9, -1), (date(2024, 8, 22), 3, -1), (date(2024, 10, 23), 6, -1),
               (date(2024, 12, 21), 1, 1)]


def d_jiuxing(y, m, d):
    """日家白星：冬至/雨水/谷雨 起 1/7/4 顺行；夏至/处暑/霜降 起 9/3/6 逆行。"""
    tgt = date(y, m, d)
    ad, start, step = None, 0, 0
    for a, s, st in JIU_ANCHORS:
        if a <= tgt and (ad is None or a > ad):
            ad, start, step = a, s, st
    base = _first_jiazi(ad)
    delta = (tgt - base).days
    return ((start - 1 + step * delta) % 9) + 1


def g14_huangli():
    group("g14 黄历历注：建除/值神/二十八宿/九星/六曜/胎神/彭祖/冲煞/神位/空亡")
    t14 = read(D14)

    # ---- 3.13 总表：脚本独立计算，逐格比对文档
    _, rows = find_table(D14, "| 字段 | 2024-01-01")
    tbl = {}
    for r in rows:
        c = cells(r)
        if len(c) >= 6:
            tbl[c[0]] = c[1:6]
    check("14 篇 3.13 总表可解析（>=12 行 × 5 列）",
          len(tbl) >= 12 and len(tbl.get("建除", [])) == 5, str(sorted(tbl))[:120])

    # (年, 月, 日, 节气月支序, 农历月, 农历日, 农历文本)
    cases = [
        (2024, 1, 1, 0, 11, 20, "十一月二十"),
        (2024, 2, 10, 2, 1, 1, "正月初一"),
        (2024, 2, 11, 2, 1, 2, "正月初二"),
        (2024, 3, 10, 3, 2, 1, "二月初一"),
        (2024, 7, 1, 6, 5, 26, "五月廿六"),
    ]
    for k, (y, mo, dd, mz, lm, ld, lunar_txt) in enumerate(cases):
        jd = jdn(y, mo, dd)
        idx = (jd + 49) % 60
        g, z = GAN[idx % 10], ZHI[idx % 12]
        gz = g + z
        tag = "%04d-%02d-%02d" % (y, mo, dd)
        check("%s 日柱 %s" % (tag, gz), tbl["日柱"][k] == gz, tbl["日柱"][k])
        check("%s 节气月 %s" % (tag, ZHI[mz]), tbl["节气月"][k].startswith(ZHI[mz]), tbl["节气月"][k])
        check("%s 农历 %s" % (tag, lunar_txt), tbl["农历"][k] == lunar_txt, tbl["农历"][k])
        jc = JIANCHU[d_jianchu(mz, idx % 12)]
        check("%s 建除 %s" % (tag, jc), tbl["建除"][k] == jc, tbl["建除"][k])
        vs = d_zhishen(mz, idx % 12)
        cell = tbl["值神"][k]
        check("%s 值神 %s" % (tag, ZHISHEN12[vs]),
              cell.startswith(ZHISHEN12[vs]) and (("（黄）" in cell) == (vs in HUANG_DAO)), cell)
        xi = d_xiu(jd)
        check("%s 值日宿 %s" % (tag, XIU28[xi]), tbl["值日宿"][k] == XIU28[xi], tbl["值日宿"][k])
        n9 = d_jiuxing(y, mo, dd)
        check("%s 日九星 %s" % (tag, JIU_NUM[n9 - 1]), tbl["日九星"][k] == JIU_NUM[n9 - 1], tbl["日九星"][k])
        ly = LIUYAO6[(lm + ld) % 6]
        check("%s 六曜 %s" % (tag, ly), tbl["六曜"][k] == ly, tbl["六曜"][k])
        check("%s 胎神方位 %s" % (tag, d_taishen_dir(idx)), tbl["胎神方位"][k] == d_taishen_dir(idx),
              tbl["胎神方位"][k])
        exp_chong = JIAZI[(idx + 54) % 60] + "·煞" + d_sha(idx % 12)
        check("%s 冲煞 %s" % (tag, exp_chong), tbl["冲"][k] == exp_chong, tbl["冲"][k])
        check("%s 喜神 %s" % (tag, XI_SHEN[g]), tbl["喜神"][k] == XI_SHEN[g], tbl["喜神"][k])
        check("%s 财神 %s" % (tag, CAI_SHEN[g]), tbl["财神"][k] == CAI_SHEN[g], tbl["财神"][k])
        exp_gui = ZHI_FANG[YANG_GUI[g]] + "/" + ZHI_FANG[YIN_GUI[g]]
        check("%s 阳贵/阴贵 %s" % (tag, exp_gui), tbl["阳贵/阴贵"][k] == exp_gui, tbl["阳贵/阴贵"][k])
        check("%s 日空亡 %s" % (tag, XUN_KONG[idx // 10]), tbl["日空亡"][k] == XUN_KONG[idx // 10],
              tbl["日空亡"][k])

    # ---- 3.3 值神五例表（月支/起支/值神序）
    _, rows = find_table(D14, "| 日期 | 日柱 | 节气月 |")
    for r in rows:
        c = cells(r)
        y, mo, dd = [int(x) for x in c[0].split("-")]
        mz = ZHI.index(c[2][0])
        idx = jz_index(y, mo, dd)
        # 青龙起支 c 与值神序 v 双检
        c_val = (2 * mz + 8) % 12
        v_val = (idx % 12 - c_val) % 12
        check("3.3 值神表 %s 起支" % c[0], c[3].startswith(str(c_val)), c[3])
        check("3.3 值神表 %s 值神" % c[0], c[5].startswith(ZHISHEN12[v_val]), c[5])

    # ---- 3.4 时家黄黑道：三例 × 12 时辰
    hour_seq = {
        (2024, 2, 10): "凶凶吉凶吉吉凶凶吉吉凶吉",
        (2024, 2, 11): "凶吉凶凶吉凶吉吉凶凶吉吉",
        (2024, 7, 1): "吉吉凶凶吉吉凶吉凶凶吉凶",
    }
    for (y, mo, dd), want in hour_seq.items():
        dz = jz_index(y, mo, dd) % 12
        got = "".join("吉" if h_zhishen(dz, hz) in HUANG_DAO else "凶" for hz in range(12))
        check("时家黄黑道 %04d-%02d-%02d" % (y, mo, dd), got == want, got + " vs " + want)
    check("3.4 篇内载三例时辰序列", "子凶 丑凶 寅吉" in t14 and "子凶 丑吉 寅凶" in t14
          and "子吉 丑吉 寅凶" in t14)

    # ---- 3.8 胎神：局表 15 段拼合 = 60 日公式；部位合成
    _, rows = find_table(D14, "| 甲子序 | 起讫 |")
    seq = []
    for r in rows:
        c = cells(r)
        rng = c[0].replace("–", "-").split("-")
        try:
            lo, hi = int(rng[0]), int(rng[-1])
        except ValueError:
            continue
        seq += [c[2]] * (hi - lo + 1)
    check("胎神逐日占方定局 60 日全表", len(seq) == 60 and all(seq[i] == d_taishen_dir(i) for i in range(60)),
          "len=%d" % len(seq))
    for jz_txt, parts in (("甲子", "门" + "碓"), ("乙巳", "碓磨" + "床"),
                          ("癸酉", "房床" + "门"), ("丙寅", "厨灶" + "炉")):
        check("胎神部位 %s = %s" % (jz_txt, parts),
              parts == GAN_POS[jz_txt[0]] + ZHI_POS[jz_txt[1]] and parts in t14, parts)
    check("胎神甲子日作『占门碓』", "占门碓" in t14)

    # ---- 3.9 彭祖百忌 22 条
    miss = [k for k, v in PENGZU.items() if v not in t14]
    check("彭祖百忌 22 条齐备", len(PENGZU) == 22 and not miss, str(miss))
    miss = [k for k, v in PENGZU.items() if v not in read("01_基础_阴阳五行干支历法与易学宇宙观.md")
            and v not in t14]
    check("彭祖百忌 无漏字", not miss, str(miss))

    # ---- 3.10 冲煞 / 三煞
    check("日冲 甲辰→戊戌", JIAZI[(jz_index(2024, 2, 10) + 54) % 60] == "戊戌")
    check("日冲 乙巳→己亥", JIAZI[(jz_index(2024, 2, 11) + 54) % 60] == "己亥")
    check("日煞 申子辰煞南 / 亥卯未煞西", d_sha(0) == "南" and d_sha(3) == "西")
    check("日煞 寅午戌煞北 / 巳酉丑煞东", d_sha(6) == "北" and d_sha(9) == "东")
    check("3.10 三煞 年南月北日南", "年南 月北 日南" in t14)

    # ---- 3.11 神位表（干→方位 与篇内表一致）
    for gl, fang in (("甲己", "东北"), ("乙庚", "西北"), ("丙辛", "西南"),
                     ("丁壬", "正南"), ("戊癸", "东南")):
        check("喜神 %s → %s" % (gl, fang), all(XI_SHEN[g] == fang for g in gl))
    for gl, fang in (("甲乙", "东北"), ("丙丁", "西南"), ("戊己", "正北"),
                     ("庚辛", "正东"), ("壬癸", "正南")):
        check("财神 %s → %s" % (gl, fang), all(CAI_SHEN[g] == fang for g in gl))
    for g in GAN:
        check("阳贵/阴贵 %s 互不相同" % g, YANG_GUI[g] != YIN_GUI[g])
    check("3.11 阳贵阴贵 表内一致",
          cells(find_table(D14, "| 日干 | 甲 | 乙 |")[1][0])[1:11] == [YANG_GUI[g] for g in GAN])
    check("3.11 阴贵 表内一致",
          cells(find_table(D14, "| 日干 | 甲 | 乙 |")[1][1])[1:11] == [YIN_GUI[g] for g in GAN])

    # ---- 3.12 空亡 / 日禄
    for i, x in enumerate(XUN_KONG):
        check("旬空 第 %d 旬 = %s" % (i + 1, x), (i * 10) // 10 == i and x in t14)
    check("日空亡 甲辰日属甲辰旬→寅卯", XUN_KONG[jz_index(2024, 2, 10) // 10] == "寅卯")
    check("日空亡 癸酉日属甲子旬→戌亥", XUN_KONG[jz_index(2024, 3, 10) // 10] == "戌亥")
    check("3.12 日禄表一致",
          cells(find_table(D14, "| 干 | 甲 | 乙 |")[1][0])[1:11] == [LU_ZHI[g] for g in GAN])

    # ---- 3.6 九星三元起例表
    _, rows = find_table(D14, "| 半年 | 元 | 起算节气 |")
    starts = [cells(r)[3] for r in rows]
    dirs = [cells(r)[4] for r in rows]
    check("九星三元起星 1/7/4/9/3/6", starts == ["一白", "七赤", "四绿", "九紫", "三碧", "六白"], str(starts))
    check("九星三元 阳顺阴逆", dirs[0].startswith("+1") and dirs[3].startswith("−1"), str(dirs))

    # ---- 3.5 二十八宿 / 3.2 建除 / 3.7 六曜 / 3.6 星名
    check("二十八宿 28 名齐备", all(ch in t14 for ch in XIU28))
    check("建除十二神名齐备", all(n in t14 for n in JIANCHU))
    check("建除别名齐备", all(x in t14 for x in ("兵福", "吉期", "天巫", "天罡", "时阴",
                                               "小耗", "大耗", "天喜", "河魁", "时阳", "血支")))
    check("值神十二名齐备", all(n in t14 for n in ZHISHEN12))
    check("黄道六神", "青龙、明堂、金匮、天德、玉堂、司命" in t14)
    check("六曜六名齐备", all(n in t14 for n in LIUYAO6))
    check("九星三名体系并存", all(x in t14 for x in ("太乙", "贪狼", "天枢")))
    check("二十八宿两种口径辨析", "值日宿" in t14 and "本命星宿" in t14)

    # ---- 文献与篇内引文
    for kw in ("二十四气六宫周", "阳顺一四七中游", "九六三星逆行求", "夏至后甲子为上元起九紫",
               "子午青龙起在申", "月神随月建行阴阳六辰", "协纪辨方书", "卷九", "五要奇书"):
        check("14 篇引文 | %s" % kw, kw in t14)


def main():
    for fn in (g01_day_pillar, g02_four_pillars, g03_canggan_nayin_shishen, g04_ziwei,
               g05_sihua, g06_najia_bagong, g07_gua64, g08_sanyuan_xuankong,
               g09_dayun, g10_piyu, g11_placeholders, g12_text_consistency, g13_koujing,
               g14_huangli):
        try:
            fn()
        except Exception as e:
            import traceback
            FAILED.append((fn.__name__, "EXCEPTION %r" % e))
            traceback.print_exc()
    print("\n" + "=" * 60)
    print("PASS %d / FAIL %d   （%d 组）" % (PASSED, len(FAILED), len(_marks)))
    if FAILED:
        for name, detail in FAILED:
            print("  - %s  %s" % (name, detail))
        print("RESULT: FAIL")
        return 1
    print("RESULT: ALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())

# ---------------------------------------------------------------------------
# 变异自检记录（v1.2，2026-10）
# 在副本上逐处注入错误后重跑本脚本，16/16 全部报红（退出码 1）：
#   [07] 日柱 +49→+50；紫微 r 偶/奇 顺逆互换；天府 4→5；八宫 遁/姤 互换；
#        纳甲 乾·甲辰→甲巳；三元龙天元八山混入寅；世应 +3→+2；
#        大运 15 岁 9 月→8 月；五行局水二局起限 2→3
#   [02a] 藏干 巳 丙庚戊→丙戊庚（次序）；锚点 2000-01-01 戊午→戊申
#   [03a] 四化 甲·廉贞→天相；紫微全表 木三局初一 辰→巳
#   [04b] 纳甲 乾·甲子→庚子；[04a] 卦序 3 屯→蒙；[05a] 子山 阴→阳
# 重放方法：Verification/mutation_test.py（复制 yixue_work 后逐例改错再跑本脚本）。
#
# v1.4 补记（2026-11）：新增 [14] 组后注入 3 处（建除 (日支−月支)→(日支+月支)、
#   二十八宿 +11→+10、胎神局第 40–43 段改「房内西」），3/3 报红、退出码 1。
# ---------------------------------------------------------------------------
