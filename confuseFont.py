# coding:utf-8
import io
import os
import random
import re
import unicodedata
import itertools

from fontTools.ttLib import TTFont
from fontTools.fontBuilder import FontBuilder
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.pens.recordingPen import DecomposingRecordingPen

# 字体名称配置
FAMILY_NAME = 'MyAwesomeFont'
STYLE_NAME = 'Regular'
SRC_FONT_NAME = 'DreamHanSansCN-W15'

# 字体缓存
_FONT_CACHE = {}
# CJK 候选码位池缓存
_CJK_POOL_CACHE = {}


def _safe_close_font(font):
    """安全关闭 TTFont 对象，忽略关闭时的异常。"""
    try:
        font.close()
    except Exception:
        pass


def _load_font(path):
    """加载字体文件，带缓存。路径归一化防重复 key。替换前先关闭旧对象。"""
    norm_path = os.path.normpath(path)
    if norm_path not in _FONT_CACHE:
        new_font = TTFont(path)  # 先打开新字体，成功后再替换
        for old_font in _FONT_CACHE.values():
            _safe_close_font(old_font)
        _FONT_CACHE.clear()
        _FONT_CACHE[norm_path] = new_font
    return _FONT_CACHE[norm_path]


def clear_font_cache():
    """显式释放字体缓存，关闭 TTFont 对象。"""
    for font in _FONT_CACHE.values():
        _safe_close_font(font)
    _FONT_CACHE.clear()
    _CJK_POOL_CACHE.clear()

# 字体 name 表信息
NAME_STRING = {
    'familyName': FAMILY_NAME,
    'styleName': STYLE_NAME,
    'psName': FAMILY_NAME + '-' + STYLE_NAME,
    'copyright': 'Created by RUD',
    'version': 'Version 3.6',
}

def _load_characters():
    """从外部文件加载混淆字符集。"""
    chars_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'characters.txt')
    with open(chars_path, 'r', encoding='utf-8') as f:
        return f.read().strip()

# 加载混淆字符集
easy_font = _load_characters()
# 模块级缓存集合，用于快速查找
_EASY_FONT_SET = frozenset(easy_font)

# CJK 码位范围
_CJK_RANGES = (range(0x3400, 0x4DC0), range(0x4E00, 0xA000))


def _iter_cjk():
    """惰性迭代所有 CJK 码位。"""
    return itertools.chain.from_iterable(_CJK_RANGES)


def _get_cjk_pool(font_path, original_cmap):
    """获取 CJK 候选码位池，带缓存。同一字体路径只计算一次。"""
    norm_path = os.path.normpath(font_path)
    if norm_path not in _CJK_POOL_CACHE:
        _CJK_POOL_CACHE[norm_path] = [c for c in _iter_cjk() if c in original_cmap]
    return _CJK_POOL_CACHE[norm_path]


def str_has_whitespace(s: str) -> bool:
    """检查字符串是否包含空格。"""
    return ' ' in s


# Emoji 检测正则
_EMOJI_RE = re.compile(
    '['
    '\U0001F600-\U0001F64F'  # 表情符号
    '\U0001F300-\U0001F5FF'  # 杂项符号和象形文字
    '\U0001F680-\U0001F6FF'  # 交通和地图符号
    '\U0001F900-\U0001F9FF'  # 补充符号
    '\U0001FA00-\U0001FA6F'  # 棋类符号
    '\U0001FA70-\U0001FAFF'  # 扩展符号 A
    '\U0001F1E0-\U0001F1FF'  # 旗帜
    ']'
)


def filter_emoji(s: str) -> str:
    """移除字符串中的 emoji 字符，使其不参与混淆。"""
    return _EMOJI_RE.sub('', s)


def deduplicate_str(s: str) -> str:
    """字符串去重。"""
    return "".join(dict.fromkeys(s))


def _is_fullwidth(c: str) -> bool:
    """判断字符是否为全角宽度。"""
    eaw = unicodedata.east_asian_width(c)
    return eaw in ('F', 'W')


class FontEncryptError(Exception):
    """FontEncrypt 插件基础异常。"""
    pass


class MissingGlyphError(FontEncryptError):
    """源字体缺少所需字符时抛出。"""
    pass


class InvalidInputError(FontEncryptError):
    """输入文本无效时抛出。"""
    pass


class CodePointExhaustedError(FontEncryptError):
    """可用码位不足时抛出。"""
    pass


def ensure_cmap_has_all_text(cmap: dict, s: str) -> bool:
    """检查源字体 cmap 是否包含所有需要的字符。"""
    missing = [c for c in s if ord(c) not in cmap]
    if missing:
        sample = ''.join(missing[:5])
        raise MissingGlyphError(
            f'源字体缺少以下字符（共 {len(missing)} 个）：{sample}'
            + ('...' if len(missing) > 5 else '')
            + '\n请更换字体或移除这些字符。'
        )
    return True


def obfuscate_plus(plain_text):
    """
    生成混淆字体并返回字符映射和字体数据。

    :param plain_text: 需要混淆的明文字符集
    :return: (映射后的字符列表, 字体二进制数据 bytes)
    """
    plugin_dir = os.path.dirname(os.path.abspath(__file__))
    if str_has_whitespace(plain_text):
        raise InvalidInputError('明文不允许含有空格，请检查输入文本。')

    # 过滤 emoji
    plain_text = filter_emoji(plain_text)

    # 去重
    plain_text = deduplicate_str(plain_text)

    # 加载源字体
    original_font = _load_font(os.path.join(plugin_dir, f'{SRC_FONT_NAME}.ttf'))
    original_cmap: dict = original_font.getBestCmap()

    # 验证源字体包含所有所需字符
    ensure_cmap_has_all_text(original_cmap, plain_text)

    glyphs, metrics, cmap = {}, {}, {}

    plain_ords = set(ord(c) for c in plain_text)

    # 将明文字符按全角/半角分类
    fw_indices = [i for i, c in enumerate(plain_text) if _is_fullwidth(c)]
    hw_indices = [i for i, c in enumerate(plain_text) if not _is_fullwidth(c)]

    # 使用缓存的 CJK 候选码位池
    font_path = os.path.join(plugin_dir, f'{SRC_FONT_NAME}.ttf')
    all_cjk_in_cmap = _get_cjk_pool(font_path, original_cmap)

    # 全角字符 -> CJK 码位（East Asian Width = W）
    cjk_candidates = [
        c for c in all_cjk_in_cmap
        if c not in plain_ords and c != 0x7684
    ]
    if len(cjk_candidates) < len(fw_indices):
        raise CodePointExhaustedError(
            f'CJK 码位不足：需要 {len(fw_indices)} 个，仅有 {len(cjk_candidates)} 个可用。\n'
            '请减少选中章节的字符数量。'
        )

    # 半角字符 -> BMP 私有使用区（U+E000-U+F8FF，East Asian Width = Neutral）
    pua_candidates = [c for c in range(0xE000, 0xF900) if c not in plain_ords]
    if len(pua_candidates) < len(hw_indices):
        raise CodePointExhaustedError(
            f'PUA 码位不足：需要 {len(hw_indices)} 个，仅有 {len(pua_candidates)} 个可用。\n'
            '请减少选中章节的半角字符数量。'
        )

    # 随机采样码位
    fw_codes = random.sample(cjk_candidates, len(fw_indices))
    hw_codes = random.sample(pua_candidates, len(hw_indices))

    # 合并为按位置排列的私有码位列表
    private_codes = [0] * len(plain_text)
    for pos, code in zip(fw_indices, fw_codes):
        private_codes[pos] = code
    for pos, code in zip(hw_indices, hw_codes):
        private_codes[pos] = code

    glyph_set = original_font.getGlyphSet()

    pen = TTGlyphPen(glyph_set)

    def _draw_glyph(glyph_name):
        """绘制字形，自动分解复合字形为轮廓。"""
        rec_pen = DecomposingRecordingPen(glyph_set)
        glyph_set[glyph_name].draw(rec_pen)
        rec_pen.replay(pen)

    glyph_order = original_font.getGlyphOrder()

    final_shadow_text: list = []

    # 添加特殊字形
    if 'null' in glyph_order:
        _draw_glyph('null')
        glyphs['null'] = pen.glyph()
        metrics['null'] = original_font['hmtx']['null']
        final_shadow_text += ['null']

    if '.notdef' in glyph_order:
        _draw_glyph('.notdef')
        glyphs['.notdef'] = pen.glyph()
        metrics['.notdef'] = original_font['hmtx']['.notdef']
        final_shadow_text += ['.notdef']

    html_entities = []

    # 复用已构建的 CJK 池选择影子字形
    seen_glyph_names = set(final_shadow_text)
    unique_cjk = []
    for c in all_cjk_in_cmap:
        gname = original_cmap[c]
        if gname not in seen_glyph_names:
            seen_glyph_names.add(gname)
            unique_cjk.append(c)
    if len(unique_cjk) < len(plain_text):
        raise CodePointExhaustedError(
            f'CJK 影子码位不足：需要 {len(plain_text)} 个唯一字形，'
            f'仅有 {len(unique_cjk)} 个可用。\n'
            '请减少选中章节的字符数量，或更换字形更丰富的源字体。'
        )
    cjk_codes = random.sample(unique_cjk, len(plain_text))

    # 构建字形映射：私有码位 -> 影子字形名 -> 原始字形轮廓
    for index, plain in enumerate(plain_text):
        shadow_cmap_name = original_cmap[cjk_codes[index]]

        final_shadow_text += [shadow_cmap_name]

        _draw_glyph(original_cmap[ord(plain)])
        glyphs[shadow_cmap_name] = pen.glyph()

        metrics[shadow_cmap_name] = original_font['hmtx'][original_cmap[ord(plain)]]

        cmap[private_codes[index]] = shadow_cmap_name
        html_entities += [chr(private_codes[index])]

    # 多看兼容：强制确保 U+7684（的）在 cmap 中有映射
    # 多看通过检测「的」码位是否有字形来判断是否为 CJK 字体
    DE_CODE = 0x7684
    if DE_CODE not in cmap:
        de_glyph_name = original_cmap.get(DE_CODE)
        if de_glyph_name and de_glyph_name not in glyphs:
            _draw_glyph(de_glyph_name)
            glyphs[de_glyph_name] = pen.glyph()
            metrics[de_glyph_name] = original_font['hmtx'][de_glyph_name]
            final_shadow_text.append(de_glyph_name)
        if de_glyph_name:
            cmap[DE_CODE] = de_glyph_name

    # 构建水平排版头信息
    horizontal_header = {
        'ascent': original_font['hhea'].ascent,
        'descent': original_font['hhea'].descent,
    }

    # 构建新字体
    fb = FontBuilder(original_font['head'].unitsPerEm, isTTF=True)
    # 按码位排序字形顺序
    reverse_cmap = {v: k for k, v in cmap.items()}
    special_glyphs = [g for g in final_shadow_text if g not in reverse_cmap]
    mapped_glyphs = [g for g in final_shadow_text if g in reverse_cmap]
    mapped_glyphs.sort(key=lambda g: reverse_cmap[g])
    final_shadow_text = special_glyphs + mapped_glyphs
    fb.setupGlyphOrder(final_shadow_text)
    fb.setupCharacterMap(cmap)
    fb.setupGlyf(glyphs)
    fb.setupHorizontalMetrics(metrics)
    fb.setupHorizontalHeader(**horizontal_header)
    fb.setupNameTable(NAME_STRING)
    # 复制 OS/2 表关键字段
    src_os2 = original_font['OS/2']
    fb.setupOS2(
        sTypoAscender=src_os2.sTypoAscender,
        sTypoDescender=src_os2.sTypoDescender,
        sTypoLineGap=src_os2.sTypoLineGap,
        usWinAscent=src_os2.usWinAscent,
        usWinDescent=src_os2.usWinDescent,
        fsType=0x0000,
    )
    fb.setupPost()

    # 直接写入内存缓冲区，避免临时文件
    buf = io.BytesIO()
    fb.save(buf)
    font_data = buf.getvalue()

    return html_entities, font_data
