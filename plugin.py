#!/usr/bin/env python
# -*- coding: utf-8 -*-

import os
import queue
import re
import sys
import traceback
import uuid
import threading
import xml.etree.ElementTree as ET

_PLUGIN_DIR = os.path.dirname(os.path.abspath(__file__))
_VENDOR_DIR = os.path.join(_PLUGIN_DIR, 'vendor')
if os.path.isdir(_VENDOR_DIR) and _VENDOR_DIR not in sys.path:
    sys.path.insert(0, _VENDOR_DIR)

import tkinter as tk
from tkinter import ttk, messagebox


# 需要排除混淆的 HTML 标签
_EXCLUDE_TAGS = frozenset({'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'script', 'style', 'code', 'pre'})
# 需要排除混淆的 class 值
_EXCLUDE_CLASSES = frozenset({'cut', 'int', 'spe', 'duokan-footnote-item', 'zhangyue-footnote'})
# 需要排除的 class 后缀
_EXCLUDE_CLASS_SUFFIX = '-Regular'

# 从 DOM 路径的排除常量动态生成回退路径使用的排除正则
def _build_fallback_exclude_re():
    """从 _EXCLUDE_TAGS / _EXCLUDE_CLASSES / _EXCLUDE_CLASS_SUFFIX 动态生成排除正则。"""
    parts = []
    if _EXCLUDE_TAGS:
        tags = '|'.join(re.escape(t) for t in sorted(_EXCLUDE_TAGS))
        parts.append(rf'<({tags})\b[^>]*>.*?</\1>')
    if _EXCLUDE_CLASSES:
        classes = '|'.join(re.escape(c) for c in sorted(_EXCLUDE_CLASSES))
        parts.append(
            rf'<\w+\s[^>]*\bclass=["\'][^"\']*\b(?:{classes})\b[^"\']*["\'][^>]*>.*?</\w+>'
        )
    if _EXCLUDE_CLASS_SUFFIX:
        suffix = re.escape(_EXCLUDE_CLASS_SUFFIX)
        parts.append(
            rf'<\w+\s[^>]*\bclass=["\'][^"\']*{suffix}["\'][^>]*>.*?</\w+>'
        )
    return re.compile('|'.join(parts), re.S) if parts else re.compile(r'(?!)')

_FALLBACK_EXCLUDE_RE = _build_fallback_exclude_re()


def _preflight_check():
    """启动前依赖预检，返回错误列表（空列表表示通过）。"""
    errors = []

    try:
        from fontTools.ttLib import TTFont
        from fontTools.fontBuilder import FontBuilder
        from fontTools.pens.ttGlyphPen import TTGlyphPen
    except Exception as exc:
        errors.append(
            f"fontTools 库加载失败：{type(exc).__name__}: {exc}\n"
            "请运行重新构建插件，或手动安装：\n"
            "  pip install fonttools"
        )

    ttf_path = os.path.join(_PLUGIN_DIR, 'MiSans-Regular.ttf')
    if not os.path.isfile(ttf_path):
        errors.append(f"源字体文件缺失：{ttf_path}")

    chars_path = os.path.join(_PLUGIN_DIR, 'characters.txt')
    if not os.path.isfile(chars_path):
        errors.append(f"字符集文件缺失：{chars_path}")

    return errors


def random_name():
    """生成随机文件名。"""
    return uuid.uuid4().hex[:16]

def _walk_text_nodes(elem, visitor_fn):
    """通用 DOM 文本节点遍历器，跳过排除的子树。

    visitor_fn(text, is_tail) -> new_text 或 None（None 表示不修改）
    """
    if _should_exclude_element(elem):
        return
    if elem.text:
        result = visitor_fn(elem.text, False)
        if result is not None:
            elem.text = result
    for child in elem:
        _walk_text_nodes(child, visitor_fn)
        if child.tail:
            result = visitor_fn(child.tail, True)
            if result is not None:
                child.tail = result


def _translate_element_text(elem, translate_table):
    """递归翻译元素的文本节点，跳过排除的子树。"""
    _walk_text_nodes(elem, lambda text, _: text.translate(translate_table))


def _collect_text_from_element(elem, chars, easy_font_set):
    """递归收集元素中的文本字符，跳过排除的子树。"""
    def _collector(text, _is_tail):
        for c in text:
            if c in easy_font_set:
                chars.add(c)
        return None
    _walk_text_nodes(elem, _collector)


def _detect_namespace(content):
    """检测并注册 XHTML 内容中的所有命名空间。"""
    ns = ''
    # 注册默认命名空间（xmlns="..." 或 xmlns='...'）
    default_match = re.search(r'\bxmlns\s*=\s*([\'"])([^\'"]+)\1', content)
    if default_match:
        ns = default_match.group(2)
        ET.register_namespace('', ns)
    # 注册所有前缀命名空间（xmlns:prefix="..." 或 xmlns:prefix='...'）
    for prefix_match in re.finditer(r'\bxmlns:(\w+)\s*=\s*([\'"])([^\'"]+)\2', content):
        prefix = prefix_match.group(1)
        uri = prefix_match.group(3)
        if prefix != 'xml':  # xml 命名空间是内置的，不需要重新注册
            ET.register_namespace(prefix, uri)
    return ns


def _inject_wrapper_div(body, ns_prefix, wrapper_class):
    """通过 DOM 操作在 body 子元素外层注入包装 div。"""
    wrapper = ET.SubElement(body, f'{ns_prefix}div')
    wrapper.set('class', wrapper_class)
    # 将所有现有子元素（除了新创建的 wrapper）移入其中
    children = list(body)
    for child in children:
        if child is not wrapper:
            body.remove(child)
            wrapper.append(child)
    # 保留 body 的文本内容
    wrapper.text = body.text
    body.text = '\n'
    wrapper.tail = '\n'


def convert_xhtml(content, wrapper_class, translate_table):
    """翻译 <body> 中的文本，注入包装 div，跳过排除元素。

    使用 ET 解析进行安全的节点级翻译，但只序列化 <body> 并拼接回原始字符串。
    这样可以保留原始的声明头、<html> 属性、<head>、命名空间和格式。
    """
    try:
        ns = _detect_namespace(content)
        root = ET.fromstring(content)
    except ET.ParseError:
        return _convert_regex_fallback(content, wrapper_class, translate_table)

    # 查找 <body>
    ns_prefix = '{' + ns + '}' if ns else ''
    body = root.find(f'.//{ns_prefix}body')
    if body is None:
        return _convert_regex_fallback(content, wrapper_class, translate_table)

    # 只翻译 .text 和 .tail，不修改属性
    _translate_element_text(body, translate_table)

    # 通过 DOM 注入包装 div
    _inject_wrapper_div(body, ns_prefix, wrapper_class)

    # 只序列化 <body> 元素（不序列化整棵树）
    new_body_str = ET.tostring(body, encoding='unicode', method='xml')

    # 用原始 <body> 开标签替换 ET 生成的版本（移除多余的 xmlns 声明，保留原始属性）
    orig_body_open_match = re.search(r'<body[^>]*>', content, re.I | re.S)
    if orig_body_open_match:
        orig_body_tag = orig_body_open_match.group()
        new_body_str = re.sub(r'<body[^>]*>', lambda _m: orig_body_tag, new_body_str, count=1)

    # 拼接：将原始内容中 <body>...</body> 替换为新内容
    # 这样 <body> 外部的一切保持原样不变
    body_open_re = re.compile(r'<(?:\w+:)?body[\s>]', re.I)
    body_close_re = re.compile(r'</(?:\w+:)?body\s*>', re.I)

    open_match = body_open_re.search(content)
    close_match = body_close_re.search(content)

    if open_match and close_match:
        before_body = content[:open_match.start()]
        after_body = content[close_match.end():]
        return before_body + new_body_str + after_body

    # 原始字符串中找不到 body 标签
    return _convert_regex_fallback(content, wrapper_class, translate_table)


# 需要保护内容不被翻译的块级标签（script/style/code/pre）
_PROTECTED_TAG_OPEN_RE = re.compile(
    r'<(script|style|code|pre)\b[^>]*>.*?</\1\s*>',
    re.I | re.S
)


def _convert_regex_fallback(content, wrapper_class, translate_table):
    """简化的回退方案：用于格式异常的 XHTML，只翻译标签之间的文本。"""

    # 使用统一的排除正则保护排除元素
    placeholders = {}
    counter = [0]

    def _protect(m):
        key = f'\uFDD0PROTECT{counter[0]}\uFDD0'
        counter[0] += 1
        placeholders[key] = m.group()
        return key

    content = _FALLBACK_EXCLUDE_RE.sub(_protect, content)
    # 保护 script/style/code/pre 块级标签的内容不被翻译
    content = _PROTECTED_TAG_OPEN_RE.sub(_protect, content)

    # 只翻译标签外部的文本：按标签分割，翻译文本段
    parts = re.split(r'(<[^>]+>)', content)
    for i, part in enumerate(parts):
        if not part.startswith('<'):
            parts[i] = part.translate(translate_table)
    result = ''.join(parts)

    # 还原被保护的排除元素（反向遍历，确保嵌套占位符正确展开）
    for key, original in reversed(list(placeholders.items())):
        result = result.replace(key, original)

    # 注入包装 div
    result = re.sub(r'(<body[^>]*>)', r'\1\n<div class="' + wrapper_class + r'">\n', result, count=1, flags=re.S)
    result = re.sub(r'(</body>)', r'\n</div>\n\1', result, count=1, flags=re.S)
    return result

def _find_linked_css_ids(bk, html_id):
    """解析 HTML 查找关联的 CSS 文件的 manifest ID。"""
    html_content = bk.readfile(html_id)
    html_bookpath = bk.id_to_bookpath(html_id)
    html_dir = bk.get_startingdir(html_bookpath)
    css_ids = []
    for match in re.finditer(r'<link[^>]+href=["\']([^"\']+)["\'][^>]*>', html_content):
        href = match.group(1)
        if href.endswith('.css'):
            css_bookpath = bk.build_bookpath(href, html_dir)
            css_id = bk.bookpath_to_id(css_bookpath)
            if css_id:
                css_ids.append(css_id)
    return css_ids


def inject_css_to_existing(bk, html_ids, wrapper_class, ttf_name):
    """将 @font-face 规则注入到 HTML 关联的已有 CSS 文件中。"""
    all_css_ids = set()
    for html_id in html_ids:
        css_ids = _find_linked_css_ids(bk, html_id)
        all_css_ids.update(css_ids)

    if not all_css_ids:
        return

    font_bookpath = bk.id_to_bookpath(ttf_name + ".ttf")

    for css_id in all_css_ids:
        existing_css = bk.readfile(css_id)
        css_bookpath = bk.id_to_bookpath(css_id)
        font_rel_path = bk.get_relativepath(css_bookpath, font_bookpath)

        # 检查是否已注入过该类名
        if re.search(rf'\.{re.escape(wrapper_class)}\b', existing_css):
            continue

        safe_rel = font_rel_path.replace('"', r'\"')
        new_rule = (
            f'@font-face {{font-family: "{wrapper_class}";\n'
            f'src: url("{safe_rel}");}}\n'
            f'.{wrapper_class}{{font-family: "{wrapper_class}" !important;}}\n'
        )

        css_snippet = '/* Font_Encrypt */\n' + new_rule
        if '/* Font_Encrypt */' in existing_css:
            existing_css = existing_css.replace(
                '/* Font_Encrypt */',
                '/* Font_Encrypt */\n' + new_rule,
                1,
            )
            bk.writefile(css_id, existing_css)
        else:
            bk.writefile(css_id, css_snippet + existing_css.lstrip())

def _should_exclude_element(elem):
    """检查元素是否匹配任何排除规则。"""
    tag = elem.tag.split('}')[-1] if '}' in elem.tag else elem.tag
    if tag in _EXCLUDE_TAGS:
        return True
    cls = elem.get('class', '')
    cls_parts = cls.split()
    for part in cls_parts:
        if part in _EXCLUDE_CLASSES or part.endswith(_EXCLUDE_CLASS_SUFFIX):
            return True
    return False


def _collect_chars(selected_items, html_contents, easy_font_set):
    """从 HTML 内容中收集需要混淆的字符集。"""
    chars = set()
    for Id, _href in selected_items:
        content = html_contents[Id]
        try:
            _detect_namespace(content)
            xml_root = ET.fromstring(content)
        except ET.ParseError:
            cleaned = _FALLBACK_EXCLUDE_RE.sub('', content)
            cleaned = _PROTECTED_TAG_OPEN_RE.sub('', cleaned)
            text = re.sub(r'<[^>]+>', '', cleaned)
            for c in text:
                if c in easy_font_set:
                    chars.add(c)
            continue
        body = None
        for elem in xml_root.iter():
            tag = elem.tag.split('}')[-1] if '}' in elem.tag else elem.tag
            if tag == 'body':
                body = elem
                break
        target = body if body is not None else xml_root
        _collect_text_from_element(target, chars, easy_font_set)
    return chars


def _transform_chapters(selected_items, html_contents, translate_table, wrapper_class, progress_cb=None):
    """逐章转换 XHTML 内容。"""
    transformed = {}
    for idx, (Id, _href) in enumerate(selected_items):
        content = html_contents[Id]
        transformed[Id] = convert_xhtml(content, wrapper_class, translate_table)
        if progress_cb:
            progress_cb(idx + 1)
    return transformed


def run(bk):

    # 依赖预检
    preflight_errors = _preflight_check()
    if preflight_errors:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror(
            "Font_Encrypt - 启动失败",
            "插件依赖检查未通过：\n\n" + "\n\n".join(preflight_errors)
        )
        root.destroy()
        return 1

    # 延迟导入已移至 worker 线程内部

    text_iter = list(bk.text_iter())

    root = tk.Tk()
    root.title("Font_Encrypt - 章节选择")
    root.minsize(450, 300)

    tree_height = max(5, min(len(text_iter), 20))
    tree = ttk.Treeview(
        root, columns=("Data1", "Data2"),
        show="headings", height=tree_height, style="Treeview"
    )
    tree.column("#0", width=0, stretch=tk.NO)
    tree.column("Data1", anchor=tk.W, width=180)
    tree.column("Data2", anchor=tk.W, width=220)
    tree.heading("Data1", text="文件标识 (ID)")
    tree.heading("Data2", text="文件路径 (Href)")

    scroll_bar = ttk.Scrollbar(root, orient=tk.VERTICAL, command=tree.yview)
    tree.configure(yscrollcommand=scroll_bar.set)

    for index, (data1, data2) in enumerate(text_iter):
        tree.insert(parent="", index=tk.END, iid=index, values=(data1, data2))

    def _set_ui_state(state):
        """启用或禁用所有交互式 UI 元素。"""
        button.config(state=state, text="正在处理中..." if state == tk.DISABLED else "开始处理")
        tree.config(selectmode='none' if state == tk.DISABLED else 'extended')
        for btn in btn_frame.winfo_children():
            btn.config(state=state)

    def run_selected_items():
        selected_items = []
        for i in tree.selection():
            selected_items.append(tree.item(i)['values'])

        if not selected_items:
            messagebox.showwarning("提示", "请先在列表中选择需要加密的章节！")
            return

        # 处理中禁用 UI
        _set_ui_state(tk.DISABLED)
        total = len(selected_items)
        progress = ttk.Progressbar(root, mode='indeterminate', length=300)
        progress.grid(row=4, column=0, columnspan=2, padx=10, pady=(0, 5))
        progress.start(10)  # 启动滚动动画
        progress_label = ttk.Label(root, text="准备中...")
        progress_label.grid(row=5, column=0, columnspan=2, pady=(0, 5))
        root.update()

        # 工作线程与主线程通信队列
        msg_queue = queue.Queue()

        # 在主线程读取所有 HTML 内容（bk I/O 安全）
        html_contents = {}
        for Id, href in selected_items:
            html_contents[Id] = bk.readfile(Id)

        def _worker():
            """纯计算工作线程：不执行 bk I/O，结果通过队列发送。"""
            try:
                from confuseFont import filter_emoji, _EASY_FONT_SET, obfuscate_plus
                msg_queue.put(('status', '正在扫描分析章节文本...'))

                # 收集明文字符
                chars = _collect_chars(selected_items, html_contents, _EASY_FONT_SET)
                plain_text = filter_emoji(''.join(sorted(chars)))

                # 生成混淆字体
                msg_queue.put(('status', '正在生成混淆字体（较耗时）...'))
                ttf_name = random_name()
                fenc_list, font_data = obfuscate_plus(plain_text)
                translate_table = str.maketrans(dict(zip(list(plain_text), fenc_list)))

                # 逐章转换
                wrapper_class = f'fenc_{ttf_name}'
                msg_queue.put(('status', f'正在转换章节... 0/{total}'))
                transformed = _transform_chapters(
                    selected_items, html_contents, translate_table, wrapper_class,
                    progress_cb=lambda n: msg_queue.put(('progress', n))
                )

                msg_queue.put(('done', {
                    'ttf_name': ttf_name,
                    'font_data': font_data,
                    'transformed': transformed,
                    'wrapper_class': wrapper_class,
                    'html_ids': [Id for Id, _ in selected_items],
                }))
            except Exception as e:
                msg_queue.put(('error', e))
            finally:
                from confuseFont import clear_font_cache
                clear_font_cache()

        def _poll_queue():
            """轮询消息队列，处理工作线程的结果。"""
            try:
                while True:
                    msg_type, payload = msg_queue.get_nowait()
                    if msg_type == 'status':
                        progress_label.config(text=payload)
                    elif msg_type == 'progress':
                        # 首次收到 progress 时切换为 determinate 模式
                        if str(progress.cget('mode')) != 'determinate':
                            progress.stop()
                            progress.config(mode='determinate', maximum=total)
                        progress['value'] = payload
                        progress_label.config(text=f"转换中... {payload}/{total}")
                    elif msg_type == 'done':
                        # 在主线程执行所有 bk 写入操作
                        progress.stop()
                        try:
                            _apply_results(payload)
                            progress.grid_forget()
                            progress_label.grid_forget()
                            messagebox.showinfo("完成", f"成功处理了 {total} 个章节！")
                            root.quit()
                        except Exception as apply_err:
                            progress.grid_forget()
                            progress_label.grid_forget()
                            _handle_error(apply_err)
                            _set_ui_state(tk.NORMAL)
                        return
                    elif msg_type == 'error':
                        progress.grid_forget()
                        progress_label.grid_forget()
                        _handle_error(payload)
                        _set_ui_state(tk.NORMAL)
                        return
            except queue.Empty:
                pass
            root.after(100, _poll_queue)

        def _apply_results(data):
            """在主线程执行所有 bk I/O 操作。"""
            bk.addfile(data['ttf_name'] + ".ttf", data['ttf_name'] + ".ttf", data['font_data'])
            # 注入 CSS（需要 bk.readfile 读取 CSS 文件）
            inject_css_to_existing(bk, data['html_ids'], data['wrapper_class'], data['ttf_name'])
            for Id, content in data['transformed'].items():
                bk.writefile(Id, content)

        def _handle_error(err):
            """统一的错误处理函数。"""
            from confuseFont import FontEncryptError
            if isinstance(err, ImportError):
                messagebox.showerror("依赖缺失", f"缺少必要的库：\n{err}")
            elif isinstance(err, FontEncryptError):
                messagebox.showerror("处理失败", str(err))
            else:
                tb_str = ''.join(traceback.format_exception(type(err), err, err.__traceback__))
                messagebox.showerror(
                    "处理异常",
                    f"执行过程中发生意外错误：\n\n{type(err).__name__}: {err}"
                    f"\n\n--- Traceback ---\n{tb_str}"
                )

        worker_thread = threading.Thread(target=_worker, daemon=True)
        worker_thread.start()
        root.after(100, _poll_queue)

    tree.grid(row=0, column=0, sticky='nsew')
    scroll_bar.grid(row=0, column=1, sticky='ns')

    btn_frame = ttk.Frame(root)
    btn_frame.grid(row=1, column=0, columnspan=2, pady=(5, 0))

    def _select_all():
        for item in tree.get_children():
            tree.selection_add(item)

    def _deselect_all():
        tree.selection_remove(*tree.get_children())

    ttk.Button(btn_frame, text="全选", width=8, command=_select_all).pack(side=tk.LEFT, padx=5)
    ttk.Button(btn_frame, text="取消全选", width=8, command=_deselect_all).pack(side=tk.LEFT, padx=5)

    introduction_text = "请在上述列表中，Ctrl选取 或 Shift选取"
    label = ttk.Label(root, text=introduction_text, justify=tk.LEFT)
    label.grid(row=2, column=0, columnspan=2, padx=10, pady=(5, 0))

    button = ttk.Button(root, text="开始处理", command=run_selected_items)
    button.grid(row=3, column=0, columnspan=2, pady=10)

    root.columnconfigure(0, weight=1)
    root.rowconfigure(0, weight=1)

    root.mainloop()
    return 0


def main():
    print("I reached main when I should not have\n")
    return -1


if __name__ == "__main__":
    sys.exit(main())
