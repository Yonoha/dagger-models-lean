"""Conservative Lean 4.27 header-import scanner for staged CI preflight.

This intentionally accepts only ordinary dotted ASCII module names. Lean's
compiler remains authoritative; this scanner only rejects unexpected imports
before candidate sources enter an isolated build.
"""

import re
from pathlib import Path


MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def _skip(text: str, pos: int) -> int:
    """Skip Lean line comments, nested block comments, and whitespace."""
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif text.startswith("--", pos):
            end = text.find("\n", pos + 2)
            pos = len(text) if end < 0 else end + 1
        elif text.startswith("/-", pos):
            depth = 1
            pos += 2
            while depth:
                if pos >= len(text):
                    raise ValueError("Unterminated Lean block comment in module header")
                if text.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif text.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
        else:
            break
    return pos


def _word(text: str, pos: int, word: str) -> bool:
    if not text.startswith(word, pos):
        return False
    end = pos + len(word)
    return (end == len(text) or text[end].isspace() or
            text.startswith("--", end) or text.startswith("/-", end))


def header_imports(path: Path) -> list[str]:
    """Read valid-shaped header imports, rejecting unsupported import spellings."""
    text = path.read_text(encoding="utf-8")
    pos = _skip(text, 0)
    has_module = _word(text, pos, "module")
    if has_module:
        pos = _skip(text, pos + len("module"))
    if _word(text, pos, "prelude"):
        pos = _skip(text, pos + len("prelude"))
    imports = []
    while pos < len(text):
        start = pos
        public = _word(text, pos, "public")
        if public:
            pos = _skip(text, pos + len("public"))
        meta = _word(text, pos, "meta")
        if meta:
            pos = _skip(text, pos + len("meta"))
        if not _word(text, pos, "import"):
            # `public section` and `meta def` are commands, not imports.
            pos = start
            break
        if (public or meta) and not has_module:
            raise ValueError("Lean public/meta import requires a module header")
        pos = _skip(text, pos + len("import"))
        all_import = _word(text, pos, "all")
        if all_import:
            if not has_module or public:
                raise ValueError("Invalid Lean import all qualifier")
            pos = _skip(text, pos + len("all"))
        match = MODULE_NAME.match(text, pos)
        if match is None:
            raise ValueError("Unsupported Lean import module syntax")
        module = match.group()
        pos = match.end()
        if (pos < len(text) and not text[pos].isspace() and
                not text.startswith("--", pos) and
                not text.startswith("/-", pos)):
            raise ValueError(f"Unsupported token after Lean import {module}")
        imports.append(module)
        pos = _skip(text, pos)
    return imports
