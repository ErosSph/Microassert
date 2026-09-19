"""pyslang-backed RTL parsing and a compact, serializable structural view."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from pathlib import Path
import hashlib
import re
from typing import Any

try:
    import pyslang
except ImportError as exc:  # pragma: no cover - exercised by CLI error path
    raise RuntimeError("pyslang is required; run this project in the conda 'lhq' environment") from exc

from dateassertion.ir.schema import AssignmentInfo, SignalInfo, dump_json


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")
SV_KEYWORDS = {
    "always", "and", "assign", "begin", "case", "default", "else", "end", "endcase",
    "for", "if", "logic", "or", "reg", "wire", "posedge", "negedge", "signed",
}


def _strip_sv_comments(text: str) -> str:
    """Remove comment trivia without changing quoted string contents."""

    output: list[str] = []
    index = 0
    in_string = False
    while index < len(text):
        char = text[index]
        if in_string:
            output.append(char)
            if char == "\\" and index + 1 < len(text):
                index += 1
                output.append(text[index])
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            output.append(char)
            index += 1
            continue
        if text.startswith("//", index):
            newline = text.find("\n", index + 2)
            if newline < 0:
                break
            output.append(" ")
            index = newline + 1
            continue
        if text.startswith("/*", index):
            end = text.find("*/", index + 2)
            output.append(" ")
            index = len(text) if end < 0 else end + 2
            continue
        output.append(char)
        index += 1
    return "".join(output)


def _canonical_syntax_text(node: Any, data: bytes | None = None) -> str:
    """Return preprocessed, comment-free text for a pyslang syntax node."""

    try:
        rendered = str(node)
    except UnicodeDecodeError:
        if data is None:
            raise
        rendered = _slice(data, node)
    text = " ".join(_strip_sv_comments(rendered).split())
    text = re.sub(r"\s+([,}\]\)])", r"\1", text)
    text = re.sub(r"([{\[(])\s+", r"\1", text)
    return text


@dataclass
class CaseInfo:
    selector: str
    labels: list[str]
    file: str
    line_start: int
    line_end: int
    snippet: str
    module: str


@dataclass
class ModuleInfo:
    name: str
    file: str
    line_start: int
    line_end: int
    instances: list[dict[str, str]] = field(default_factory=list)


@dataclass
class AlwaysInfo:
    kind: str
    event_control: str
    file: str
    line_start: int
    line_end: int
    module: str
    assigned_signals: list[str] = field(default_factory=list)


@dataclass
class RTLDesign:
    files: list[str]
    modules: list[ModuleInfo]
    signals: dict[str, SignalInfo]
    module_signals: dict[str, dict[str, SignalInfo]]
    always_blocks: list[AlwaysInfo]
    assignments: list[AssignmentInfo]
    cases: list[CaseInfo]
    diagnostics: list[dict[str, Any]]
    source_digest: str
    macros: dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "files": self.files,
            "modules": [asdict(item) for item in self.modules],
            "signals": {name: asdict(item) for name, item in self.signals.items()},
            "module_signals": {
                module: {name: asdict(item) for name, item in entries.items()}
                for module, entries in self.module_signals.items()
            },
            "always_blocks": [asdict(item) for item in self.always_blocks],
            "assignments": [asdict(item) for item in self.assignments],
            "cases": [asdict(item) for item in self.cases],
            "diagnostics": self.diagnostics,
            "source_digest": self.source_digest,
            "macros": self.macros,
        }

    def save(self, path: str | Path) -> None:
        dump_json(path, self.to_dict())

    @classmethod
    def load(cls, path: str | Path) -> "RTLDesign":
        import json

        raw = json.loads(Path(path).read_text(encoding="utf-8"))
        flat_signals = {name: SignalInfo(**item) for name, item in raw["signals"].items()}
        module_signals = {
            module: {name: SignalInfo(**item) for name, item in entries.items()}
            for module, entries in raw.get("module_signals", {}).items()
        }
        if not module_signals:
            for name, signal in flat_signals.items():
                module_signals.setdefault(signal.module, {})[name] = signal
        return cls(
            files=raw["files"],
            modules=[ModuleInfo(**item) for item in raw["modules"]],
            signals=flat_signals,
            module_signals=module_signals,
            always_blocks=[AlwaysInfo(**item) for item in raw.get("always_blocks", [])],
            assignments=[AssignmentInfo(**item) for item in raw["assignments"]],
            cases=[CaseInfo(**item) for item in raw["cases"]],
            diagnostics=raw["diagnostics"],
            source_digest=raw["source_digest"],
            macros=raw.get("macros", {}),
        )


def discover_rtl_files(inputs: list[str | Path]) -> list[Path]:
    result: list[Path] = []
    for value in inputs:
        path = Path(value).expanduser().resolve()
        if path.is_dir():
            result.extend(sorted(item for item in path.rglob("*") if item.suffix.lower() in {".v", ".sv"}))
        elif path.suffix.lower() in {".v", ".sv"} and path.is_file():
            result.append(path)
        else:
            raise FileNotFoundError(f"RTL input not found or unsupported: {path}")
    unique = list(dict.fromkeys(result))
    if not unique:
        raise FileNotFoundError("no Verilog/SystemVerilog files discovered")
    return unique


def _offset(node: Any) -> tuple[int, int]:
    return int(node.sourceRange.start.offset), int(node.sourceRange.end.offset)


def _slice(data: bytes, node: Any) -> str:
    start, end = _offset(node)
    return data[start : end + 1].decode("utf-8", errors="replace")


def _line(data: bytes, offset: int) -> int:
    return data.count(b"\n", 0, offset) + 1


def _module_for_offset(modules: list[ModuleInfo], file: str, offset_line: int) -> str:
    for module in modules:
        if module.file == file and module.line_start <= offset_line <= module.line_end:
            return module.name
    return ""


def _split_top_level_commas(text: str) -> list[str]:
    """Split a declaration list without mistaking expression commas for declarators.

    A declaration initializer may legally contain concatenations, function
    arguments, or indexed expressions.  Only commas at the declaration's
    outermost level separate declarators.
    """

    parts: list[str] = []
    start = 0
    stack: list[str] = []
    closing = {")": "(", "]": "[", "}": "{"}
    in_string = False
    escaped = False
    for index, char in enumerate(text):
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char in "([{":
            stack.append(char)
        elif char in ")]}":
            if stack and stack[-1] == closing[char]:
                stack.pop()
        elif char == "," and not stack:
            parts.append(text[start:index])
            start = index + 1
    parts.append(text[start:])
    return parts


def _declaration_signals(text: str, file: str, module: str, base_line: int) -> dict[str, SignalInfo]:
    """Extract declaration names after pyslang has established valid syntax boundaries."""
    signals: dict[str, SignalInfo] = {}
    declaration = re.compile(
        r"(?ms)^\s*(input|output|inout|wire|reg|logic)\b\s*"
        r"(?:(wire|reg|logic)\b\s*)?(signed\b\s*)?(\[[^\]]+\]\s*)?([^;]+);"
    )
    for match in declaration.finditer(text):
        direction_or_kind, explicit_kind, _signed, width, names_text = match.groups()
        # Module headers can put another direction in the same semicolon-delimited match.
        if re.search(r"\b(input|output|inout)\b", names_text):
            continue
        direction = direction_or_kind if direction_or_kind in {"input", "output", "inout"} else "internal"
        kind = explicit_kind or (direction_or_kind if direction == "internal" else "logic")
        for entry in _split_top_level_commas(names_text):
            entry = entry.split("=")[0].strip()
            names = IDENT.findall(entry)
            if not names:
                continue
            name = names[0]
            if name in SV_KEYWORDS:
                continue
            signal_kind = (
                f"{kind}_array"
                if re.search(rf"\b{re.escape(name)}\b\s*\[", entry)
                else kind
            )
            line = base_line + text.count("\n", 0, match.start())
            signals[name] = SignalInfo(
                name=name,
                width=(width or "").strip(),
                direction=direction,
                kind=signal_kind,
                module=module,
                file=file,
                line=line,
            )

    # ANSI ports end in commas, so parse them line-by-line as a supplement.
    port_line = re.compile(r"^\s*(input|output|inout)\s+(.*)")
    for index, line_text in enumerate(text.splitlines(), start=base_line):
        match = port_line.match(line_text.split("//", 1)[0])
        if not match:
            continue
        direction, body = match.groups()
        body = body.split("input", 1)[0].split("output", 1)[0].split("inout", 1)[0]
        kind_match = re.search(r"\b(wire|reg|logic)\b", body)
        width_match = re.search(r"\[[^\]]+\]", body)
        clean = re.sub(r"\b(?:wire|reg|logic|signed)\b|\[[^\]]+\]", " ", body)
        for entry in clean.split(","):
            names = IDENT.findall(entry)
            if not names:
                continue
            name = names[-1]
            signals[name] = SignalInfo(
                name=name,
                width=width_match.group(0) if width_match else "",
                direction=direction,
                kind=kind_match.group(1) if kind_match else "logic",
                module=module,
                file=file,
                line=index,
            )
    # Parameters and localparams are valid identifiers in grounded path
    # conditions (feature switches, FSM labels, opcode constants).  They are
    # not runtime signals, but must be part of the module symbol table so the
    # fixed primitive binder does not mistake them for cross-module names.
    parameter_re = re.compile(
        r"(?m)\b(parameter|localparam)\b\s*"
        r"(?:(?:integer|int|bit|logic|reg|wire|signed|unsigned)\b\s*)?"
        r"(\[[^\]]+\]\s*)?([A-Za-z_][A-Za-z0-9_$]*)\s*="
    )
    for match in parameter_re.finditer(text):
        kind, width, name = match.groups()
        signals.setdefault(name, SignalInfo(
            name=name,
            width=(width or "").strip(),
            direction="constant",
            kind=kind,
            module=module,
            file=file,
            line=base_line + text.count("\n", 0, match.start()),
        ))
    for block in re.finditer(r"(?ms)\b(localparam|parameter)\b([^;]+);", text):
        kind, body = block.groups()
        width_match = re.search(r"\[[^\]]+\]", body)
        for entry in body.split(","):
            name_match = re.search(r"([A-Za-z_][A-Za-z0-9_$]*)\s*=", entry)
            if not name_match:
                continue
            name = name_match.group(1)
            signals.setdefault(name, SignalInfo(
                name=name,
                width=width_match.group(0) if width_match else "",
                direction="constant",
                kind=kind,
                module=module,
                file=file,
                line=base_line + text.count("\n", 0, block.start()),
            ))
    return signals


def _dependencies(rhs: str) -> list[str]:
    without_literals = re.sub(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+", " ", rhs)
    return sorted({name for name in IDENT.findall(without_literals) if name.lower() not in SV_KEYWORDS and not name[0].isdigit()})


def _contains(container: Any, child: Any) -> bool:
    """Return whether ``child`` is textually contained by ``container``."""
    if container is None or child is None:
        return False
    c_start, c_end = _offset(container)
    n_start, n_end = _offset(child)
    return c_start <= n_start and n_end <= c_end


def _compact_node(node: Any, data: bytes) -> str:
    # ``str`` renders the syntax node without the following delimiter token;
    # slicing a pyslang source range for predicates/case labels can include the
    # closing parenthesis or colon owned by the parent node.
    try:
        text = str(node)
    except UnicodeDecodeError:
        # Some pyslang builds attempt to decode preceding non-ASCII comment
        # trivia while rendering a node.  The source slice is byte-safe; trim
        # only delimiters known to belong to the parent syntax node.
        text = _slice(data, node).strip()
        if text.endswith(":"):
            text = text[:-1]
        while text.endswith(")") and text.count(")") > text.count("("):
            text = text[:-1]
    return " ".join(_strip_sv_comments(text).split())


def _case_condition(item: Any, case_node: Any, data: bytes) -> str:
    selector = _compact_node(case_node.expr, data)
    kind = str(item.kind)
    if kind.endswith("DefaultCaseItem"):
        previous: list[str] = []
        for candidate in case_node.items:
            if candidate is item:
                break
            for expression in getattr(candidate, "expressions", []):
                label = _compact_node(expression, data)
                if re.search(r"[A-Za-z0-9_`']", label):
                    previous.append(label)
        return " && ".join(f"({selector} !=? {label})" for label in previous) or "1'b1"
    labels = [
        label for expression in getattr(item, "expressions", [])
        if (label := _compact_node(expression, data)) and re.search(r"[A-Za-z0-9_`']", label)
    ]
    return " || ".join(f"({selector} ==? {label})" for label in labels)


def _guard(node: Any, data: bytes) -> str:
    """Recover the complete syntactic path condition for an assignment.

    In addition to nested ``if`` predicates this includes the negation of
    every enclosing else/else-if predecessor and each enclosing case item.
    This is intentionally syntax based: it is deterministic, auditable, and
    does not pretend to be a symbolic executor.
    """
    terms: list[str] = []
    parent = getattr(node, "parent", None)
    for _ in range(64):
        if parent is None:
            break
        kind = str(parent.kind)
        if kind.endswith("ConditionalStatement"):
            predicate = _compact_node(parent.predicate, data)
            # In some pyslang syntax shapes ``statement`` spans the complete
            # conditional text, including its else clause.  Check the more
            # specific else subtree first or an else assignment can inherit
            # the positive predicate (notably turning normal reset-else RTL
            # into reset-only behavior).
            if getattr(parent, "elseClause", None) is not None and _contains(parent.elseClause.clause, node):
                terms.append(f"!({predicate})")
            elif _contains(parent.statement, node):
                terms.append(f"({predicate})")
        elif kind.endswith("StandardCaseItem") or kind.endswith("DefaultCaseItem"):
            case_node = getattr(parent, "parent", None)
            if case_node is not None and str(case_node.kind).endswith("CaseStatement"):
                condition = _case_condition(parent, case_node, data)
                if condition:
                    terms.append(f"({condition})")
        parent = getattr(parent, "parent", None)
    return " && ".join(reversed(terms))


def _assignment_kind(node: Any, default: str) -> str:
    parent = getattr(node, "parent", None)
    for _ in range(12):
        if parent is None:
            break
        if str(parent.kind).endswith("ContinuousAssign"):
            return "continuous"
        parent = getattr(parent, "parent", None)
    return default


def _assignment_is_module_behavior(node: Any) -> bool:
    """Exclude generate-loop controls and other non-behavioral ``=`` nodes."""

    parent = getattr(node, "parent", None)
    for _ in range(64):
        if parent is None:
            return False
        kind = str(parent.kind)
        if kind.endswith("ContinuousAssign") or kind.endswith((
            "AlwaysBlock", "AlwaysCombBlock", "AlwaysFFBlock", "AlwaysLatchBlock",
        )):
            return True
        if kind.endswith("ModuleDeclaration"):
            return False
        parent = getattr(parent, "parent", None)
    return False


def _supplement_declarator_signals(
    tree: Any, data: bytes, path: Path, modules: list[ModuleInfo],
    module_signals: dict[str, dict[str, SignalInfo]], node_filter: Any | None = None,
    declarator_nodes: list[Any] | None = None,
) -> None:
    """Recover identifiers that regex extraction loses on unpacked arrays."""

    declarators = declarator_nodes if declarator_nodes is not None else []
    if declarator_nodes is None:
        tree.root.visit(lookup_table={
            pyslang.syntax.SyntaxKind.Declarator: lambda node: declarators.append(node),
        })
    for node in declarators:
        if node_filter is not None and not node_filter(node):
            continue
        name = str(getattr(getattr(node, "name", None), "valueText", "")).strip()
        if not name:
            continue
        start, _ = _offset(node)
        line_no = _line(data, start)
        module = _module_for_offset(modules, str(path), line_no)
        if not module:
            continue
        table = module_signals.setdefault(module, {})
        dimensions = [_canonical_syntax_text(dimension, data) for dimension in node.dimensions]
        # Syntax Declarator dimensions are authoritative.  A regex pass can
        # otherwise mistake a comma inside an initializer (for example a
        # concatenation containing ``signal[index]``) for a second declarator.
        unpacked = bool(dimensions)
        if name in table:
            if unpacked and not table[name].kind.endswith("_array"):
                table[name].kind += "_array"
            if unpacked:
                table[name].unpacked_dimensions = dimensions
            elif table[name].kind.endswith("_array"):
                table[name].kind = table[name].kind.removesuffix("_array")
                table[name].unpacked_dimensions = []
            continue
        parent_text = _canonical_syntax_text(getattr(node, "parent", node), data)
        kind_match = re.search(r"\b(wire|reg|logic|integer|genvar)\b", parent_text)
        width_match = re.search(r"\[[^\]]+\]", parent_text)
        direction_match = re.search(r"\b(input|output|inout)\b", parent_text)
        base_kind = kind_match.group(1) if kind_match else "logic"
        table[name] = SignalInfo(
            name=name,
            width=width_match.group(0) if width_match else "",
            direction=direction_match.group(1) if direction_match else "internal",
            kind=f"{base_kind}_array" if unpacked else base_kind,
            module=module,
            file=str(path),
            line=line_no,
            unpacked_dimensions=dimensions if unpacked else [],
        )


def _inherit_ansi_ports(node: Any, data: bytes, table: dict[str, SignalInfo]) -> None:
    """ANSI comma continuations inherit direction and packed type, not scalar defaults."""
    ports = getattr(node.header, "ports", None)
    if ports is None or not str(ports.kind).endswith("AnsiPortList"):
        return
    direction, width, base_kind = "", "", "logic"
    for port in ports.ports:
        declarator = getattr(port, "declarator", None)
        header = getattr(port, "header", None)
        if declarator is None or header is None:
            continue
        explicit_direction = str(getattr(getattr(header, "direction", None), "valueText", ""))
        dtype = getattr(header, "dataType", None)
        type_text = _canonical_syntax_text(dtype, data) if dtype is not None else ""
        if explicit_direction in {"input", "output", "inout", "ref"}:
            direction = explicit_direction
            width, base_kind = "", "logic"
        if type_text.strip():
            dimensions = re.findall(r"\[[^\]]+\]", type_text)
            width = "".join(dimensions)
            type_match = re.search(r"\b(wire|reg|logic|bit|integer|int)\b", type_text)
            base_kind = type_match.group(1) if type_match else "logic"
        signal = table.get(declarator.name.valueText)
        if signal is not None and direction:
            signal.direction, signal.width = direction, width
            signal.kind = base_kind + ("_array" if signal.kind.endswith("_array") else "")


def parse_rtl(
    inputs: list[str | Path], *, include_dirs: list[str | Path] | None = None
) -> RTLDesign:
    files = discover_rtl_files(inputs)
    modules: list[ModuleInfo] = []
    assignments: list[AssignmentInfo] = []
    always_blocks: list[AlwaysInfo] = []
    cases: list[CaseInfo] = []
    signals: dict[str, SignalInfo] = {}
    module_signals: dict[str, dict[str, SignalInfo]] = {}
    diagnostics: list[dict[str, Any]] = []
    macros: dict[str, str] = {}
    digest = hashlib.sha256()
    # Parse an ordered file list as *one Verilog compilation unit*.  Parsing
    # each source file in isolation loses legal macro definitions introduced
    # by an earlier file (for example, a conventional ``*_defs.v`` preceding
    # a module that uses its constants).  ``fromFiles`` uses pyslang's actual
    # preprocessor semantics for ordered ``define`` / ``undef`` / conditional
    # / include handling.  Its SourceManager still preserves the original
    # source buffer for every syntax node, so evidence locations remain in
    # the upstream file rather than a synthetic concatenation.
    source_manager = pyslang.SourceManager()
    preprocessor = pyslang.parsing.PreprocessorOptions()
    preprocessor.additionalIncludePaths = [
        str(Path(item).expanduser().resolve()) for item in include_dirs or []
    ]
    syntax_options = pyslang.Bag()
    syntax_options.preprocessorOptions = preprocessor

    # Pyslang preprocesses executable expressions, but declaration widths are
    # intentionally retained as source text.  Include-header macros are needed
    # to give both representations the same stable width identity.
    macro_sources = list(files)
    for include_dir in include_dirs or []:
        directory = Path(include_dir).expanduser().resolve()
        if directory.is_dir():
            macro_sources.extend(sorted(
                item for item in directory.rglob("*")
                if item.suffix.lower() in {".v", ".sv", ".vh", ".svh"}
            ))
    for macro_path in dict.fromkeys(macro_sources):
        source_text = macro_path.read_text(encoding="utf-8", errors="replace")
        for match in re.finditer(
            r"(?m)^[ \t]*`define[ \t]+([A-Za-z_][A-Za-z0-9_$]*)"
            r"(?![A-Za-z0-9_$]|[ \t]*\()[ \t]+([^\r\n/]+)",
            source_text,
        ):
            value = match.group(2).strip()
            if value:
                macros[match.group(1)] = value

    file_data: dict[Path, bytes] = {}
    for path in files:
        data = path.read_bytes()
        file_data[path] = data
        digest.update(data)
    tree = pyslang.syntax.SyntaxTree.fromFiles(
        [str(path) for path in files], source_manager, syntax_options,
    )
    file_set = set(files)
    buffer_paths: dict[Any, Path] = {}

    def node_path(node: Any) -> Path | None:
        """Return a node's physical source path after preprocessing."""

        try:
            buffer = node.sourceRange.start.buffer
            if buffer not in buffer_paths:
                buffer_paths[buffer] = Path(source_manager.getFullPath(buffer)).resolve()
            return buffer_paths[buffer]
        except Exception:
            return None

    for diagnostic in tree.diagnostics:
        try:
            location = source_manager.getFullyOriginalLoc(diagnostic.location)
            diagnostic_path = str(Path(source_manager.getFullPath(location.buffer)).resolve())
        except Exception:
            diagnostic_path = "<compilation-unit>"
        diagnostics.append(
            {
                "file": diagnostic_path,
                "code": str(diagnostic.code),
                "severity": str(getattr(diagnostic, "severity", "unknown")),
            }
        )

    # Walking a full compilation unit once is materially cheaper than walking
    # it once per source file.  More importantly, these buckets retain the
    # original source-buffer ownership required by the evidence model.
    def buckets() -> dict[Path, list[Any]]:
        return {path: [] for path in files}

    module_nodes_by_path = buckets()
    declarators_by_path = buckets()
    parameter_nodes_by_path = buckets()
    assignment_nodes_by_path: dict[Path, list[tuple[Any, str]]] = {
        path: [] for path in files
    }
    net_nodes_by_path = buckets()
    always_nodes_by_path: dict[Path, list[tuple[Any, str]]] = {
        path: [] for path in files
    }
    case_nodes_by_path = buckets()

    def append_node(target: dict[Path, list[Any]], node: Any) -> None:
        path = node_path(node)
        if path in file_set:
            target[path].append(node)

    assignment_kinds = {
        pyslang.syntax.SyntaxKind.NonblockingAssignmentExpression: "nonblocking",
        pyslang.syntax.SyntaxKind.AssignmentExpression: "blocking",
    }
    always_kinds = {
        pyslang.syntax.SyntaxKind.AlwaysBlock: "always",
        pyslang.syntax.SyntaxKind.AlwaysCombBlock: "always_comb",
        pyslang.syntax.SyntaxKind.AlwaysFFBlock: "always_ff",
        pyslang.syntax.SyntaxKind.AlwaysLatchBlock: "always_latch",
    }
    tree.root.visit(lookup_table={
        pyslang.syntax.SyntaxKind.ModuleDeclaration:
        lambda node: append_node(module_nodes_by_path, node),
        pyslang.syntax.SyntaxKind.Declarator:
        lambda node: append_node(declarators_by_path, node),
        pyslang.syntax.SyntaxKind.ParameterDeclaration:
        lambda node: append_node(parameter_nodes_by_path, node),
        pyslang.syntax.SyntaxKind.NetDeclaration:
        lambda node: append_node(net_nodes_by_path, node),
        pyslang.syntax.SyntaxKind.CaseStatement:
        lambda node: append_node(case_nodes_by_path, node),
        **{
            kind: (lambda node, label=label: assignment_nodes_by_path[node_path(node)].append((node, label))
                   if node_path(node) in file_set else None)
            for kind, label in assignment_kinds.items()
        },
        **{
            kind: (lambda node, label=label: always_nodes_by_path[node_path(node)].append((node, label))
                   if node_path(node) in file_set else None)
            for kind, label in always_kinds.items()
        },
    })

    for path in files:
        data = file_data[path]
        source_text = data.decode("utf-8", errors="replace")
        in_path = lambda node, current=path: node_path(node) == current

        module_nodes = module_nodes_by_path[path]
        for node in module_nodes:
            start, end = _offset(node)
            module_text = data[start : end + 1].decode("utf-8", errors="replace")
            name = node.header.name.valueText
            module = ModuleInfo(
                name=name,
                file=str(path),
                line_start=_line(data, start),
                line_end=_line(data, end),
            )
            # Only obvious named instantiations are needed for the hierarchy summary.
            inst_re = re.compile(r"(?m)^\s*([A-Za-z_][\w$]*)\s+(?:#\s*\([^;]*?\)\s*)?([A-Za-z_][\w$]*)\s*\(")
            for match in inst_re.finditer(module_text):
                if match.group(1) not in {"if", "for", "while", "case", "module", "function", "task"}:
                    module.instances.append({"module": match.group(1), "instance": match.group(2)})
            modules.append(module)
            declared = _declaration_signals(module_text, str(path), name, module.line_start)
            module_signals.setdefault(name, {}).update(declared)
            for signal_name, signal in declared.items():
                # Unqualified names are sufficient for a selected top. Preserve the
                # first declaration instead of silently replacing it in later modules.
                signals.setdefault(signal_name, signal)

        _supplement_declarator_signals(
            tree, data, path, modules, module_signals, node_filter=in_path,
            declarator_nodes=declarators_by_path[path],
        )
        for node in module_nodes:
            _inherit_ansi_ports(node, data, module_signals[node.header.name.valueText])

        # Preserve literal localparam evidence for attributed graph motifs.
        # Do not evaluate overrideable parameter defaults as design constants.
        def capture_localparam(node):
            if not in_path(node):
                return
            if node.keyword.valueText != "localparam":
                return
            start, _ = _offset(node)
            owner = _module_for_offset(modules, str(path), _line(data, start))
            for declarator in node.declarators:
                if not hasattr(declarator, "name") or not declarator.initializer:
                    continue
                symbol = module_signals.get(owner, {}).get(declarator.name.valueText)
                if symbol is not None:
                    symbol.constant_expression = _canonical_syntax_text(declarator.initializer.expr, data)
        for node in parameter_nodes_by_path[path]:
            capture_localparam(node)

        for node, kind in assignment_nodes_by_path[path]:
            if not _assignment_is_module_behavior(node):
                continue
            kind = _assignment_kind(node, kind)
            left = _canonical_syntax_text(node.left, data)
            right = _canonical_syntax_text(node.right, data).rstrip(";").strip()
            match = re.fullmatch(r"([A-Za-z_][\w$]*)(?:\s*\[[^\]]+\])*", left)
            if not match or not right:
                continue
            lhs = match.group(1)
            rhs = right
            start, _ = _offset(node)
            line_no = _line(data, start)
            module_name = _module_for_offset(modules, str(path), line_no)
            assignments.append(
                AssignmentInfo(
                    lhs=lhs,
                    rhs=rhs,
                    kind=kind,
                    guard=_guard(node, data),
                    module=module_name,
                    file=str(path),
                    line=line_no,
                    dependencies=_dependencies(rhs),
                    lhs_expression=left,
                )
            )

        # A net declaration initializer is a continuous driver, unlike a
        # variable initializer (one-time initialization). Preserve this real
        # producer so selected ALU result cones do not stop at a wire name.
        def capture_net_initializers(node):
            if not in_path(node):
                return
            parent = getattr(node, "parent", None)
            while parent is not None:
                if str(parent.kind).endswith(("FunctionDeclaration", "TaskDeclaration")):
                    return
                parent = getattr(parent, "parent", None)
            for declarator in node.declarators:
                if not getattr(declarator, "initializer", None):
                    continue
                line_no = _line(data, _offset(declarator)[0])
                owner = _module_for_offset(modules, str(path), line_no)
                rhs = _canonical_syntax_text(declarator.initializer.expr, data)
                assignments.append(AssignmentInfo(
                    lhs=declarator.name.valueText, rhs=rhs, kind="continuous", guard="",
                    module=owner, file=str(path), line=line_no, dependencies=_dependencies(rhs)))
        for node in net_nodes_by_path[path]:
            capture_net_initializers(node)

        for node, kind in always_nodes_by_path[path]:
            snippet = _slice(data, node)
            start, end = _offset(node)
            line_start = _line(data, start)
            line_end = _line(data, end)
            event_match = re.search(r"@\s*\((.*?)\)", snippet, re.S)
            module_name = _module_for_offset(modules, str(path), line_start)
            assigned = sorted(
                {
                    item.lhs
                    for item in assignments
                    if item.file == str(path)
                    and item.module == module_name
                    and line_start <= item.line <= line_end
                }
            )
            always_blocks.append(
                AlwaysInfo(
                    kind=kind,
                    event_control=" ".join(event_match.group(1).split()) if event_match else "implicit",
                    file=str(path),
                    line_start=line_start,
                    line_end=line_end,
                    module=module_name,
                    assigned_signals=assigned,
                )
            )

        for node in case_nodes_by_path[path]:
            snippet = _slice(data, node)
            selector_match = re.search(r"\bcase[xz]?\s*\((.*?)\)", snippet, re.S)
            if not selector_match:
                continue
            labels: list[str] = []
            for label_group in re.findall(r"(?m)^\s*([^:\n]+?)\s*:", snippet):
                for label in label_group.split(","):
                    label = label.strip()
                    if re.fullmatch(r"`[A-Za-z_][\w$]*|[A-Za-z_][\w$]*|\d+'[bBdDhHoO][0-9a-fA-FxXzZ_]+", label):
                        if label.lower() != "default":
                            labels.append(label)
            start, end = _offset(node)
            line_start = _line(data, start)
            cases.append(
                CaseInfo(
                    selector=" ".join(selector_match.group(1).split()),
                    labels=list(dict.fromkeys(labels)),
                    file=str(path),
                    line_start=line_start,
                    line_end=_line(data, end),
                    snippet=snippet[:12000],
                    module=_module_for_offset(modules, str(path), line_start),
                )
            )

    # Verilog permits implicit nets.  A continuous-assignment target accepted
    # by the parser is still a stable module symbol even when no explicit wire
    # declaration was written.
    for assignment in assignments:
        module_table = module_signals.setdefault(assignment.module, {})
        if assignment.lhs not in module_table and assignment.kind == "continuous":
            module_table[assignment.lhs] = SignalInfo(
                name=assignment.lhs,
                width="",
                direction="internal",
                kind="implicit_wire",
                module=assignment.module,
                file=assignment.file,
                line=assignment.line,
            )

    # Refresh the legacy unqualified view after syntax-backed supplements.
    for module in modules:
        for signal_name, signal in module_signals.get(module.name, {}).items():
            signals.setdefault(signal_name, signal)

    return RTLDesign(
        files=[str(path) for path in files],
        modules=modules,
        signals=signals,
        module_signals=module_signals,
        always_blocks=always_blocks,
        assignments=assignments,
        cases=cases,
        diagnostics=diagnostics,
        source_digest=digest.hexdigest(),
        macros=macros,
    )
