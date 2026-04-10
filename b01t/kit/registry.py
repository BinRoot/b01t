"""In-memory registry of packages: save, load, and resolve dependencies."""

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from b01t.core.types import DSLValidationError, IRProgram
from b01t.core.exact_types import ExactProgram
from .ir import dump_ir


@dataclass
class PackageMeta:
    name: str
    effect: str
    safe: bool
    tags: list[str] = field(default_factory=list)
    docs: str = ""
    ir: Optional[IRProgram] = None
    inputs: list[tuple[str, int]] = field(default_factory=list)
    version: str = "0.1.0"
    depends_on: list[str] = field(default_factory=list)
    exact_program: Optional[ExactProgram] = None
    artifact_format: Optional[str] = None


class PackageRegistry:
    def __init__(self):
        self._items: dict[str, PackageMeta] = {}

    def publish(self, meta: PackageMeta) -> None:
        self._items[meta.name] = meta

    def find_by_tag(self, tag: str) -> list[PackageMeta]:
        return [m for m in self._items.values() if tag in m.tags]

    def get(self, name: str) -> Optional[PackageMeta]:
        return self._items.get(name)

    def all(self) -> list[PackageMeta]:
        return list(self._items.values())

    def save(self, path: str | Path) -> None:
        from b01t.core.exact_serde import exact_program_to_dict
        data = []
        for m in self._items.values():
            entry: dict[str, Any] = {
                "name": m.name, "effect": m.effect, "safe": m.safe,
                "tags": m.tags, "docs": m.docs, "inputs": m.inputs,
                "version": m.version, "depends_on": m.depends_on,
            }
            if m.ir is not None:
                entry["ir_dump"] = dump_ir(m.ir)
            if m.exact_program is not None:
                entry["exact_oracle"] = exact_program_to_dict(m.exact_program)
                entry["artifact_format"] = "exact-oracle-v1"
            elif m.artifact_format is not None:
                entry["artifact_format"] = m.artifact_format
            data.append(entry)
        Path(path).write_text(json.dumps(data, indent=2))

    def load(self, path: str | Path) -> None:
        from b01t.core.exact_serde import exact_program_from_dict
        data = json.loads(Path(path).read_text())
        for entry in data:
            exact_prog = None
            if "exact_oracle" in entry:
                exact_prog = exact_program_from_dict(entry["exact_oracle"])
            self._items[entry["name"]] = PackageMeta(
                name=entry["name"], effect=entry["effect"], safe=entry["safe"],
                tags=entry.get("tags", []), docs=entry.get("docs", ""),
                inputs=entry.get("inputs", []), version=entry.get("version", "0.1.0"),
                depends_on=entry.get("depends_on", []),
                exact_program=exact_prog,
                artifact_format=entry.get("artifact_format"),
            )

    def resolve(self, name: str) -> list[PackageMeta]:
        """Topological sort of transitive dependencies."""
        visited: set[str] = set()
        order: list[PackageMeta] = []
        in_progress: set[str] = set()

        def visit(n: str):
            if n in visited:
                return
            if n in in_progress:
                raise DSLValidationError(f"circular dependency: {n}")
            in_progress.add(n)
            meta = self._items.get(n)
            if meta is None:
                raise DSLValidationError(f"missing dependency: {n}")
            for dep in meta.depends_on:
                visit(dep)
            in_progress.discard(n)
            visited.add(n)
            order.append(meta)

        visit(name)
        return order

    def dependency_graph_dot(self) -> str:
        lines = ["digraph packages {", "  rankdir=BT;"]
        for m in self._items.values():
            lines.append(f'  "{m.name}" [label="{m.name}\\n[{m.effect}]"];')
            for dep in m.depends_on:
                lines.append(f'  "{m.name}" -> "{dep}";')
        lines.append("}")
        return "\n".join(lines)


DEFAULT_REGISTRY = PackageRegistry()
