"""Apply the read-once obstruction to advertised monotone bipartite upper bounds."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re


TITLE = re.compile(
    r"(?:One-a-side promise: the |Table 1a, )([0-9]{1,2}) by ([0-9]{1,2})"
    r"[^:]{0,65}[:,]?[ ]*(?:with )?mask ([0-9]{1,45}).{0,110}"
    r"(?:AND/OR circuit of fan-in two|fan-in-two AND/OR circuit) (?:with|of) at most ([0-9]{1,3}) gates"
)


def necessary_lines(lines: list[set[int]]) -> list[int]:
    return [i for i, line in enumerate(lines) if any(line - other for other in lines)]


def induced_path(rows: list[set[int]], cols: list[set[int]]) -> tuple[int, int, int, int] | None:
    """Find an edge path a-c-b with a-d also present and b-d absent."""
    regular_cols = {j for j, column in enumerate(cols) if len(column) != len(rows)}
    for a, row_a in enumerate(rows):
        if len(row_a) == len(cols):
            continue
        for b, row_b in enumerate(rows):
            shared = row_a & row_b & regular_cols
            missing = row_a - row_b
            if shared and missing:
                return a, b, min(shared), min(missing)
    return None


def screen(n: int, m: int, mask: int, budget: int) -> dict | None:
    rows = [{j for j in range(m) if mask & (1 << (m * i + j))} for i in range(n)]
    cols = [{i for i in range(n) if j in rows[i]} for j in range(m)]
    essential_rows = necessary_lines(rows)
    essential_cols = necessary_lines(cols)
    count = len(essential_rows) + len(essential_cols)
    obstruction = None
    if budget + 1 < count:
        obstruction = {"reason": "required_inputs"}
    elif budget + 1 == count:
        path = induced_path(rows, cols)
        if path is not None:
            obstruction = {"reason": "induced_path", "path": path}
    if obstruction is not None:
        obstruction.update(
            rows=n, cols=m, mask=mask, budget=budget,
            necessary_rows=essential_rows, necessary_columns=essential_cols,
        )
    return obstruction


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("board", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    board = json.loads(args.board.read_bytes())
    certificates = []
    applicable = 0
    for gap in board["gaps"]:
        if not gap.get("offerable") or gap.get("held") or gap.get("kind") != "prove":
            continue
        title = gap.get("title")
        if not isinstance(title, str) or len(title) > 350:
            continue
        match = TITLE.fullmatch(title)
        if match is None or not re.fullmatch(r"L-meta-[0-9]{1,9}", gap["id"]):
            continue
        n, m, mask, budget = map(int, match.groups())
        if not n or not m or mask >= 1 << (n * m):
            continue
        applicable += 1
        obstruction = screen(n, m, mask, budget)
        if obstruction is not None:
            certificates.append({"unit": gap["id"], **obstruction})
    provenance = {"board_time": board["updated_at"], "titles_tested": applicable, "obstructions": certificates}
    print(f"{board['updated_at']}: {len(certificates)} of {applicable} advertised bounds obstructed")
    if args.output:
        args.output.write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
