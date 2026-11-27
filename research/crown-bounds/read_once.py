"""Search binary AND/OR formulas on the one-vertex-per-side promise."""

from __future__ import annotations

import argparse
from collections.abc import Iterator
from typing import NamedTuple, Union


class Gate(NamedTuple):
    op: str
    left: "Formula"
    right: "Formula"


class Not(NamedTuple):
    operand: "Formula"


Formula = Union[int, Gate, Not]


def bipartite_inputs(rows: int, cols: int) -> list[int]:
    return [
        sum(1 << (cols * row + col) for col in range(cols))
        for row in range(rows)
    ] + [
        sum(1 << (cols * row + col) for row in range(rows))
        for col in range(cols)
    ]


def partitions(subset: int) -> Iterator[tuple[int, int]]:
    anchor = subset & -subset
    left = (subset - 1) & subset
    while left:
        if left & anchor:
            yield left, subset ^ left
        left = (left - 1) & subset


def candidates(tables: dict[int, dict[int, Formula]], subset: int) -> Iterator[tuple[int, Gate]]:
    for left, right in partitions(subset):
        for x, fx in tables[left].items():
            for y, fy in tables[right].items():
                yield x & y, Gate("and", fx, fy)
                yield x | y, Gate("or", fx, fy)


def synthesize(inputs: list[int], target: int, gate_budget: int) -> Formula | None:
    if target in inputs:
        return inputs.index(target)

    # Each table keeps a single witness for a promised truth table on exactly
    # the wires in the subset. Subsequent gates depend only on the table.
    tables = {1 << i: {table: i} for i, table in enumerate(inputs)}
    for subset in range(1, 1 << len(inputs)):
        if not 2 <= bin(subset).count("1") <= gate_budget + 1:
            continue
        witnesses: dict[int, Formula] = {}
        for value, formula in candidates(tables, subset):
            if value == target:
                return formula
            witnesses.setdefault(value, formula)
        tables[subset] = witnesses
    return None


def circuit(formula: Formula, input_count: int) -> tuple[list[tuple[str, int, int]], int]:
    gates: list[tuple[str, int, int]] = []
    emitted: dict[Union[Gate, Not], int] = {}

    def wire(node: Formula) -> int:
        if isinstance(node, int):
            return node
        if node in emitted:
            return emitted[node]
        if isinstance(node, Not):
            op, left, right = "not", wire(node.operand), 0
        else:
            op, left, right = node.op, wire(node.left), wire(node.right)
        output = input_count + len(gates)
        gates.append((op, left, right))
        emitted[node] = output
        return output

    return gates, wire(formula)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rows", type=int)
    parser.add_argument("cols", type=int)
    parser.add_argument("target", type=int)
    parser.add_argument("gate_budget", type=int)
    args = parser.parse_args()
    if args.rows <= 0 or args.cols <= 0:
        parser.error("the two sides must be nonempty")
    if not 0 <= args.target < 1 << (args.rows * args.cols):
        parser.error("the target is outside the promised truth table")
    inputs = bipartite_inputs(args.rows, args.cols)
    formula = synthesize(inputs, args.target, args.gate_budget)
    if formula is None:
        raise SystemExit("No read-once witness within the gate budget")
    gates, output = circuit(formula, len(inputs))
    print(f"{len(gates)} gates, output wire {output}")
    for op, left, right in gates:
        print(f"      ⟨GateOp.{op}, [{left}, {right}]⟩,")


if __name__ == "__main__":
    main()
