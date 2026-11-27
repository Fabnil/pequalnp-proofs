"""Find promised circuits with one shared subformula and up to one NOT."""

from __future__ import annotations

import argparse

from circuit_search import necessary_inputs, two_lit_instance
from read_once import Formula, Gate, Not, bipartite_inputs, candidates, circuit, partitions, synthesize
from screen_board import necessary_lines


def synthesize_one_not(inputs: list[int], target: int, width: int) -> Formula | None:
    universe = (1 << width) - 1
    positive: dict[int, dict[int, Formula]] = {1 << i: {t: i} for i, t in enumerate(inputs)}
    negative: dict[int, dict[int, Formula]] = {1 << i: {t ^ universe: Not(i)} for i, t in enumerate(inputs)}
    for scope in range(1, 1 << len(inputs)):
        if scope not in positive:
            plain: dict[int, Formula] = {}
            for truth, formula in candidates(positive, scope):
                plain.setdefault(truth, formula)
            positive[scope] = plain
            signed: dict[int, Formula] = {truth ^ universe: Not(formula) for truth, formula in plain.items()}
            for a, b in partitions(scope):
                for signed_part, plain_part in ((a, b), (b, a)):
                    for x, fx in negative[signed_part].items():
                        for y, fy in positive[plain_part].items():
                            signed.setdefault(x & y, Gate("and", fx, fy))
                            signed.setdefault(x | y, Gate("or", fx, fy))
            negative[scope] = signed
        if target in negative[scope]:
            return negative[scope][target]
    return None


def search(wires: list[int], selected: list[int], target: int, *, signed_width: int = 0) -> Formula | None:
    count = len(selected)
    full = (1 << count) - 1
    tables: dict[int, dict[int, Formula]] = {
        1 << i: {wires[wire]: wire} for i, wire in enumerate(selected)
    }
    for shared_mask in range(1, full):
        if shared_mask not in tables:
            subs: dict[int, Formula] = {}
            for value, formula in candidates(tables, shared_mask):
                subs.setdefault(value, formula)
            tables[shared_mask] = subs
        remainder = [wire for i, wire in enumerate(selected) if not shared_mask & (1 << i)]
        independent = [wires[wire] for wire in remainder]
        for value, shared in tables[shared_mask].items():
            values = [*independent, value, value]
            if signed_width:
                outer = synthesize_one_not(values, target, signed_width)
            else:
                outer = synthesize(values, target, len(independent) + 1)
            if outer is None:
                continue

            def substitute(formula: Formula) -> Formula:
                if isinstance(formula, int):
                    return remainder[formula] if formula < len(remainder) else shared
                if isinstance(formula, Not):
                    return Not(substitute(formula.operand))
                return Gate(formula.op, substitute(formula.left), substitute(formula.right))

            return substitute(outer)
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parameters", type=int, nargs="+", help="rows cols mask, or inputs mask with --two-lit")
    parser.add_argument("--two-lit", action="store_true", help="use the two-lit promise and include one NOT")
    args = parser.parse_args()
    signed_width = 0
    if args.two_lit:
        if len(args.parameters) != 2:
            parser.error("expected inputs mask")
        n, mask = args.parameters
        if not 2 <= n <= 7 or not 0 <= mask < 1 << (n * n):
            parser.error("invalid number of inputs or mask")
        signed_width = n * (n + 1) // 2
        wires, target = two_lit_instance(n, mask)
        selected = sorted(necessary_inputs(wires, target, signed_width))
    else:
        if len(args.parameters) != 3:
            parser.error("expected rows cols mask")
        n, m, target = args.parameters
        if not (1 <= n <= 12 and 1 <= m <= 12 and 0 <= target < 1 << (n * m)):
            parser.error("invalid dimensions or mask")
        row_sets = [{j for j in range(m) if target & (1 << (m * i + j))} for i in range(n)]
        col_sets = [{i for i in range(n) if j in row_sets[i]} for j in range(m)]
        selected = necessary_lines(row_sets) + [n + j for j in necessary_lines(col_sets)]
        wires = bipartite_inputs(n, m)
    if len(selected) > 9:
        parser.error("more than nine required inputs exceeds this search's intended scale")
    formula = search(wires, selected, target, signed_width=signed_width)
    if formula is None:
        raise SystemExit(f"No witness in the single-fork search on {len(selected)} required wires")
    gates, output = circuit(formula, len(wires))
    print(f"{len(gates)} gates, output wire {output}")
    for op, a, b in gates:
        print(f"      ⟨GateOp.{op}, [{a}]⟩," if op == "not" else f"      ⟨GateOp.{op}, [{a}, {b}]⟩,")


if __name__ == "__main__":
    main()
