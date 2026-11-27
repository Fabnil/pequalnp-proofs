"""Find small AND/OR/NOT circuits on a finite set of promised inputs."""

from __future__ import annotations

import argparse
import re
import subprocess

from read_once import bipartite_inputs
from screen_board import necessary_lines


def two_lit_instance(inputs: int, mask: int) -> tuple[list[int], int]:
    pairs = [(i, j) for i in range(inputs) for j in range(i, inputs)]
    wires = [sum(1 << k for k, pair in enumerate(pairs) if i in pair) for i in range(inputs)]
    target = sum(1 << k for k, (i, j) in enumerate(pairs) if mask & (1 << (inputs * i + j)))
    return wires, target


def necessary_inputs(wires: list[int], target: int, width: int) -> set[int]:
    rows = [
        sum(1 << i for i, wire in enumerate(wires) if (wire >> row) & 1)
        for row in range(width)
    ]
    output = {row: (target >> i) & 1 for i, row in enumerate(rows)}
    return {
        i
        for i in range(len(wires))
        if any((row ^ (1 << i)) in output and output[row] != output[row ^ (1 << i)] for row in rows)
    }


def problem(
    inputs: list[int], target: int, width: int, budget: int, *,
    allow_not: bool, timeout: int, required: set[int]
) -> tuple[str, int]:
    # Give the solver a false wire. The model can implement this using a
    # nonexistent wire, which the project's circuit evaluator reads as false.
    sources = [f"(_ bv{x} {width})" for x in (*inputs, 0)]
    index_width = (len(sources) + budget).bit_length()
    index = lambda n: f"(_ bv{n} {index_width})"
    lines = ["(set-logic QF_BV)", f"(set-option :timeout {timeout * 1000})"]
    queries: list[str] = []

    for gate in range(budget):
        a, b = f"a{gate}", f"b{gate}"
        left, right = f"left{gate}", f"right{gate}"
        out, disjunction, negation = f"out{gate}", f"or{gate}", f"not{gate}"
        skip = f"skip{gate}"
        for name in (a, b):
            lines += [
                f"(declare-fun {name} () (_ BitVec {index_width}))",
                f"(assert (bvult {name} {index(len(sources))}))",
            ]
        for name in (left, right, out):
            lines.append(f"(declare-fun {name} () (_ BitVec {width}))")
        for name in (disjunction, negation, skip):
            lines.append(f"(declare-fun {name} () Bool)")
        if not allow_not:
            lines.append(f"(assert (not {negation}))")
        lines += [
            f"(assert (=> (not {skip}) (ite {negation} (= {a} {b}) (bvult {a} {b}))))",
            f"(assert (=> {negation} (not {disjunction})))",
        ]
        for source_index, source in enumerate(sources):
            source_index = index(source_index)
            lines.append(f"(assert (=> (= {a} {source_index}) (= {left} {source})))")
            lines.append(f"(assert (=> (= {b} {source_index}) (= {right} {source})))")
        computed = f"(ite {negation} (bvnot {left}) (ite {disjunction} (bvor {left} {right}) (bvand {left} {right})))"
        lines.append(f"(assert (= {out} (ite {skip} {sources[-1]} {computed})))")
        # A gate equivalent to any earlier wire on the promise is redundant.
        not_redundant = " ".join(f"(not (= {out} {source}))" for source in sources)
        lines.append(f"(assert (=> (not {skip}) (and {not_redundant})))")
        if gate:
            lines.append(f"(assert (=> skip{gate - 1} {skip}))")
            prev = index(len(sources) - 1)
            # Among available gates a topological order may choose the
            # smallest truth table first. This removes symmetric orderings.
            independent = f"(and (not {skip}) (not (= {a} {prev})) (not (= {b} {prev})))"
            lines.append(f"(assert (=> {independent} (bvult out{gate - 1} {out})))")
        else:
            lines.append(f"(assert (not {skip}))")
        sources.append(out)
        queries.extend((a, b, disjunction, negation, skip))

    # Keep only the output cone of a circuit. After removing unused gates,
    # every nonfinal active gate and every essential input has a consumer.
    for wire in sorted(required | set(range(len(inputs) + 1, len(sources) - 1))):
        internal = wire >= len(inputs) + 1
        first_consumer = wire - len(inputs) if internal else 0
        operand = index(wire)
        uses = [
            f"(and (not skip{j}) (or (= a{j} {operand}) (= b{j} {operand})))"
            for j in range(first_consumer, budget)
        ]
        if internal:
            uses.append(f"skip{first_consumer}")
        lines.append(f"(assert (or {' '.join(uses)}))")

    outputs = []
    for gate in range(budget):
        # A circuit smaller than the budget ends immediately before the first skip.
        last = f"(not skip{gate})"
        if gate + 1 < budget:
            last = f"(and {last} skip{gate + 1})"
        outputs.append(f"(and {last} (= out{gate} (_ bv{target} {width})))")
    lines += [f"(assert (or {' '.join(outputs)}))", "(check-sat)", f"(get-value ({' '.join(queries)}))"]
    return "\n".join(lines), len(inputs)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", type=int)
    parser.add_argument("mask", type=int)
    parser.add_argument("budget", type=int)
    parser.add_argument("--cols", type=int, help="for a bipartite instance, interpret inputs as rows")
    parser.add_argument("--monotone", action="store_true")
    parser.add_argument("--timeout", type=int, default=40)
    parser.add_argument("--solver", default="/opt/homebrew/bin/z3")
    args = parser.parse_args()
    if args.inputs < 1 or args.budget < 1 or args.timeout < 1 or args.mask < 0:
        parser.error("expected a nonnegative mask and positive input count, budget and timeout")

    if args.cols is None:
        wires, target = two_lit_instance(args.inputs, args.mask)
        width = args.inputs * (args.inputs + 1) // 2
        required = necessary_inputs(wires, target, width)
    else:
        if args.cols < 1 or args.mask >= 1 << (args.inputs * args.cols):
            parser.error("invalid bipartite dimensions or mask")
        wires = bipartite_inputs(args.inputs, args.cols)
        target, width = args.mask, args.inputs * args.cols
        required = set()
        if args.monotone:
            rows = [{j for j in range(args.cols) if target & (1 << (args.cols * i + j))} for i in range(args.inputs)]
            cols = [{i for i in range(args.inputs) if j in rows[i]} for j in range(args.cols)]
            required.update(necessary_lines(rows))
            required.update(args.inputs + j for j in necessary_lines(cols))
    if target in wires:
        print(f"0 gates, output wire {wires.index(target)}")
        return
    if target == 0:
        print(f"0 gates, output wire {len(wires)}")
        return
    if target == (1 << width) - 1:
        print(f"1 gate, output wire {len(wires)}")
        print("      ⟨GateOp.and, []⟩,")
        return
    smt, false_wire = problem(
        wires, target, width, args.budget,
        allow_not=not args.monotone, timeout=args.timeout, required=required
    )
    result = subprocess.run(
        [args.solver, "-in", "-memory:900"], input=smt, capture_output=True, text=True,
        timeout=args.timeout + 8,
    )
    status = result.stdout.splitlines()[0] if result.stdout else ""
    if status not in {"sat", "unsat", "unknown"}:
        raise SystemExit(result.stdout[:800] or result.stderr[:800])
    if status != "sat":
        raise SystemExit(f"{status} for this search with up to {args.budget} gates")

    values = dict(re.findall(r"\((\w+) (#x[0-9a-fA-F]+|#b[01]+|true|false)\)", result.stdout))

    def wire(key: str) -> int:
        value = values[key]
        i = int(value[2:], 16 if value.startswith("#x") else 2)
        if i == false_wire:
            return false_wire + args.budget + 1
        return i - (i > false_wire)

    used = sum(values[f"skip{i}"] == "false" for i in range(args.budget))
    print(f"{used} gates, output wire {len(wires) + used - 1}")
    for gate in range(used):
        a, b = wire(f"a{gate}"), wire(f"b{gate}")
        if values[f"not{gate}"] == "true":
            print(f"      ⟨GateOp.not, [{a}]⟩,")
        else:
            op = "or" if values[f"or{gate}"] == "true" else "and"
            print(f"      ⟨GateOp.{op}, [{a}, {b}]⟩,")


if __name__ == "__main__":
    main()
