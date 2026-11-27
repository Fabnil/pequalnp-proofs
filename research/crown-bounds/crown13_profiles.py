"""Profile restrictions for a 31-gate threshold-two circuit on thirteen inputs."""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
import json
import subprocess

from crown11_and_profiles import RUNS, bitset, system, width
from crown11_or_profiles import possible_counts, supported_groups, topological_graphs


INPUTS = 13


def budgets(stages, extra):
    """Each shared signal accounts for at least one extra read."""
    for separators in combinations(range(1, extra), stages - 1):
        points = (0, *separators, extra)
        yield tuple(1 + b - a for a, b in zip(points, points[1:]))


def stage_orders(pending, incoming):
    if not pending:
        yield ()
    for stage in range(len(incoming)):
        bit = 1 << stage
        if pending & bit and not pending & incoming[stage]:
            for other in stage_orders(pending ^ bit, incoming):
                yield (stage, *other)


def representative_graphs(stages, first, extra=6):
    """Permutations preserve the OR prefix, the first non-OR stage and its suffix."""
    prefix = (1 << first) - 1
    suffix = ((1 << stages) - 1) & ~((1 << (first + 1)) - 1)
    seen = set()
    for uses in budgets(stages, extra):
        for links, output in topological_graphs(uses):
            if (uses, links) in seen:
                continue
            incoming = [0] * stages
            for source, target in links:
                incoming[target] |= 1 << source
            if first < stages and width(incoming[first]) < 2:
                continue
            tails = tuple(stage_orders(suffix, incoming)) if first < stages else ((),)
            middle = (first,) if first < stages else ()
            for head in stage_orders(prefix, incoming):
                for tail in tails:
                    order = (*head, *middle, *tail)
                    rename = [0] * stages
                    for j, old in enumerate(order):
                        rename[old] = j
                    caps = tuple(uses[j] for j in order)
                    relabeled = tuple(sorted((rename[a], rename[b]) for a, b in links))
                    seen.add((caps, relabeled))
            yield uses, links, output


def or_cases():
    shapes = Counter()
    surviving = []
    for stages in range(4, 7):
        for uses, links, output in representative_graphs(stages, stages):
            shapes[stages] += 1
            groups = tuple(supported_groups(stages, links))
            for counts in possible_counts(groups, output, INPUTS):
                layout = [(g.profile, g.raw_reads, c) for g, c in zip(groups, counts) if c]
                covered = [sum(c for mask, _, c in layout if mask >> i & 1) for i in range(stages)]
                if min(covered) >= 2:
                    surviving.append({"uses": uses, "links": links, "output": output, "labels": layout})
    (RUNS / "crown13_or_profiles.json").write_text(json.dumps(surviving) + "\n", encoding="utf-8")
    print("OR graphs:", sorted(shapes.items()))
    print("OR survivors by stages and edges:", sorted(
        Counter((len(x["uses"]), len(x["links"])) for x in surviving).items()
    ))
    for case in surviving:
        labels = case["labels"]
        pairs = {mask for mask, raw, count in labels if raw == 0 and count == 1}
        matching = (case["uses"] == case["output"] == (2,) * 6 and not case["links"]
                    and (0, 2, 1) in labels and sum(count for _, _, count in labels) == 13
                    and len(pairs) == 12 and all(width(mask) == 2 for mask in pairs)
                    and all(sum(1 for mask in pairs if mask >> j & 1) == 4 for j in range(6)))
        if not matching:
            raise RuntimeError(f"Unexpected OR survivor: {case}")


def graph_masks(uses, links):
    stages = len(uses)
    incoming = [0] * stages
    outgoing = [0] * stages
    for source, target in links:
        incoming[target] |= 1 << source
        outgoing[source] |= 1 << target
    at_output = bitset(j for j, limit in enumerate(uses) if width(outgoing[j]) < limit)
    return incoming, outgoing, at_output


def and_instance(uses, first, links, prefix_support, inputs=INPUTS, **constraints):
    incoming, outgoing, at_output = graph_masks(uses, links)
    return system(uses, first, incoming, outgoing, at_output, inputs=inputs,
                  prefix_support=prefix_support, **constraints)


def and_instances():
    for stages in range(4, 7):
        for first in range(2, stages):
            for uses, links, _ in representative_graphs(stages, first):
                _, rules = and_instance(uses, first, links, prefix_support=2)
                if rules is not None:
                    yield {"uses": uses, "links": links, "first": first}, rules


def solve_batch(solver, batch, timeout, *, arithmetic_solver=None):
    query = ["(set-logic QF_LIA)", f"(set-option :timeout {timeout})"]
    if arithmetic_solver is not None:
        query.append(f"(set-option :smt.arith.solver {arithmetic_solver})")
    for label, (_, rules) in enumerate(batch):
        query += [f'(echo "{label}")', "(push 1)", *rules, "(check-sat)", "(pop 1)"]
    p = subprocess.run([solver, "-in", "-memory:650"], input="\n".join(query) + "\n", text=True,
                       capture_output=True, timeout=(len(batch) * timeout) // 1000 + 20)
    result = p.stdout.splitlines()
    if p.returncode or len(result) != 2 * len(batch) or result[::2] != [str(i) for i in range(len(batch))]:
        raise RuntimeError(p.stderr + p.stdout[-1800:])
    for (case, _), status in zip(batch, result[1::2]):
        if status not in {"sat", "unsat", "unknown"}:
            raise RuntimeError(status)
        yield case, status


def and_cases(solver):
    counts = Counter()
    surviving = []
    batch = []

    def check(ready):
        for case, status in solve_batch(solver, ready, timeout=500):
            counts[len(case["uses"]), case["first"] + 1, status] += 1
            if status != "unsat":
                surviving.append({**case, "status": status})

    for instance in and_instances():
        batch.append(instance)
        if len(batch) == 64:
            check(batch)
            batch.clear()
    if batch:
        check(batch)
    (RUNS / "crown13_and_profiles.json").write_text(json.dumps(surviving) + "\n", encoding="utf-8")
    print("AND systems by stages, first non-OR stage and status:", sorted(counts.items()))


def refine_cases(solver):
    path = RUNS / "crown13_and_profiles.json"
    cases = json.loads(path.read_text(encoding="utf-8"))
    batch = []
    for case in cases:
        _, rules = and_instance(case["uses"], case["first"], case["links"], prefix_support=3)
        if rules is not None:
            batch.append((case, rules))
    remaining = []
    counts = Counter()
    for i in range(0, len(batch), 8):
        for case, status in solve_batch(solver, batch[i:i + 8], timeout=5000):
            counts[status] += 1
            if status != "unsat":
                remaining.append({**case, "status": status})
    (RUNS / "crown13_and_refined.json").write_text(json.dumps(remaining) + "\n", encoding="utf-8")
    print("Cases with the three-singleton constraint:", sorted(counts.items()))
    if remaining:
        raise RuntimeError(f"{len(remaining)} systems still lack an unsatisfiability result")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=("or", "and", "refine"))
    parser.add_argument("--solver", default="z3")
    args = parser.parse_args()
    RUNS.mkdir(parents=True, exist_ok=True)
    if args.kind == "or":
        or_cases()
    elif args.kind == "and":
        and_cases(args.solver)
    else:
        refine_cases(args.solver)
