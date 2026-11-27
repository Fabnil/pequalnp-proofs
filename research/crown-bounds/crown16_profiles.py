"""Profile restrictions for a 38-gate threshold-two circuit on sixteen inputs."""

from argparse import ArgumentParser
from collections import Counter
import json
from subprocess import TimeoutExpired

from crown11_and_profiles import Profile, forms, prepared_shapes
from crown11_or_profiles import possible_counts, supported_groups
from crown13_profiles import RUNS, and_instance, graph_masks, representative_graphs, solve_batch


INPUTS = 16
EXTRA = 7
SUPPORT = 4
THRESHOLD_FLOORS = ((2, -3), (3, -2), (4, -1), (5, 0), (6, 1), (7, 2), (8, 3),
                    (10, 4), (11, 5), (13, 6))


def or_cases():
    graphs = Counter()
    remaining = []
    for stages in range(4, EXTRA + 1):
        for uses, links, output in representative_graphs(stages, stages, EXTRA):
            graphs[stages] += 1
            groups = tuple(supported_groups(stages, links))
            for counts in possible_counts(groups, output, INPUTS, min_support=SUPPORT):
                labels = [(g.profile, g.raw_reads, count) for g, count in zip(groups, counts) if count]
                remaining.append({"uses": uses, "links": links, "output": output, "labels": labels})
        print("OR graphs through", stages, ":", sorted(graphs.items()), "survivors", len(remaining), flush=True)
    (RUNS / "crown16_or_profiles.json").write_text(json.dumps(remaining) + "\n", encoding="utf-8")
    if remaining:
        raise RuntimeError(f"{len(remaining)} all-OR cases still lack an exclusion")


def and_cases(solver, timeout, stage_count, first_position):
    positions = range(3, stage_count + 1) if first_position is None else (first_position,)
    for position in positions:
        first = position - 1
        counts = Counter()
        remaining = []
        batch = []

        def check():
            for case, status in solve_batch(solver, batch, timeout, arithmetic_solver=2):
                counts[status] += 1
                if status != "unsat":
                    remaining.append({**case, "status": status})
            batch.clear()

        for uses, links, _ in representative_graphs(stage_count, first, EXTRA):
            _, rules = constraints(uses, first, links)
            if rules is not None:
                batch.append(({"uses": uses, "links": links, "first": first}, rules))
            else:
                counts["excluded_by_support"] += 1
            if len(batch) == 24:
                check()
        if batch:
            check()
        print("AND systems for", (stage_count, position), ":", sorted(counts.items()), flush=True)
        path = RUNS / f"crown16_joint_profiles_{stage_count}_{position}.json"
        path.write_text(json.dumps(remaining) + "\n", encoding="utf-8")


def constraints(uses, first, links, *, triples=False, pair_models=False, anchor=None, companion=None,
                opposite=None, sides=None):
    return and_instance(uses, first, links, prefix_support=SUPPORT, inputs=INPUTS,
                        irredundant_or=True, stage_support=SUPPORT, joint_pairs=True, all_prepared=True,
                        triples=triples, pair_models=pair_models, frozen_floors=THRESHOLD_FLOORS,
                        anchor=anchor, companion=companion, opposite=opposite, sides=sides)


def refine_cases(solver, timeout, stage_count, first, legacy, pending_only, triples, pair_models):
    path = RUNS / f"crown16_refined_{stage_count}_{first}.json"
    if legacy:
        original = RUNS / f"crown16_and_profiles_{stage_count}.json"
    elif pending_only:
        original = path
    else:
        original = RUNS / f"crown16_joint_profiles_{stage_count}_{first}.json"
    selected = [case for case in json.loads(original.read_bytes()) if case["first"] + 1 == first]
    pending = []
    counts = Counter()
    for start in range(0, len(selected), 12):
        batch = []
        for case in selected[start:start + 12]:
            _, rules = constraints(case["uses"], case["first"], case["links"],
                                   triples=triples, pair_models=pair_models)
            if rules is None:
                counts["excluded_by_support"] += 1
            else:
                batch.append((case, rules))
        for case, status in solve_batch(solver, batch, timeout, arithmetic_solver=2):
            counts[status] += 1
            if status != "unsat":
                pending.append({**case, "status": status})
    path.write_text(json.dumps(pending) + "\n", encoding="utf-8")
    print("Joint pair constraints for", (stage_count, first), ":", sorted(counts.items()), flush=True)


def overlap_anchors(case):
    """Any realization must contain a singleton witnessing the first AND."""
    first = case["first"]
    incoming, _, _ = graph_masks(case["uses"], case["links"])
    pure, choices = prepared_shapes(first, incoming)
    required = [(1 << s) | (1 << t) | (1 << first) for s, t in choices[first]]
    for profile in forms(case["uses"], pure, incoming, irredundant_or=True, distinct_shared=True):
        if any(profile.flags & mask == mask for mask in required):
            yield profile


def decode_profile(saved):
    readers, flags = saved
    return Profile(tuple(readers), flags)


def exclusive_branches(case):
    """Select an exclusive singleton for one of the first AND's two arguments."""
    anchor = decode_profile(case["anchor"])
    first = case["first"]
    incoming, _, _ = graph_masks(case["uses"], case["links"])
    _, choices = prepared_shapes(first, incoming)
    types, rules = constraints(case["uses"], first, case["links"], anchor=anchor)
    if rules is None:
        return
    for left, right in choices[first]:
        both = (1 << left) | (1 << right)
        if anchor.flags & both != both:
            continue
        witnesses = [[p for p in types if p.flags & both == 1 << flag] for flag in (left, right)]
        for p in min(witnesses, key=len):
            yield {**case, "sides": (left, right), "companion": (p.readers, p.flags)}


def opposite_branches(case):
    """Complete the three singleton witnesses for the first AND."""
    anchor = decode_profile(case["anchor"])
    companion = decode_profile(case["companion"])
    sides = tuple(case["sides"])
    both = (1 << sides[0]) | (1 << sides[1])
    target = both ^ (companion.flags & both)
    types, rules = constraints(case["uses"], case["first"], case["links"],
                               anchor=anchor, companion=companion, sides=sides)
    if rules is None:
        return
    for p in types:
        if p.flags & both == target:
            yield {**case, "opposite": (p.readers, p.flags)}


def solve_split_batch(solver, batch, timeout):
    """Keep answers printed before an outer timeout and isolate its remaining work."""
    if not batch:
        return []
    try:
        return list(solve_batch(solver, batch, timeout, arithmetic_solver=2))
    except TimeoutExpired as error:
        raw = error.stdout or b""
        output = raw.decode("ascii") if isinstance(raw, bytes) else raw
        lines = output.splitlines()
        if output and not output.endswith("\n"):
            lines.pop()
        done = []
        for i, (case, _) in enumerate(batch):
            if len(lines) < 2 * i + 2:
                break
            number, status = lines[2 * i:2 * i + 2]
            if number != str(i) or status not in {"sat", "unsat", "unknown"}:
                raise RuntimeError(f"Invalid solver output before timeout: {number!r}, {status!r}")
            done.append((case, status))
        left = batch[len(done):]
        if not left:
            return done
        if len(batch) == 1:
            return [(batch[0][0], "unknown")]
        middle = max(1, len(left) // 2)
        return done + solve_split_batch(solver, left[:middle], timeout) + solve_split_batch(solver, left[middle:], timeout)


def split_cases(solver, timeout, stage_count, first, pending_only, pair_models, exclusive, both_sides):
    primary = RUNS / f"crown16_split_{stage_count}_{first}.json"
    secondary = primary.with_name(primary.stem + "_exclusive.json")
    if both_sides:
        path = primary.with_name(primary.stem + "_both.json")
        original = path if pending_only else secondary
    elif exclusive:
        path = secondary
        original = path if pending_only else primary
    else:
        path = primary
        original = path if pending_only else RUNS / f"crown16_refined_{stage_count}_{first}.json"
    cases = json.loads(original.read_bytes())
    counts = Counter()
    remaining = []
    batch = []
    graphs_without_anchors = 0

    def check():
        for case, status in solve_split_batch(solver, batch, timeout):
            counts[status] += 1
            if status != "unsat":
                remaining.append({**case, "status": status})
        batch.clear()

    for pos, case in enumerate(cases, 1):
        if pending_only:
            branches = [case]
        elif both_sides:
            branches = list(opposite_branches(case))
        elif exclusive:
            branches = list(exclusive_branches(case))
        else:
            branches = [{**case, "anchor": (p.readers, p.flags)} for p in overlap_anchors(case)]
        if not branches:
            graphs_without_anchors += 1
        for branch in branches:
            anchor = decode_profile(branch["anchor"])
            companion = decode_profile(branch["companion"]) if "companion" in branch else None
            opposite = decode_profile(branch["opposite"]) if "opposite" in branch else None
            sides = tuple(branch["sides"]) if "sides" in branch else None
            _, rules = constraints(case["uses"], case["first"], case["links"],
                                   anchor=anchor, companion=companion, opposite=opposite,
                                   sides=sides, pair_models=pair_models)
            if rules is None:
                counts["excluded_by_support"] += 1
            else:
                batch.append((branch, rules))
            if len(batch) == 6:
                check()
        if not pending_only and pos % 10 == 0:
            print("Cases processed", pos, "of", len(cases), "branch results", sorted(counts.items()), flush=True)
    if batch:
        check()
    target = path.with_suffix(".tmp")
    target.write_text(json.dumps(remaining) + "\n", encoding="utf-8")
    target.replace(path)
    open_graphs = {tuple(map(tuple, case["links"])) + (tuple(case["uses"]),) for case in remaining}
    print("Split overlap cases", (stage_count, first), "branches", sorted(counts.items()),
          "cases without compatible witnesses", graphs_without_anchors, "open graphs", len(open_graphs), flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    choices = parser.add_subparsers(dest="case", required=True)
    choices.add_parser("or")
    mixed = choices.add_parser("and")
    mixed.add_argument("--first", type=int, choices=range(3, EXTRA + 1))
    refine = choices.add_parser("refine")
    refine.add_argument("first", type=int, choices=range(3, EXTRA + 1))
    sources = refine.add_mutually_exclusive_group()
    sources.add_argument("--legacy", action="store_true", help="read the original run without joint pair constraints")
    sources.add_argument("--pending", action="store_true", help="process cases left by the last refinement")
    comparisons = refine.add_mutually_exclusive_group()
    comparisons.add_argument("--triples", action="store_true", help="compare each pair with a third singleton")
    comparisons.add_argument("--pair-models", action="store_true", help="require a pair profile consistent with all singletons")
    split = choices.add_parser("split")
    split.add_argument("first", type=int, choices=range(3, EXTRA + 1))
    split.add_argument("--pending", action="store_true", help="check only unresolved branches from the last split run")
    split.add_argument("--pair-models", action="store_true")
    depth = split.add_mutually_exclusive_group()
    depth.add_argument("--exclusive", action="store_true", help="split each overlap branch by an exclusive singleton")
    depth.add_argument("--both-sides", action="store_true", help="also select a singleton on the other exclusive side")
    for check, default_timeout in ((mixed, 350), (refine, 1500), (split, 500)):
        check.add_argument("stages", type=int, choices=range(4, EXTRA + 1))
        check.add_argument("--solver", default="z3")
        check.add_argument("--timeout", type=int, default=default_timeout, help="milliseconds per system")
    args = parser.parse_args()
    RUNS.mkdir(parents=True, exist_ok=True)
    if args.case == "or":
        or_cases()
    elif args.case == "and":
        if args.first is not None and args.first > args.stages:
            mixed.error("the first AND must be a shared stage")
        and_cases(args.solver, args.timeout, args.stages, args.first)
    elif args.case == "refine":
        refine_cases(args.solver, args.timeout, args.stages, args.first, args.legacy, args.pending,
                     args.triples, args.pair_models)
    else:
        split_cases(args.solver, args.timeout, args.stages, args.first, args.pending, args.pair_models,
                    args.exclusive, args.both_sides)
