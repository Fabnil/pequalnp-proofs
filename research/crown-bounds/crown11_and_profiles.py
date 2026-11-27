"""Check the finite profile systems for a first non-OR shared stage."""

from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations
import os
from pathlib import Path
import subprocess

from crown11_or_profiles import topological_graphs


RUNS = Path(os.environ.get("CROWN_RUNS", Path(__file__).resolve().parents[1] / ".pnp-local" / "runs"))


def members(mask, count):
    return [i for i in range(count) if mask >> i & 1]


def width(mask):
    return bin(mask).count("1")


@dataclass(frozen=True)
class Profile:
    readers: tuple
    flags: int


def bitset(flags):
    return sum(1 << s for s in flags)


def forms(uses, pure, incoming, *, irredundant_or=False, distinct_shared=False):
    k = len(uses)
    for readers in combinations_with_replacement(range(k + 1), 2):
        if distinct_shared and readers[0] == readers[1] and readers[0] < k:
            continue
        masks = [0]
        for j in range(k):
            next_masks = []
            for flags in masks:
                provided = j in readers or bool(flags & incoming[j])
                if pure >> j & 1:
                    if irredundant_or and j in readers and (readers == (j, j) or flags & incoming[j]):
                        continue
                    next_masks.append(flags | (1 << j) if provided else flags)
                    continue
                next_masks.append(flags)
                if provided:
                    next_masks.append(flags | (1 << j))
            masks = next_masks
        for flags in sorted(masks):
            if flags != (1 << k) - 1:
                yield Profile(readers, flags)


def price(profile, fixed, pure, uses, incoming, outgoing, scale):
    baseline = fixed
    for j in members(pure, len(uses)):
        if baseline & incoming[j]:
            baseline |= 1 << j
    raw = sum(not (fixed >> s & 1) for s in profile.readers)
    extra = sum(max(0, uses[s] - 1 - width(fixed & outgoing[s]))
                for s in members(profile.flags & ~baseline, len(uses)))
    return scale >> (raw + extra)


def can_switch(before, added, first, incoming, read_at_output):
    output = len(incoming)
    if output in added.readers:
        return True
    changes = (added.flags & ((1 << first) - 1)) & ~before.flags
    for j in range(first, output):
        if not (before.flags >> j & 1) and (j in added.readers or changes & incoming[j]):
            changes |= 1 << j
    return bool(changes & read_at_output)


def pair_activations(a, b, first, incoming, witness=None):
    """Bound the pair using the two singletons and an optional comparison."""
    may_on = a.flags | b.flags
    for j in range(first, len(incoming)):
        if (witness is not None and not witness.flags >> j & 1 and j not in a.readers
                and j not in b.readers and not (may_on & incoming[j] & ~witness.flags)):
            # The pair cannot exceed the off singleton at this formula's inputs.
            continue
        if not (may_on >> j & 1) and (
            j in b.readers or may_on & incoming[j] & ~a.flags
        ) and (
            j in a.readers or may_on & incoming[j] & ~b.flags
        ):
            may_on |= 1 << j
    return may_on


def output_can_switch(a, b, may_on, output, read_at_output):
    return bool((output in b.readers or may_on & read_at_output & ~a.flags)
                and (output in a.readers or may_on & read_at_output & ~b.flags))


def pair_can_switch(a, b, first, incoming, read_at_output):
    return output_can_switch(a, b, pair_activations(a, b, first, incoming), len(incoming), read_at_output)


def pair_blocked_by(a, b, witness, first, incoming, read_at_output):
    upper = pair_activations(a, b, first, incoming, witness=witness)
    output = len(incoming)
    accepted = output_can_switch(a, b, upper, output, read_at_output)
    dominated = (output not in a.readers and output not in b.readers
                 and not (upper & read_at_output & ~witness.flags))
    return not accepted or dominated


def triple_rules(types, first, incoming, at_output, eligible):
    for i, a in enumerate(types):
        for j in range(i + 1, len(types)):
            if not eligible[i] >> j & 1:
                continue
            b = types[j]
            blocked = []
            for k in members(eligible[i] & eligible[j], len(types)):
                if pair_blocked_by(a, b, types[k], first, incoming, at_output):
                    blocked.append(variable(k))
            if blocked:
                yield f"(assert (or (= {variable(i)} 0) (= {variable(j)} 0) (= {smt_sum(blocked)} 0)))"


def pair_masks(a, b, pure, incoming, at_output):
    """Enumerate pair profiles consistent with their two singleton profiles."""
    masks = [0]
    singleton_union = a.flags | b.flags
    for stage, parents in enumerate(incoming):
        bit = 1 << stage
        next_masks = []
        for flags in masks:
            if pure & bit:
                on = flags & parents or stage in a.readers or stage in b.readers
                next_masks.append(flags | bit if on else flags)
                continue
            if not singleton_union & bit:
                next_masks.append(flags)
            changed_from_a = a.flags & bit or stage in b.readers or flags & parents & ~a.flags
            changed_from_b = b.flags & bit or stage in a.readers or flags & parents & ~b.flags
            if changed_from_a and changed_from_b:
                next_masks.append(flags | bit)
        masks = next_masks
    return (flags for flags in masks if output_can_switch(a, b, flags, len(incoming), at_output))


def pair_agrees_with(a, b, flags, witness, incoming, at_output):
    output = len(incoming)
    for stage, parents in enumerate((*incoming, at_output)):
        if stage == output or flags >> stage & 1:
            if (not witness.flags >> stage & 1 and stage not in a.readers and stage not in b.readers
                    and not flags & parents & ~witness.flags):
                return False
        elif (witness.flags >> stage & 1 and stage not in witness.readers
              and not witness.flags & parents & ~flags):
            return False
    return True


def pair_mask_rules(types, pure, incoming, at_output, eligible, limits):
    output = len(incoming)
    parents = (*incoming, at_output)

    @lru_cache(maxsize=None)
    def on_witnesses(stage, flags):
        return bitset(i for i, p in enumerate(types) if p.flags >> stage & 1 and stage not in p.readers
                      and not (p.flags & parents[stage] & ~flags))

    @lru_cache(maxsize=None)
    def off_witnesses(stage, flags):
        return bitset(i for i, p in enumerate(types) if not p.flags >> stage & 1 and not (flags & ~p.flags))

    for i, a in enumerate(types):
        for j in range(i, len(types)):
            repeat = i == j
            if (repeat and limits[i] < 2) or (not repeat and not eligible[i] >> j & 1):
                continue
            b = types[j]
            raw = set(a.readers) | set(b.readers)
            candidates = eligible[i] & eligible[j]
            exclusions = []
            for flags in pair_masks(a, b, pure, incoming, at_output):
                bad = 0
                for stage, pred in enumerate(parents):
                    if flags >> stage & 1 or stage == output:
                        if stage not in raw:
                            bad |= off_witnesses(stage, flags & pred)
                    else:
                        bad |= on_witnesses(stage, flags & pred)
                bad &= candidates
                if not bad:
                    break
                if not any(old & bad == old for old in exclusions):
                    exclusions = [old for old in exclusions if old & bad != bad]
                    exclusions.append(bad)
            else:
                guards = [f"(<= {variable(i)} 1)"] if repeat else [f"(= {variable(i)} 0)", f"(= {variable(j)} 0)"]
                for mask in exclusions:
                    absent = smt_sum([variable(k) for k in members(mask, len(types))])
                    guards.append(f"(= {absent} 0)")
                yield f"(assert (or {' '.join(guards)}))"


def monotone_pair(below, above, first, incoming, reject_redundant_raw=False):
    for j in range(first, len(incoming)):
        if below.flags >> j & 1 and j not in below.readers and not (incoming[j] & below.flags & ~above.flags):
            if not above.flags >> j & 1 or (reject_redundant_raw and j in above.readers):
                return False
    return True


def compatible(a, b, first, incoming, at_output, joint_pairs, all_prepared):
    possible = pair_can_switch(a, b, first, incoming, at_output) if joint_pairs else (
        can_switch(a, b, first, incoming, at_output) and can_switch(b, a, first, incoming, at_output)
    )
    return (possible and monotone_pair(a, b, first, incoming, all_prepared)
            and monotone_pair(b, a, first, incoming, all_prepared))


def smt_sum(terms):
    return "(+ 0 " + " ".join(terms) + ")" if terms else "0"


def variable(i):
    return f"x{i}"


def prepared_shapes(first, incoming):
    """Every OR stage inherits the signals that imply one of its arguments."""
    pure = (1 << first) - 1
    implies = []
    overlap_choices = []
    for j, parents in enumerate(incoming):
        predecessors = members(parents, j)
        pairs = [(s, t) for s, t in combinations(predecessors, 2)
                 if not (implies[s] >> t & 1 or implies[t] >> s & 1)]
        if j > first and not pairs:
            pure |= 1 << j
        baseline = 1 << j
        if pure >> j & 1:
            for p in predecessors:
                baseline |= implies[p]
        implies.append(baseline)
        overlap_choices.append(pairs)
    return pure, overlap_choices


def frozen_budget_rules(types, uses, pure, incoming, outgoing, floors, scale):
    """Apply smaller threshold lower bounds after freezing shared signals."""
    stages = len(uses)
    all_stages = (1 << stages) - 1
    readers = [(1 << p.readers[0]) | (1 << p.readers[1]) for p in types]
    budgets = {}
    packings = set()
    for fixed in range(1, 1 << stages):
        live = all_stages ^ fixed
        fees = [(j, max(0, uses[j] - 1 - width(fixed & outgoing[j]))) for j in members(live, stages)]
        surplus = sum(fee for _, fee in fees)
        for on in range(fixed + 1):
            if on & fixed != on:
                continue
            silent = fixed ^ on
            if any(incoming[j] & ~fixed for j in members(silent, stages)):
                continue
            # The silent stages read no remaining raw input and only fixed
            # predecessors, so their values are constant as well.
            group = tuple((i, sum(on >> t & 1 for t in p.readers))
                          for i, p in enumerate(types) if p.flags & on == on and not readers[i] & silent)
            if group:
                budgets[group] = min(budgets.get(group, surplus), surplus)
            if silent and group:
                base = on
                for stage in members(pure, stages):
                    if base & incoming[stage]:
                        base |= 1 << stage
                row = tuple((i, scale >> (2 - lost + sum(
                    fee for j, fee in fees if (types[i].flags & ~base) >> j & 1
                ))) for i, lost in group)
                packings.add(row)

    for index, (group, surplus) in enumerate(budgets.items()):
        labels = smt_sum([variable(i) for i, _ in group])
        lost = smt_sum([f"(* {leaves} {variable(i)})" for i, leaves in group if leaves])
        size = f"group{index}"
        removed = f"lost{index}"
        yield f"(define-fun {size} () Int {labels})"
        if lost != "0":
            yield f"(define-fun {removed} () Int {lost})"
        for minimum, margin in floors:
            allowance = surplus - 1 - margin
            if allowance < 0:
                yield f"(assert (< {size} {minimum}))"
                break
            if lost != "0":
                yield f"(assert (or (< {size} {minimum}) (<= {removed} {allowance})))"
    for group in sorted(packings):
        weight = smt_sum([f"(* {cost} {variable(i)})" for i, cost in group])
        yield f"(assert (<= {weight} {scale}))"


def system(uses, first, incoming, outgoing, at_output, inputs=11, prefix_support=2,
           *, irredundant_or=False, stage_support=0, joint_pairs=False, all_prepared=False,
           triples=False, pair_models=False, frozen_floors=(), anchor=None, companion=None,
           opposite=None, sides=None):
    pure = (1 << first) - 1
    if all_prepared:
        pure, overlap_choices = prepared_shapes(first, incoming)
    raw_or = 0
    for j in members(pure, len(uses)):
        if incoming[j] & ~raw_or == 0:
            raw_or |= 1 << j
    if all_prepared and raw_or >> first:
        # Schedule all OR-only stages with OR-only ancestors before the first AND.
        return [], None
    types = list(forms(uses, pure, incoming, irredundant_or=irredundant_or,
                       distinct_shared=all_prepared))
    known = tuple(p for p in (anchor, companion, opposite) if p is not None)
    if known:
        def allowed_masks(a, b):
            other = [p for p in known if p != a and p != b]
            return [flags for flags in pair_masks(a, b, pure, incoming, at_output)
                    if all(pair_agrees_with(a, b, flags, p, incoming, at_output) for p in other)]

        def coexist(a, b):
            return a == b or (compatible(a, b, first, incoming, at_output, joint_pairs, all_prepared)
                              and bool(allowed_masks(a, b)))

        types = [p for p in types if all(coexist(p, witness) for witness in known)]
        if any(p not in types for p in known):
            return types, None
        frozen_pairs = [(a, b, allowed_masks(a, b)) for a, b in combinations(known, 2)]
        types = [p for p in types if p in known or all(
            any(pair_agrees_with(a, b, flags, p, incoming, at_output) for flags in masks)
            for a, b, masks in frozen_pairs
        )]
    scale = 1 << (2 + sum(limit - 1 for limit in uses))

    def labels(predicate):
        return smt_sum([variable(i) for i, p in enumerate(types) if predicate(p.flags)])

    def counts(predicate):
        return smt_sum([variable(i) for i, p in enumerate(types) if predicate(p)])

    alternatives = []
    first_choices = overlap_choices[first] if all_prepared else combinations(members(incoming[first], len(uses)), 2)
    for s, t in first_choices:
        both = bitset((s, t))
        if sides is not None and (s, t) != sides:
            continue
        if anchor is not None and anchor.flags & both != both:
            continue
        above = both | (1 << first)
        demands = (
            labels(lambda mask: mask & above == above),
            labels(lambda mask: mask & both == 1 << s),
            labels(lambda mask: mask & both == 1 << t),
        )
        if all(term != "0" for term in demands):
            alternatives.append("(and " + " ".join(f"(> {term} 0)" for term in demands) + ")")
    if not alternatives:
        return types, None

    require = []
    if all_prepared:
        first_off = counts(lambda p: not p.flags >> first & 1
                           and (first in p.readers or p.flags & incoming[first]))
        if first_off == "0":
            return types, None
        require.append(f"(assert (> {first_off} 0))")
    if irredundant_or:
        private_support = stage_support if all_prepared else 1
        for target in members(pure, len(uses)):
            for source in members(incoming[target] & raw_or, len(uses)):
                only_source = counts(lambda p: p.flags & incoming[target] == 1 << source
                                     and target not in p.readers)
                if only_source == "0":
                    return types, None
                require.append(f"(assert (>= {only_source} {private_support}))")
    if stage_support or all_prepared:
        ancestors = []
        for j in range(len(uses)):
            ancestry = {j}
            for i in members(incoming[j], j):
                ancestry.update(ancestors[i])
            ancestors.append(ancestry)
            if not (raw_or >> j & 1):
                raw = counts(lambda p: any(i in ancestry for i in p.readers))
                minimum = stage_support + (all_prepared and j == first)
                require.append(f"(assert (>= {raw} {minimum}))")
                if all_prepared and j > first and not (pure >> j & 1):
                    mismatch = counts(lambda p: bool(p.flags >> j & 1)
                                      != bool(j in p.readers or p.flags & incoming[j]))
                    overlap = labels(lambda flags: flags >> j & 1 and any(
                        flags >> s & 1 and flags >> t & 1 for s, t in overlap_choices[j]
                    ))
                    and_stage = f"(and (> {overlap} 0) (>= {raw} {stage_support + 1}))"
                    if incoming[j] & ~raw_or == 0:
                        require.append(f"(assert {and_stage})")
                        require.append(f"(assert (> {mismatch} 0))")
                    else:
                        require.append(f"(assert (or (= {mismatch} 0) {and_stage}))")

    if all_prepared:
        for readers in combinations(members(pure, len(uses)), 2):
            same = counts(lambda p: p.readers == readers)
            if same != "0":
                require.append(f"(assert (<= {same} 1))")

        for target in range(first, len(uses)):
            if pure >> target & 1:
                continue
            parents = incoming[target]
            if width(parents) >= 2 and not parents & ~raw_or:
                # Zero all direct readers. If the remaining arguments form a
                # chain, the surviving formula collapses to one shared leaf.
                chain_violations = set()
                for order in permutations(members(parents, len(uses))):
                    adjacent = tuple(zip(order, order[1:]))
                    broken = counts(lambda p: target in p.readers or any(
                        p.flags >> s & 1 and not p.flags >> t & 1 for s, t in adjacent
                    ))
                    chain_violations.add(broken)
                require.extend(f"(assert (>= {broken} {stage_support}))" for broken in sorted(chain_violations))
            for source in members(parents & raw_or, len(uses)):
                contexts = {
                    p.flags & parents for p in types
                    if p.flags >> target & 1 and not p.flags >> source & 1 and target not in p.readers
                }
                for fixed in sorted(contexts):
                    witnesses = counts(lambda p: p.flags >> target & 1 and target not in p.readers
                                       and p.flags & parents == fixed)
                    uncovered = labels(lambda flags: flags >> source & 1 and fixed & ~flags)
                    require.append(f"(assert (or (= {witnesses} 0) (>= {uncovered} {stage_support})))")

    lines = []
    limits = []
    for i, profile in enumerate(types):
        v = variable(i)
        lines.extend((f"(declare-const {v} Int)", f"(assert (>= {v} 0))"))
        cap = scale // price(profile, profile.flags, pure, uses, incoming, outgoing, scale)
        if (not can_switch(profile, profile, first, incoming, at_output)
                or any(witness != profile and pair_blocked_by(profile, profile, witness, first, incoming, at_output)
                       for witness in known)):
            cap = 1
        limits.append(cap)
        lines.append(f"(assert (<= {v} {cap}))")
    lines.append(f"(assert (= {labels(lambda _: True)} {inputs}))")
    for profile in known:
        lines.append(f"(assert (> {variable(types.index(profile))} 0))")
    lines.append("(assert (or " + " ".join(alternatives) + "))")
    lines.extend(require)
    for j in range(len(uses)):
        reaches = labels(lambda mask: mask >> j & 1)
        lines.append(f"(assert (>= {reaches} {prefix_support if raw_or >> j & 1 else 1}))")
    for fixed in range(1 << len(uses)):
        terms = [f"(* {price(p, fixed, pure, uses, incoming, outgoing, scale)} {variable(i)})"
                 for i, p in enumerate(types) if p.flags & fixed == fixed]
        if terms:
            lines.append(f"(assert (<= {smt_sum(terms)} {scale}))")
    if frozen_floors:
        lines.extend(frozen_budget_rules(types, uses, pure, incoming, outgoing, frozen_floors, scale))
    eligible = [0] * len(types)
    for i, j in combinations(range(len(types)), 2):
        a, b = types[i], types[j]
        if (not compatible(a, b, first, incoming, at_output, joint_pairs, all_prepared)
                or any(witness != a and witness != b and pair_blocked_by(a, b, witness, first, incoming, at_output)
                       for witness in known)):
            lines.append(f"(assert (or (= {variable(i)} 0) (= {variable(j)} 0)))")
        elif triples or pair_models:
            eligible[i] |= 1 << j
            eligible[j] |= 1 << i
    if triples:
        lines.extend(triple_rules(types, first, incoming, at_output, eligible))
    if pair_models:
        lines.extend(pair_mask_rules(types, pure, incoming, at_output, eligible, limits))
    return types, lines


def listed_layouts(incoming, first):
    k = len(incoming)
    late = k - 1
    if k != 5 or any(mask for j, mask in enumerate(incoming) if j != first):
        return []
    predecessors = members(incoming[first], k)
    H = k

    def label(readers, flags):
        return Profile(tuple(sorted(readers)), bitset(flags))

    if len(predecessors) == 3:
        other, = set(range(k)) - set(predecessors) - {first}
        layout = [label((a, b), (a, b, first)) for a, b in combinations(predecessors, 2)]
        layout += [label((a, H), (a,)) for a in predecessors]
        layout += [label((a, other), (a, other)) for a in predecessors]
        layout.append(label((first, other), (first, other)))
        cold = [(H, H), (first, H)]
        if other > first:
            cold.append((other, H))
        return [Counter(layout + [label(c, ())]) for c in cold]
    if first == late and len(predecessors) == 4:
        a, *tail = predecessors
        result = []
        for b in tail:
            part = {a, b}
            layout = [label((s, t), (s, t, first) if (s in part) != (t in part) else (s, t))
                      for s, t in combinations(predecessors, 2)]
            layout += [label((s, H), (s,)) for s in predecessors]
            result.extend(Counter(layout + [label(c, ())]) for c in ((H, H), (first, H)))
        return result
    return []


def outside(types, allowed):
    options = []
    for layout in allowed:
        if not layout.keys() <= set(types):
            raise ValueError("Listed layout includes an unavailable profile")
        options.append("(and " + " ".join(
            f"(= {variable(i)} {layout[profile]})" for i, profile in enumerate(types)
        ) + ")")
    return "(assert (not (or " + " ".join(options) + ")))" if options else ""


def check(solver):
    queries = ["(set-logic QF_LIA)", "(set-option :timeout 850)"]
    counts = Counter()
    declared = 0
    cases = 0
    patterns = [tuple(2 + (i == triple) for i in range(4)) for triple in range(4)]
    patterns.append((2,) * 5)
    for uses in patterns:
        k = len(uses)
        for links, output in topological_graphs(uses):
            incoming = [0] * k
            outgoing = [0] * k
            for source, target in links:
                incoming[target] |= 1 << source
                outgoing[source] |= 1 << target
            at_output = bitset(j for j, cap in enumerate(output) if cap)
            for first in range(2, k):
                if width(incoming[first]) < 2:
                    continue
                types, rules = system(uses, first, incoming, outgoing, at_output)
                if rules is None:
                    continue
                allowed = listed_layouts(incoming, first)
                declared += len(allowed)
                case = f"{k}-{first + 1}-{''.join(map(str, uses))}-{','.join(map(str, incoming))}"
                queries += [f'(echo "{case}")', "(push 1)", *rules, outside(types, allowed),
                            "(check-sat)", "(pop 1)"]
                counts[k, first + 1] += 1
                cases += 1
    contents = "\n".join(queries) + "\n"
    (RUNS / "crown11_and_profiles.smt2").write_text(contents, encoding="utf-8")
    run = subprocess.run([solver, "-in", "-memory:650"], input=contents, text=True,
                         capture_output=True, timeout=105)
    (RUNS / "crown11_and_profiles.log").write_text(run.stdout + run.stderr, encoding="utf-8")
    result = run.stdout.splitlines()
    if run.returncode != 0 or len(result) != 2 * cases:
        raise RuntimeError("Incomplete result, see crown11_and_profiles.log")
    remaining = [(c, s) for c, s in zip(result[::2], result[1::2]) if s != "unsat"]
    if remaining:
        raise RuntimeError(f"Unexpected solver results: {remaining}")
    return cases, declared, sorted(counts.items())


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="z3")
    args = parser.parse_args()
    RUNS.mkdir(parents=True, exist_ok=True)
    cases, layouts, counts = check(args.solver)
    print(f"Checked {cases} systems outside the {layouts} listed layouts.")
    print("Systems by (stages, position of first non-OR stage):", counts)
