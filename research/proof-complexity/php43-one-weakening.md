# One weakening and the last pivot of PHP(4,3)

## Eliminating a single weakening

For any CNF, a Res(⊕) refutation with at most one weakening step yields an ordinary resolution refutation of at most the original length minus the number of weakenings. The Lean theorem `ordinaryRefutation` uses the project's clause and resolution rules. [Formal proof](ResolutionOneWeakening.lean)

After a single weakening, all nonsingleton equations come from that one line. Each later clause either contains the entire set of those equations or contains none of them. A singleton pivot preserves the nonsingleton equations. On a nonsingleton pivot, both parents contain the same set, so each loses only an equation that the other retains. Consequently a resolution whose output consists of singleton equations has parents of that form too. The singleton part of the proof can be simulated by ordinary resolution using subclauses, with the weakening discarded.

For PHP(4,3), the accepted ordinary lower bound of 52 lines now gives 53 lines for Res(⊕) refutations using exactly one weakening. Lean checks `php43Lower` with the standard axioms. [Accepted ordinary lower bound](https://github.com/open-goat/pequalnp-proofs/blob/661aa6ad1563cdaa2ecce4b9124db0eeaaa33885/lean/PEqualNP/Outside/L_pcx_150.lean#L2031)

## Axiom support of a final split

The first contradictory line must be a resolution. Axiom clauses are satisfiable, and an earlier line implying a contradictory clause would itself be contradictory. The pivot is nonzero because a constant pivot would leave an earlier contradictory parent. On each parity halfspace, the corresponding parent must be false on every assignment in that halfspace.

Each assignment must therefore falsify at least one axiom used in that parent's derivation. Record its set of violated axioms as a 22-bit mask. The minimum possible semantic support on either side is a minimum hitting set of those masks. The script enumerates the 86 orbits of nonzero pivots under pigeon and hole permutations. It computes the two hitting sets by branching on a currently uncovered mask, with singleton masks mandatory. Every axiom has an assignment violating that axiom alone, so the two supports cover all 22 axioms. [Reproduction script](php43-pivot-support.py)

The minimum intersection is nine axioms, attained by a singleton pivot with support sizes 19 and 12. For a nonsingleton pivot the minimum intersection is ten axioms. The script also checks disjoint violation masks on each side with a combined packing of at least 31 assignments for every orbit. In a tree proof the two parent subtrees must consequently have at least 31 axiom leaf occurrences between them. A tree with 31 leaves and unary or binary inferences has at least 61 nodes.

Run `python3 php43-pivot-support.py php43-pivot-support.json` from this directory to export the supports and the packing witnesses.

The support calculation and the tree bound use finite enumeration. The unrestricted 55-line question for DAG refutations remains open in this work.
