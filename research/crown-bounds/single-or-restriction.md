# Removing one OR at a tight cofactor bound

Let a Boolean function have an essential input \(p\), with both cofactors nonconstant. Suppose the false cofactor has lower bound \(s\) in the fan-in-two AND/OR/NOT basis. In a minimum circuit of size at most \(s+1\), exactly one gate reads \(p\). That gate is \(p\lor w\) for a distinct earlier wire \(w\). [Lean proof](SingleOrRestriction.lean)

Two readers would lose two gates on setting \(p=0\). A sole AND or NOT reader would become constant and lose a second gate at its next consumer, which exists because the false cofactor is nonconstant. A duplicated operand is an alias and would contradict minimality. `tightSoleOr` formalizes these cases.

On setting \(p=0\), the circuit simplifier redirects reads of \(p\lor w\) to \(w\), removes that OR, and retains the remaining gate operations in order. `restrictOperations` also covers several pinned inputs when each reader is an OR with an unpinned second operand. For the single-input case, `tightCofactor` additionally certifies evaluation of the cofactor, an exact one-gate saving, and equality of NOT counts.

If every circuit for the cofactor containing a NOT requires at least \(s+1\) gates, every least circuit for the original function of size at most \(s+1\) is monotone. With a monotone witness of size at most \(s+2\), `monotoneReplacement` gives a monotone circuit within the budget of any AND/OR/NOT circuit. This can use a lower bound that excludes only the circuits containing a NOT at the cofactor's minimum size.

`trueOrPathBlocksInfluence` gives a separate constraint for synthesis. If changing an input with one reader changes the output, a wire that is true in both assignments cannot reach the reader along a path of OR gates. Such a path would make the reader true in both assignments, and the circuit cut at that reader would force the outputs to agree.

## The graph of L-meta-29220

The [accepted certificate](https://github.com/open-goat/pequalnp-proofs/pull/43900) yields a lower bound of 14 whenever the circuit contains one or more NOTs. For a putative size-13 circuit, `bridge_not` produces either a certificate of size at most 12 or a live certificate at size 13 with a positive number of NOTs. The accepted `iroot` and `iroot_pos` exclude those two cases, respectively. The 14-gate monotone witness then gives replacement for arbitrary numbers of NOTs. [Lean proof using these accepted lemmas](LeafWheelUnrestricted.lean)
