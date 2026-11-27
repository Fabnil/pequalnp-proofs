# Lower bound and leaf reads for L-meta-29220

The graph in [L-meta-29220](https://pequalnp.com/desk/row?gap=L-meta-29220) is a five-cycle with a hub and two pendant vertices attached to adjacent vertices of the cycle. The minimum is between 13 and 14 gates, both with unrestricted AND/OR/NOT gates of fan-in at most two and with AND/OR alone. In a 13-gate circuit, each pendant input has one reader after ignoring unused NOT arguments. The two readers are distinct binary ORs.

## Lower bound

The pendant vertices are 2 and 3, attached to 5 and 6 respectively. On clearing 2, the remaining inputs in the order \((0,1,3,5,4,6,7)\) give exactly the seven-vertex edge function in `L_meta_10890_aux.final`. That theorem gives a lower bound of 12 gates over the unrestricted three-gate basis. The graph automorphism \((0\ 1)(2\ 3)(5\ 6)\) gives the same bound on clearing 3. [Accepted proof](https://github.com/open-goat/pequalnp-proofs/blob/a4e197c6a09356bd4ffa5f513bf729729e2ef76e/lean/PEqualNP/Outside/L_meta_10890.lean#L2707) · [Kernel check of the relabeling](LeafWheel29220.lean)

Each pendant input is essential, as witnessed by the pair consisting of that pendant and its neighbor. The output is a gate because the function rejects all singletons and accepts an edge. At least one gate therefore reads the pendant. Interpret invalid reads as the false constant, discard ignored NOT arguments and simplify constants in evaluation order. Setting the pendant to false removes any gate reading it. AND becomes false, OR becomes an alias or false, and NOT becomes true. The restricted function is nonconstant, so propagating these constants requires no output constant gate. Thus clearing either pendant saves at least one gate, and the lower bound is \(12+1=13\).

## Shape at equality

Every gate of a 13-gate circuit is in the output cone, since pruning anything would contradict the lower bound. For each pendant, two distinct gates reading it would both be removed on setting it to false, leaving at most 11 gates for the seven-vertex function. There is therefore precisely one reader after ignoring surplus NOT operands.

If that reader is an AND, a NOT, or an OR with no other operand, it becomes constant. It has another consumer because the restricted function is nonconstant. Propagating the constant through that consumer removes a second gate, which again leaves at most 11. This also excludes a duplicated pendant operand in the OR or an operand that is already constant. The unique reader must be a binary OR with a distinct other operand.

The two readers cannot be the same OR. Otherwise the inputs with only one of the two pendants active would be indistinguishable when the core bits are fixed. With just vertex 5 active in the core, pendant 2 gives an edge and pendant 3 does not.

Stripping the two ORs from a size-13 candidate leaves an 11-gate circuit for the six-vertex wheel. The reverse operation adds each OR to some of the later reads of its other operand. The reduction preserves the number of NOTs.

## Upper bound

A 14-gate monotone circuit computes the OR of the four terms

$$
x_5(x_0\lor x_2\lor x_6\lor x_7),\quad
x_6(x_1\lor x_3\lor x_7),\quad
(x_0\lor x_1)(x_4\lor x_7),\quad
x_4x_7.
$$

Lean checks the complete circuit on every input. The size-13 case remains open. [Circuit and verification](LeafWheel29220.lean)
