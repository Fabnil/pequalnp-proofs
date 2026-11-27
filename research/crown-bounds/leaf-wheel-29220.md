# Lower bound and leaf reads for L-meta-29220

The graph in [L-meta-29220](https://pequalnp.com/desk/row?gap=L-meta-29220) is a five-cycle with a hub and two pendant vertices attached to adjacent vertices of the cycle. The minimum is between 13 and 14 gates, both with unrestricted AND/OR/NOT gates of fan-in at most two and with AND/OR alone. In a 13-gate circuit, each pendant input has one reader after ignoring unused NOT arguments. The two readers are distinct binary ORs.

## Lower bound

The pendant vertices are 2 and 3, attached to 5 and 6 respectively. On clearing 2, the remaining inputs in the order \((0,1,3,5,4,6,7)\) give exactly the seven-vertex edge function in `L_meta_10890_aux.final`. That theorem gives a lower bound of 12 gates over the unrestricted three-gate basis. Lean checks the relabeling for each leaf, using the reflection \((0\ 1)(2\ 3)(5\ 6)\) for vertex 3. Lean also proves the 13-gate lower bound and the two distinct OR-reader conditions for normalized circuits. [Accepted seven-vertex proof](https://github.com/open-goat/pequalnp-proofs/blob/a4e197c6a09356bd4ffa5f513bf729729e2ef76e/lean/PEqualNP/Outside/L_meta_10890.lean#L2707) · [Formal proof](LeafWheel29220.lean)

Each pendant input is essential, as witnessed by the pair consisting of that pendant and its neighbor. The output is a gate because the function rejects all singletons and accepts an edge. At least one gate therefore reads the pendant. Interpret invalid reads as the false constant, discard ignored NOT arguments and simplify constants in evaluation order. Setting the pendant to false removes any gate reading it. AND becomes false, OR becomes an alias or false, and NOT becomes true. The restricted function is nonconstant, so propagating these constants requires no output constant gate. Thus clearing either pendant saves at least one gate, and the lower bound is \(12+1=13\).

## Shape at equality

Every gate of a 13-gate circuit is in the output cone, since pruning anything would contradict the lower bound. For each pendant, two distinct gates reading it would both be removed on setting it to false, leaving at most 11 gates for the seven-vertex function. There is therefore precisely one reader after ignoring surplus NOT operands.

If that reader is an AND, a NOT, or an OR with no other operand, it becomes constant. It has another consumer because the restricted function is nonconstant. Propagating the constant through that consumer removes a second gate, which again leaves at most 11. This also excludes a duplicated pendant operand in the OR or an operand that is already constant. The unique reader must be a binary OR with a distinct other operand.

The two readers cannot be the same OR. Otherwise the inputs with only one of the two pendants active would be indistinguishable when the core bits are fixed. With just vertex 5 active in the core, pendant 2 gives an edge and pendant 3 does not.

Stripping the two ORs from a size-13 candidate leaves an 11-gate circuit for the six-vertex wheel. The reverse operation adds each OR to some of the later reads of its other operand. The reduction preserves the number of NOTs.

## AND count with at most one NOT

At least four AND gates are necessary, independently of the number of OR gates, for circuits with at most one NOT. For the finite check, first propagate constants. Store each input and each OR wire as a disjunction of the raw inputs and the preceding AND or NOT outputs. Inductively each operand of an AND or NOT has this form because OR just takes the union of its operands' supports. The output disjunction uses only AND or NOT outputs. A direct raw input in that disjunction would accept its singleton, which the edge function rejects.

A circuit with at most three ANDs and one NOT would give an instance of a model with four slots, one for NOT and three for AND. Unused slots can be ignored by every later disjunction and the output. Each operand stores an eight-bit raw input mask and bits selecting earlier slots. The four possible positions of NOT are excluded on explicit subsets of the 256 inputs. The Lean file verifies the Boolean calculation with `bv_decide`, which uses a SAT solver and native certificate evaluation. [Finite check](LeafWheelAndCount.lean)

Consequently, a 13-gate circuit using one NOT would have at most eight ORs. Its 11-gate wheel circuit after stripping the two leaf ORs would have at most six ORs.

## Operand tests after clearing the two leaves

In any backward-reading 11-gate circuit for this wheel with exactly one NOT, each binary gate has a truth table distinct from all earlier wires. If its value agrees with an earlier wire, redirect all its consumers and the output, if needed, to that earlier wire. This deletes one binary gate and retains the NOT. The resulting ten-gate circuit, with nine binary gates and one NOT, contradicts the accepted wheel theorem. [Alias elimination and the lower-bound application in Lean](LeafWheelCoreIrredundant.lean) · [Accepted signed-wheel lower bound](https://github.com/open-goat/pequalnp-proofs/blob/a4e197c6a09356bd4ffa5f513bf729729e2ef76e/lean/PEqualNP/Outside/L_meta_10788.lean#L8440)

For a binary gate with operand functions \(a,b\), there are wheel assignments with \((a,b)=(1,0)\) and \((a,b)=(0,1)\). If either assignment were absent, the AND or OR would equal one operand. This gives two necessary tests for every surviving binary gate with both pendants zero. Removing the two pendant ORs only redirects each of their outputs to its other operand. In the original thirteen-gate circuit, the same two tests therefore apply to every binary gate except the two pendant readers.

## Upper bound

A 14-gate monotone circuit computes the OR of the four terms

$$
x_5(x_0\lor x_2\lor x_6\lor x_7),\quad
x_6(x_1\lor x_3\lor x_7),\quad
(x_0\lor x_1)(x_4\lor x_7),\quad
x_4x_7.
$$

Lean checks the complete circuit on every input. The size-13 case remains open. [Circuit and verification](LeafWheel29220.lean)
