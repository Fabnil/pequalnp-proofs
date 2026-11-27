# Two one-hot circuit budgets excluded by the single-fork search

The 5×5 table of mask 13730816 needs more than seven gates in [L-meta-20757](https://pequalnp.com/desk/row?gap=L-meta-20757). The 3×5 table of mask 3581 needs more than eight in [L-meta-20527](https://pequalnp.com/desk/row?gap=L-meta-20527). Both use the Desk's AND/OR model with one active input on each side.

A row wire is required if that row accepts a column rejected by another row. If the circuit omitted this wire, accepting the first row-column pair would imply acceptance with just the column turned on. Turning on the rejecting row preserves acceptance by monotonicity. The column version is symmetric. The required wire sets, with zero-based row indices followed by the column indices, are $\{2,3,4,5,6,7,8\}$ and $\{0,1,2,3,4,5,6,7\}$, respectively.

Normalize a hypothetical circuit by removing dead gates, constants, unary aliases and repeated operands. A nonconstant output still has an AND/OR circuit of no larger size. With $r$ raw wires and $g$ binary gates in its output cone, the sum of outgoing degrees above one over nonoutput wires is $2g-(r+g-1)=g-r+1$. Here the gate budget equals the number of required wires, so the sum is zero or one. With sum zero the output is a read-once formula, possibly using one additional raw wire in the 5×5 case. With sum one there is exactly one fork and precisely the required raw wires. Its input cone computes a read-once formula on a subset of these wires. Replacing the two outgoing uses of the fork by distinct formal leaves leaves a read-once formula on those two new leaves and the remaining raw inputs. If the fork cone contains every raw input, its two outgoing copies combine to the same signal and the output is again read-once.

The [formula search](read_once.py) computes the sets of possible output truth tables for every leaf subset up to the gate budget plus one, by partitioning into the two disjoint child leaf sets and applying AND or OR. It includes the optional wires in both input banks. The [single-fork search](single_fork.py) enumerates the leaf set of the fork cone and its possible truth tables. It then repeats the formula search with two formal leaves sharing that truth table and the other raw wires. Every lookup uses the entire promised truth table.

In this directory the following commands each report that there is no witness. Each search intentionally returns a nonzero exit code when it excludes the target.

```bash
python3 -B read_once.py 5 5 13730816 7
python3 -B single_fork.py 5 5 13730816
python3 -B read_once.py 3 5 3581 8
python3 -B single_fork.py 3 5 3581
```
