# Monotone circuit size for disjoint even cycles on the row-column promise

Let $G$ be a nonempty disjoint union of cycles $C_{2n_i}$, with $n_i\ge3$ and $N=\sum_i n_i$. Use the natural bipartition of each cycle as the row and column inputs. A monotone fan-in-two circuit must correctly test the edge when exactly one row and one column are active. Its size is at least

$$
2N-1+\left\lceil N/2\right\rceil .
$$

This bound is attained exactly when all cycle lengths occur with even multiplicity, or exactly one length has odd multiplicity and its half-length is odd.

For $k$ copies of a common cycle $C_{2n}$, the exact size is

$$
s(C_{2n}^{\sqcup k})=
\begin{cases}
5nk/2+1 & \text{if } n \text{ is even and } k \text{ is odd},\\
2nk-1+\lceil nk/2\rceil & \text{otherwise}.
\end{cases}
$$

In particular, a single $C_{12}$ takes 16 gates and a single $C_{16}$ takes 21 gates. The lower bounds allow arbitrary AND depth and sharing. The constructions have at most one AND on each input-output path. [Lean witnesses](CyclePromise.lean#L51) · [Bounds that count unpaired lengths in mixtures](cycle-mixtures.md)

## Circuits

Write the adjacency of $C_{2n}$ as row $i$ adjacent to columns $i$ and $i+1$ modulo $n$.

**Two copies of the same length.** In copies $A,B$, form $q_i=r^A_i\lor c^B_{-i}$ and $z_i=r^B_{-i}\lor c^A_i$. The minus signs denote negation of indices modulo $n$. Compute $\bigvee_i \bigl(q_i\land(z_i\lor z_{i+1})\bigr)$. Tests within either copy give the required edges, and cross-copy tests activate only one of the two families. The total is $2n+n+n+(n-1)=5n-1$.

**One copy of odd half-length.** Choose $d$ with $2d=1$ modulo $n$, and merge $r_i,c_{i+d}$ by OR. On the merged signals $x_i$ the edges are the pairs with indices differing by $d$ or $-d$. Since $d$ is invertible modulo $n$, this is the ordinary, undirected odd cycle on $n$ signals. A vertex cover of size $(n+1)/2$ can implement the edge test by stars centered at cover vertices. Assign each edge to exactly one chosen center. A star with $j$ assigned edges costs $j$ gates, including the binary OR of the leaves and the AND with its center. Joining the stars takes at most $(n-1)/2$ ORs. Together with the merging ORs this costs $2n+(n-1)/2$.

**One copy of even half-length.** For $n=4$, directly OR each row's two neighboring columns, AND with the row, and OR the four terms, for 11 gates. For even $n\ge6$ the following construction uses $5n/2+1$ gates.

All these circuits reject singleton inputs, both alone and as subcircuits of larger unions. Use pairs of copies of each length, and one remaining odd-half-length copy when allowed by the stated equality condition. Joining the outputs proves attainability in those cases. For even $n$ and odd $k$, use $(k-1)/2$ pairs and one single-copy construction.

### A single cycle of length divisible by four

Let $n=2r$ with $r\ge3$, and write the raw row and column inputs as $R_i,C_i$ for $0\le i<2r$. First build $r$ shared ORs

$$
P=R_r\lor C_0,\qquad Q=R_{2r-1}\lor C_r,\qquad
T_i=R_{r+i}\lor C_i\quad(1\le i\le r-2).
$$

For $0\le j<r$ define the two factors

$$
U_j=
\begin{cases}
R_j\lor C_{r+1+j} & 0\le j<r-2,\\
R_j\lor C_{2r-1} & r-2\le j<r,
\end{cases}
\qquad
V_j=
\begin{cases}
P\lor T_1 & j=0,\\
T_j\lor T_{j+1} & 1\le j<r-2,\\
T_{r-2}\lor C_{r-1} & j=r-2,\\
Q\lor C_{r-1} & j=r-1.
\end{cases}
$$

Take the output to be $(P\land Q)\lor\bigvee_{j=0}^{r-1}(U_j\land V_j)$. Each product has disjoint raw inputs in its two factors. Thus on a promised test it accepts exactly when the row and column occur in opposite factors. The possible products and accepted columns for each row are

| Active row | Products containing the row | Accepted columns |
| --- | --- | --- |
| $R_j$ for $0\le j<r$ | $U_j\land V_j$ | $C_j,C_{j+1}$ |
| $R_r$ | $P\land Q,\ U_0\land V_0$ | $C_r,C_{r+1}$ |
| $R_{r+i}$ for $1\le i\le r-2$ | $U_{i-1}\land V_{i-1},\ U_i\land V_i$ | $C_{r+i},C_{r+i+1}$ |
| $R_{2r-1}$ | $P\land Q,\ U_{r-1}\land V_{r-1}$ | $C_{2r-1},C_0$ |

This is the required cycle. The shared ORs cost $r$ gates, the factors cost $2r$, the products cost $r+1$, and the final OR costs $r$. Hence the total is $5r+1=5n/2+1$. The generator implements these formulas, checks its gate count for all $r\ge3$, and verifies the full promised tables at $r=3,4$. [Lean generator](CyclePromise.lean#L61)

## Counting union outputs

Use the [transposed OR network and consuming normalization](crown-all.md#transposing-the-or-graph). All $2N$ raw ports are essential with negative singleton tests. For a circuit of size $s$, let $h\le s+1-2N$ be the number of distinct nonsingleton union outputs after transposition and deduplication. A raw port has a start consisting of positions in the reversed graph. Call it a singleton port if its start has one position. Starts of size two can be chosen unmatched, by replacing an entire matched pair with its rule output as long as the start is a matched pair. They are then terminal. This preserves all tests and keeps the starts among the computed supports.

Neighborhoods on each physical side are incomparable, so the starts on each side are incomparable. Each position has at most one mate, the other operand of its AND, and an adjacent port of a singleton needs its mate in its terminal support. No adjacent ports are both singleton. If they were, their positions would be mates. The second neighbor of either singleton would need the other's position, which would contradict incomparability with that other singleton. Thus the singleton ports in each cycle form an independent set, of size at most $n_i$. Equality in a cycle forces the entire set to be one physical side. To see this, the $2n_i$ incidences at an independent set of $n_i$ degree-two vertices cover all edges, so its complement is also independent and the coloring of the connected cycle is determined.

Write $\delta$ for the deficit in the total singleton count from $N$. A nonsingleton start is shared if it is assigned to a port on both sides, and otherwise exclusive. Let $E$ count exclusive ports and let $m$ count union outputs assigned to no port. There are $N+\delta$ nonsingleton ports. Since each assigned output is used at most once per side,

$$
2h-N=\delta+E+2m.
$$

This gives the general lower bound. When $m=0$ and $E\le1$, all nonsingleton starts are pairs. A larger union would need a smaller nonsingleton operand. That operand could not be assigned on the same side as the larger start, by incomparability. If the larger start were shared, no side would be possible for the operand. If it were exclusive, both it and its operand would have to be exclusive, exceeding the allowance.

## Shared pairs in a cycle

Two facts will be used to test equality in the count.

First, on the raw ports with shared starts, exchanging the two ports for each shared start is a side-swapping graph involution. The two exchanged ports are nonadjacent because a test of two equal starts is a negative singleton test. Exchanging the sides preserves all edges because the result depends on the union of the two starts. A path component with an odd number of vertices needs a partner of the transposed orientation. A path with an even number of vertices cannot be fixed by this involution. Its only side-swapping automorphism reverses the path and exchanges the endpoints of its middle edge.

Second, when all the nonsingleton starts are pairs, treat each shared pair as one edge of a graph on support positions. This graph is the same whether its edges are enumerated from the row ports or from the column ports. In a cycle with $n$ singleton ports on one side, the $n$ opposite starts must be the consecutive pairs of the $n$ singleton mates in cyclic order. These pair supports form a cycle $C_n$ in the graph on positions. The sets of mate positions from distinct blocks on the same physical side are disjoint by incomparability. If there is one exclusive start in such a block, omitting its pair replaces the cycle by a path on $n$ vertices.

For a cycle below its full singleton count, consider the gaps of nonsingleton vertices between successive singleton ports in cyclic order. Every gap is nonempty, and the raw graph induced by all nonsingleton ports of that block is the union of the paths in the gaps. A gap with two nonsingleton vertices gives a boundary edge across which the singleton color changes, since the two singleton ports at its ends have distance three. If every gap has one or two vertices, the singleton ports occur in runs of one color, separated by those boundary edges. For a run of $j$ singleton ports, the $j-1$ nonsingleton vertices between adjacent singletons in the run have starts fixed to consecutive pairs of the $j$ mates. These supports give a path on those positions when $j\ge2$. A run of length one contributes no support edge of this type.

Suppose two boundary edges have all their endpoints shared and are exchanged by the involution. Their four endpoints form two shared pair profiles, each pairing a row endpoint of one edge with a column endpoint of the other. Such a profile requires the mate of each of the singleton neighbors of its two ports. These two required mates must be equal. Otherwise its pair consists of two positions whose mates both belong to the singleton starts. No shared start contains a singleton position on either side, by incomparability. Thus neither position of this pair can start any rule with another terminal shared start. This contradicts the boundary edge between the two profiles.

When all nonisolated nonsingleton ports come from such exchanged boundary edges, remove the shared profiles of their endpoints from the graph on positions. What remains consists of cycles from full blocks and paths from the singleton runs of the other blocks. This description holds on each orientation with disjoint position sets from different blocks and runs. If an exclusive start occurs in a full block or at an isolated port within a run, its edge is also omitted, cutting the corresponding cycle or path.

## Exact attainment of the general bound

At the lower budget, $h=\lceil N/2\rceil$. If $N$ is even, the counting identity makes $\delta=E=m=0$. All blocks have a full singleton side and all pair starts are shared. The graph of their pair supports is the same disjoint union of cycles on the two orientations. Consequently the counts of each length agree across the two orientations, and every length occurs an even number of times.

If $N$ is odd, then $\delta+E+2m=1$. With $E=1$ and $\delta=0$, all blocks have a full singleton side and a unique exclusive pair cuts one cycle in the graph of shared supports into a path. The other orientation gives only cycles, impossible.

The remaining case is $\delta=1,E=m=0$. Only one block is deficient. Within that block the nonsingleton vertices induce two edges, because deleting the independent set of $n-1$ singleton ports removes $2(n-1)$ of its $2n$ edges. If the two edges meet, their three-vertex path is the only such component and has no transpose partner. Otherwise the two edges are boundary edges and must exchange. All other gaps have one vertex. There is one run of singleton ports of each color. Remove the boundary profiles from the graph of shared pair supports. Each orientation now gives its full cycles and the path from one singleton run, possibly a run of length one with no edge. The two run lengths must agree, so the deficient block has $n-1$ singleton ports split evenly and $n$ is odd. The counts of full cycles of each length agree in the two orientations. This proves the claimed necessity, and the constructions prove sufficiency.

## Excluding the next budget for odd numbers of even-half-length copies

Take $k=2t+1$ copies with $n=2r$ and $r\ge2$. The general tightness criterion already excludes $h=nk/2$. Suppose there were a circuit with $h=nk/2+1=nt+r+1$. Now $\delta+E+2m=2$. At most $t$ full blocks can contribute their nonsingletons to either physical side, because each contributes $n$ and $r+1<n$. Thus $\delta=0$ is impossible, and $m=0$.

### One unit of singleton deficit

If $\delta=1$, then $E=1$ and all nonsingleton starts are pairs. The $2t$ full blocks must split evenly between orientations. The deficient block contributes $n+1$ nonsingleton ports with at most $r+1$ on each side, so its singleton counts are $r$ and $r-1$. Both colors occur. The two edges of its nonsingleton graph must therefore be disjoint boundary edges. If the exclusive port removed an endpoint of either, there would be one remaining edge in the shared graph, which could not exchange partners. Thus all four endpoints are shared and the boundary edges exchange.

Remove the two boundary profiles from the shared-pair graph. Omitting an exclusive start in any full block would produce a path on $n$ positions on that side, with no path of this length on the other side, whose singleton run has size at most $r$. Thus the exclusive port is within the deficient block and omits an internal pair from one of its singleton runs. The two sides have runs of lengths $r$ and $r-1$, so the omitted pair is in the longer run. For $r=2$ the boundary mate equality already fails, because the two endpoints of the longer run have different mates and the shorter run has a single mate. For $r\ge3$, the longer path must lose an end edge to become the shorter path, with the isolated endpoint omitted from the support-edge graph. But the boundary mate equality requires that endpoint also be an endpoint of the shorter run, contradicting equality of the remaining paths.

### Two units in one block

Now $E=m=0$. If one block has $n-2$ singleton ports, the $2t$ full blocks again split evenly, so the singleton counts in the deficient block are $r-1$ on each side. The nonsingleton graph has four edges. Its components are paths from gaps. Their nonzero edge counts form one of the lists $(4)$, $(3,1)$, $(2,2)$, $(2,1,1)$, and $(1,1,1,1)$.

With one path of four edges, or two paths of two edges, every gap has odd vertex count, so the singleton ports would all have the same color. With paths of three and one edges, each has even vertex count and no partner of its own size. With paths of two, one and one edges, the three-vertex path has no transpose partner.

In the last case all four nontrivial components are boundary edges. They exchange in pairs. Remove their shared profiles from the graph on positions. The internal pair supports of the deficient block are paths from its singleton runs. Equality of the support-edge graphs shows that every mate position in a run of length at least two occurs in such a run on the other side of the same block. For a singleton run of length one, its mate must also occur among singleton mates on the opposite side of that block, by the boundary mate equality. Thus every singleton in the deficient block is paired by its singleton position with a singleton on the other side. The boundary nonsingletons pair with each other. The internal nonsingletons also pair within the block, since their shared pair supports are path edges rather than any full-block cycle edge.

The full set of these equal starts would define a side-swapping, nonadjacent-pair involution on the original cycle $C_{2n}$. A cycle automorphism is either a rotation or a reflection, determined by the images of one vertex and its next neighbor. The only possible nonidentity involutive rotation is rotation by $n$, which preserves sides when $n$ is even. A side-swapping reflection has the form $i\mapsto c-i$ with $c$ odd. It interchanges the adjacent vertices $(c-1)/2$ and $(c+1)/2$, violating the nonadjacent-pair requirement. This excludes the last case.

### Two blocks deficient by one each

The $2t-1$ full blocks are split $t$ to $t-1$ between orientations. In either deficient block the two nonsingleton edges are a three-vertex path or two boundary edges. A single three-vertex path would have no transpose partner. If there are two, they need opposite orientations. In each such block all singleton ports lie on one side, since its gaps have odd vertex counts. The two blocks would then contribute $n+1$ nonsingleton ports on each side. This exceeds the $r+1$ available on the side already receiving $t$ full blocks.

Finally suppose both deficient blocks have two boundary edges. Remove the shared profiles of all their endpoints. The remaining graph on positions has paths from singleton runs and exactly the cycles from full blocks. Its equality on the two sides requires equal counts of full cycles of each length, contrary to the split $t$ to $t-1$.

This rules out $h=nk/2+1$ and gives $s\ge5nk/2+1$. The single-copy circuits of size $5n/2+1$ and the $(5n-1)$-gate pair circuits attain it.
