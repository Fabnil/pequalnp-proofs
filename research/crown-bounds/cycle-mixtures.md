# A lower bound that counts unpaired component types

Let $G$ be a nonempty disjoint union of connected $d$-regular bipartite graphs for one fixed $d\ge2$. Assume that the neighborhoods of different vertices on the same physical side are distinct. Write $N$ for the size of each side of $G$, and $u$ for the number of connected component types that occur an odd number of times. A type here identifies a graph with its transpose. Then monotone fan-in-two size on the one-row/one-column promise satisfies

$$
s(G)\ \ge\ 2N-1+\left\lceil (N+u)/2\right\rceil.
$$

For cycles $C_{2n_i}$ with $n_i\ge3$, let $u_o,u_e$ count the types of odd multiplicity with odd and even half-length, respectively. The bound and the [single- and paired-cycle constructions](cycle-promise.md#circuits) give

$$
2N-1+\left\lceil (N+u_o+u_e)/2\right\rceil
\ \le\ s(G)\ \le\
2N-1+(N+u_o)/2+2u_e .
$$

In particular, this gives the exact size for arbitrary mixtures with $u_e=0$. For instance $C_6\sqcup C_{10}\sqcup C_{14}\sqcup C_{18}$ needs 61 gates. The 61-gate construction is checked against all 576 promised cells in Lean. [Lean witness](CyclePromise.lean#L163)

For even $N$, any unpaired type of even half-length imposes at least two gates above $2N-1+N/2$. In particular, $u_o=0,\ u_e=1$ gives exact size $5N/2+1$, with no restriction on the lengths of the paired components.

## Counting unpaired regular components

Use the [transposed OR network and terminal supports](crown-all.md#transposing-the-or-graph). For a circuit with $s$ gates let $h\le s+1-2N$ count its distinct union outputs of size at least two. Equal starts are normalized the same way. Starts of size two are terminal, since an initially matched pair can be replaced by the destination of its rule. Same-side neighborhoods and starts are antichains. Each position has a unique mate if it is an AND operand. A neighbor of a singleton port needs its mate in its terminal support.

No two singleton ports are adjacent. If they were, their positions would be mates, and a second neighbor of either would have to contain the other's singleton position, contrary to incomparability. Thus a component with $n$ vertices per side has at most $n$ singleton ports. If it has $n$, call it full. The $dn$ incidences at the singleton ports of a full component cover all edges and the complement is independent. Connectivity implies that the singleton set is an entire physical side.

Let $\delta$ be the total singleton deficit from $N$. The $N+\delta$ nonsingleton ports each use one of the $h$ union outputs. An output is shared if used on both sides, and a nonsingleton port is exclusive if its output is used only on its side. Let $E$ count the exclusive ports and $m$ count the unassigned outputs. Then

$$
2h-N=\delta+E+2m.
$$

### Required mates of shared profiles

A shared profile is the pair of raw ports on opposite sides that use the same nonsingleton start. For a profile $p$, let $L(p)$ be the union of the required mates of the singleton neighbors of its two raw ports. These mates persist in its terminal support. If a singleton position occurs on both physical sides, the adjacent shared profiles are the same from either side. This follows by testing its singleton start together with the corresponding shared start. Therefore any one mate position appears in $L(p)$ for at most $d$ distinct profiles.

Call a profile enlarged if $|L(p)|\ge d+1$. We use the saturation argument for shared starts with the useful positions taken to be **all** singleton mates, from both orientations. If a start has size at least three, it is a union of two admissible helpers or one helper and a position. These helpers are unassigned union outputs whose supports contain no singleton start, output position, or assigned nonsingleton start. Their nonsingleton operands are admissible as well. Monotonicity and the same-side antichains exclude a raw singleton position from the single-port run of a shared profile on either side. A rule firing in that run can emit only an admissible helper or an allowed singleton position. Emitting any other assigned start would violate incomparability, or the rule order for the profile's own start.

Write $W$ for the union of the admissible helpers. It has at most $2m$ positions, since their union gates introduce at most two fresh positions each. From $W$ or $W$ plus one position, suppress all rules with destinations in $W$, which changes no ordinary closure from these seeds. The remaining rules emit single positions. Useful positions cannot be consumed, because their mates are excluded singleton positions. If the consuming run from $W$ produces $v$ new useful positions and begins with $a$ auxiliary positions, it ends with at most $a-2v$ auxiliary positions. After the run, an extra useful position contributes itself. An extra auxiliary position can fire only via one of the remaining auxiliary mates, and its run adds at most one useful position. Each firing in that run spends at least one position outside the original terminal set and emits at most one, so the extra position cannot branch. Include in $K$ the useful positions of $W$, the $v$ produced from $W$, and the additional useful positions from the at most $a-2v$ auxiliary extras that can start a rule. Then $|K|\le |W|-v\le2m$. For every shared start of size at least three its useful terminal positions are in $K$ with at most one exception, by monotonicity of ordinary closure. This is the [same saturation argument](crown-all.md#saturation-of-helper-supports) with the useful set enlarged.

An enlarged profile has at least three required mates and so starts at size at least three. At least $d$ distinct positions of its $L(p)$ are in $K$. As each position of $K$ can be required by at most $d$ profiles, the number $X$ of enlarged profiles satisfies $X\le |K|\le2m$.

### Pairing the components

Call a component clean if it is full and all its nonsingleton ports are shared. A clean component in which every singleton position occurs on the opposite physical side has a partner of the same type. Pair its singleton ports by equal positions and its nonsingleton ports by their shared starts. Every edge maps to an edge in the opposite orientation. Since both graphs have degree $d$ at every vertex, the image contains every neighbor of each image vertex and so is a whole connected component. It is clean, with the singleton side reversed. It cannot be the original component because that component has singletons on only one side. Equal starts give an involution on these paired clean components.

Each remaining clean component has a singleton position absent from the opposite side. Choose one such singleton $q$. Its $d$ neighbors are shared profiles. In each of these profiles call the raw counterpart of the neighbor $v$. The shared port in the clean component is isolated in the induced graph of shared nonsingleton ports. Exchanging shared profiles across sides preserves edges of that graph, so $v$ is also isolated there.

If $v$ has $d$ singleton neighbors, their mates and the $d$ mates required on the clean side have a union of size at least $d+1$. Indeed they cannot use the mate of $q$, because $q$ does not occur as a singleton position on their side. Charge this incidence to an enlarged profile. Otherwise $v$ has some nonsingleton neighbor. That neighbor is exclusive, since $v$ is isolated in the shared graph. Charge this incidence to an edge from $v$ to such an exclusive port. The exclusive port is in a non-full component, since a full component has no edges between nonsingleton ports.

Each enlarged profile receives at most two charges, one from each orientation. Each exclusive port in a non-full component receives at most $d$, one per neighbor. In fact each raw $v$ can arise at most once, because only one singleton was chosen per clean component and its neighbors determine distinct counterparts. Thus the number of remaining clean components is at most $2X/d+E_{\rm nonfull}$. There are at most $\delta$ non-full components and at most $E_{\rm full}$ full components with exclusive ports. Removing the clean pairs leaves at least $u$ components and yields

$$
u\ \le\ \delta+E+2X/d\ \le\ \delta+E+4m/d\ \le\ 2h-N .
$$

The claimed circuit lower bound follows.

## The first extra gate for an even total half-length

For cycles with even $N$, suppose $h\le N/2+1$. We show that every type of even half-length occurs an even number of times. Together with the lower bound just proved, this classifies when at most one gate above $5N/2-1$ suffices. Either all type counts are even or there are two odd type counts, both with odd half-length. In the latter case use the two single-copy constructions and pair all remaining copies of every length.

At $h=N/2$ the result follows from the [equality case of the basic bound](cycle-promise.md#exact-attainment-of-the-general-bound). At $h=N/2+1$ we have $\delta+E+2m=2$.

### No unassigned outputs and no exclusive ports

When $m=E=0$, all nonsingleton starts are shared terminal pairs. The shared nonsingleton graph has the side-swapping involution that exchanges the two raw ports of each profile. Each singleton position occurs across both sides as well. To prove this, take a neighbor $v$ of a singleton. If $v$ has two singleton neighbors, its counterpart is also isolated in the nonsingleton graph and also needs two mates. The two required pairs coincide. If $v$ has just one singleton neighbor, its counterpart also has exactly one. The two required mates in their common pair must coincide, as otherwise neither position can start a rule with any shared terminal start, contrary to an edge in the nonsingleton graph. This is the [boundary mate argument](cycle-promise.md#shared-pairs-in-a-cycle), applied to any nonisolated profile with one singleton neighbor on each side.

Consequently equal starts now exchange all the raw ports. This gives a side-swapping involution of the entire graph exchanging only nonadjacent pairs. Such an involution cannot fix a cycle with even half-length. The only involutive rotation other than identity preserves sides for that half-length, and a side-swapping reflection exchanges the endpoints of an edge. Thus the even-half-length cycles pair by type.

### All components full

If $m=1$ and $E=\delta=0$, consider the two graphs on shared profiles obtained by joining the two neighbors of each singleton port. In each orientation this is a union of cycles, with the edges labeled by the singleton mates. A label occurring in both orientations has the same endpoints. Given a profile, the union of the labels incident to it in both graphs is exactly $L(p)$. If any incident label sets differ, a label from just one orientation has both endpoints enlarged. Therefore $X\ge2$. The bound $X\le |K|\le2m=2$ implies there are two enlarged profiles and two positions in $K$, both required by both profiles.

The labels of the two positions in $K$ cannot both occur in a single orientation. They would have the same two neighboring profiles there, and those would be the entire equal neighborhoods of two distinct singleton ports on that side. Hence one label occurs exclusively in each orientation. Each enlarged profile has at most one label outside $K$, so its other incident label must be common to both orientations. All other profiles have the same incident labels on both sides. Replacing the one exclusive label on one side by the other exclusive label preserves the graph, since each joins the same two enlarged profiles. The lengths therefore pair, as they also do if no incident label sets differ.

If $E=2$ and $m=\delta=0$, every shared start is a pair. In the graph whose edges are shared pair supports on positions, an exclusive port removes a required edge from the cycle of its full component. If both removals are on the same side, there is still at least one path on that side, since every full cycle before removal has at least three edges. The other side gives only cycles. Thus there is one omission per side. The two paths of shared pairs must have the same length, which pairs their original cycle types. The remaining full cycles pair directly.

### One deficient cycle and one exclusive port

Here $\delta=E=1$ and $m=0$, so every nonsingleton start is a pair. The deficient cycle has two edges between its nonsingleton ports. If they meet, their three-vertex path has no transpose partner unless a vertex of the path is exclusive. Removing a leaf would leave a unique two-vertex path, which cannot be fixed by the shared-profile involution. Thus its center is exclusive. All singleton ports of the deficient cycle are then on the same physical side. On their mate positions the internal shared pairs form a path on $n-1$ vertices if the deficient cycle has half-length $n$. The two leaves of the raw three-vertex path each require the mate of one endpoint singleton of the run. On the other orientation the graph of shared pair supports consists only of full cycles. Thus the two leaf pairs must extend the path through one common new position to close a cycle of length $n$ on the support positions. No already internal position of a path or a full cycle can serve as an extra endpoint because it already has degree two. A direct edge between the path endpoints would leave no room for the other distinct required edge. The two orientations therefore pair all lengths, treating the deficient block as contributing this cycle of length $n$.

If the two nonsingleton edges are disjoint, neither may lose an endpoint to exclusiveness. Otherwise there is only one remaining nontrivial component, a two-vertex path, in the shared graph. Thus the two edges exchange and the [boundary mate equality](cycle-promise.md#shared-pairs-in-a-cycle) identifies the two endpoint mate sets of their two singleton runs. Remove the boundary profiles and compare the two graphs on support positions. If the exclusive port is in a full block, its side has a path from the opened full cycle in addition to the path of its own run. The other side has only its run path. Equality of the nontrivial paths requires a run of length one on the side with the opened cycle and a run of length at least three on the other. Their endpoint mate sets cannot agree. If the exclusive port is in the deficient block, one run path loses one edge. To equal the other path, the longer run has one more vertex and must lose an end edge, leaving one endpoint isolated and absent from the edge graph. The endpoint sets then differ. If the shorter run has length one, its single endpoint mate cannot coincide with both distinct endpoint mates of the longer run. This also contradicts the boundary mate equality.

These exhaust the budget $h\le N/2+1$ for even $N$. In particular, one unpaired even-half-length cycle with all other types paired requires $h\ge N/2+2$, and the explicit constructions attain that bound.
