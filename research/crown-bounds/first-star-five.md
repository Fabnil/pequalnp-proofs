# Five uncovered edges and saturation with twelve centers

In the deleted projective plane of [L-meta-9737](https://pequalnp.com/desk/row?gap=L-meta-9737), a subgraph omitting at most five edges still has a matching of size 12 if no line is isolated. This is sharp at six deletions.

Let $H$ be the union of the [admissible raw AND stars](first-star-cover.md) of a minimum normalized circuit on at most 58 gates. Suppose $H$ misses exactly five edges and no line is isolated. If there are twelve distinct centers and the projection-and-erasure bound is tight, the circuit has size 58. All its centers are lines, $H$ spans all vertices, and exactly two nonadmissible gates have both operand positions raw-reachable. These two gates account for all four raw-reachable operand positions outside the admissible stars.

## The matching threshold

All 12 lines have degree four in the original graph $G$. Points have degree three or four, only nine have degree four, and no line contains two degree-three points. Distinct lines have at most one common point. [Checked graph properties](PlaneRobustCover.lean)

If Hall's condition fails for $k$ lines, take a set of $k-1$ points containing their retained neighbors. Write $d_t$ for the number of these lines incident to a chosen point $t$ in $G$. With $j$ edge deletions the incidence sum is at least $4k-j$. Also $\sum_t\binom{d_t}{2}\le\binom{k}{2}$. If $j\le5$, the deficit $\sum_t(4-d_t)$ is at most one, so

$$
\binom{k}{2}\ \ge\ \sum_t\binom{d_t}{2}\ \ge\ 6(k-1)-3.
$$

The inequality fails for $2\le k\le11$. For $k=12$ it would require at least ten points of degree four, and $k=1$ requires an isolated line.

For $j=6$ the deficit is at most two and the analogous lower bound is $6(k-1)-6$. In the absence of an isolated line, only $k=2,11,12$ can fail Hall. If $k=11$, the three points outside the chosen set have at least eight incidences to those eleven lines. Each has at least three incidences there, except possibly one degree-three point on the omitted line that still has two. The eight incidences cannot all be removed. If $k=2$, each of the two lines must retain just its edge to their one common point. If $k=12$, the two omitted points must have degree three and lose all their edges. These two patterns are also sufficient to fail Hall and occur in $G$. The maximum matching then has size 11, since $4k-6>4(k-2)$ rules out a Hall deficit of two.

## Consequences of saturation

Write $c$ for the number of distinct centers, $\sigma$ for the number of distinct oriented star incidences, and $w$ for the number of raw-reachable operand positions at nonadmissible gates. We have $\sigma\ge43$, $c\ge12$ by the matching threshold, and $w\ge2$ because some edges do not fire a good gate first. In particular $c\le14$ and $w\le4$. Since there is no isolated line, at most one point can be isolated after five deletions. The projection-and-erasure bound reads

$$
s\ \ge\ \sigma+c-1+w.
$$

Assume equality in this bound. The [equality argument](first-star-three.md#consequences-of-equality) gives one admissible gate per center. Every union is used to compute a raw support, so any nonsingleton destination lies in a single raw support. By the [tight attachment count](first-star-four.md#budget-and-saturation), an erased position is either exclusive to the isolated raw port or enters the live raw supports through just one mixed attachment to a retained label.

Let $M$ be the number of nonadmissible gates with both operands raw-reachable, so $M\le\lfloor w/2\rfloor\le2$. Track the good center positions and the raw-unreachable operand positions in a singleton run. Every gate except those $M$ gates consumes at least one tracked position, and a destination contains at most one tracked position. Starting at a noncenter, at most $J$ tracked positions can be left after the singleton run fires $J$ of the $M$ gates.

### A constraint on missing neighbors of noncenters

Let $v$ be a noncenter and consider missing edges from $v$ to a set $X$ of noncenters. Their raw leaf projections are pairwise disjoint. A shared leaf label would give two of them a second common neighbor besides $v$, which is a noncenter. Their erased positions are disjoint as well, because a shared one would require a common retained label or would be exclusive to an isolated raw port.

Compare the accepting tests $(v,x)$ with the rejecting singleton $v$, using the [first additional gate](first-star-spanning.md#support-and-comparison-bounds-at-an-isolated-vertex). An additional good gate or a nonadmissible gate with an unreachable operand must take one of the tracked positions from the singleton's terminal support. The other operand must be supplied by $x$. A tracked position can serve at most one of the tests, because its mate occurs in at most one of the disjoint raw supports of $X$. A gate with two raw-reachable operands that was not fired on the singleton can also serve at most one test, since a fixed missing operand must come from $x$. Thus

$$
|X|\le J+(M-J)=M.
$$

## Twelve centers

### Every center is a line

If the centers omit $k$ lines they use $k$ points. At least $4k-5$ incidences of these lines must be on the chosen points. The pair count yields $\binom{k}{2}\ge6k-15$, ruling out $4\le k\le9$. For $k=3$ the sum is at most $k+\binom{k}{2}=6$, using $d\le1+\binom d2$, but it needs to be at least seven. For $k=10$ the pair count is tight and every pair of omitted lines already meets at a chosen point. An unchosen point then has at most one omitted line among its neighbors, and needs both chosen lines to have degree at least three. There are three unchosen points and two of them cannot share both lines.

If $k=1$, the omitted line retains just the edge to the one chosen point and has three missing neighbors that are noncenters. If $k=2$, at least three incidences from the omitted lines must be retained on the two chosen points, and the two lines have at most three such incidences in $G$ by the common-neighbor bound. So they retain all of these, split as one and two edges since no line is isolated, and the first line has three missing neighbors that are noncenters. If $k=11$, there are two unchosen points and only one chosen line. If either of those points has degree four, it has at least three missing noncenter neighbors. Otherwise the two degree-three points cannot both meet the chosen line, and the one that does not has three missing noncenter neighbors. If $k=12$, an unchosen point has at least three missing line neighbors and none is a center. Each of these alternatives violates $|X|\le M\le2$. This leaves $k=0$.

### There is no isolated point

Now all good centers are lines. Suppose $H$ isolates a point $v$. The raw supports of its line neighbors are pairwise disjoint, since they have distinct center positions, and the tight attachment count gives no shared erased position. Their only good raw positions are their respective centers $C_\ell$. In the singleton run at $v$, count both the pending tracked positions and the distinct target leaves $L_\ell$ ever emitted for lines $\ell$ incident to $v$. A support with a target leaf has no tracked position and contains at most one target leaf. It lies in some raw point support, and another point shares at most one line with $v$, while $v$ has no raw good leaves. So emitting a support adds at most one to the two counts combined before consumption. As before the combined count is bounded by $J$ on this singleton.

For a first additional good gate on $(v,\ell)$ the singleton closure must supply $L_\ell$. An incomplete nonadmissible gate must use a tracked position from the singleton, with its mate supplied by $\ell$. Each still-unfired nonadmissible gate with two raw-reachable operands can serve at most one test. Thus the number of accepted neighbors is at most $J+(M-J)=M$, below the degree of $v$. This excludes an isolated point.

### A single fully raw-reachable nonadmissible gate is insufficient

Suppose $M=1$, with gate $g$. Each erased position belongs to a single attachment, hence its live raw set is a single line or a subset of one line center's assigned point leaves. If either operand of $g$ has a raw line set, the corresponding line must occur in all five missed edges, which is impossible. Both sets therefore consist of points. Let $S$ be their intersection. Every missing point belongs to $S$ and triggers $g$ on its singleton. The set $S$ lies in the assigned leaves of a line $c_*$, so the missing lines are all distinct, all different from $c_*$, and each meets $S$ only at its missing point.

Each of the at most two other raw-reachable erased positions belongs to a different nonadmissible gate with one raw-unreachable mate. Such a position can appear at at most one raw line. Keep the missing edges at lines that supply none of those positions. At least three edges remain. On a kept edge $(x,\ell)$, adding the line to the raw point singleton adds just $C_\ell$. The first additional gate must be the good gate at $\ell$, so that gate is later than $g$ and the rejecting singleton at $x$ must reach $L_\ell$.

On a singleton $x\in S$, start with the common destination of $g$. There is at most one tracked position. It can offer a good gate, guarded by its leaf, or an incomplete nonadmissible gate, guarded by its other raw operand. A destination carrying good leaves has no tracked position and ends the run. A raw-unreachable operand of a gate whose two operands are raw-unreachable cannot continue a run by itself. Thus all kept points that reach target leaves follow the same sequence of offers to the same leaf destination $T$. For a fixed point $x$ the support $T$ can contain at most one leaf of a missing line at $x$. It is contained in a single raw point support, and two different points share at most one line. So the kept edges use distinct points.

For a kept line $\ell$, the three retained tests start with its good gate. The raw point is outside $S$ on each. After that gate consumes $C_\ell,L_\ell$, the common baseline is its destination. The extra raw good leaf sets of the three points are pairwise disjoint, and their only other relevant extras are the at most two erased positions of the incomplete gates. The baseline has at most one tracked position in its terminal support, since $g$ is earlier. If the baseline rejects, its one waiting position must have its mate supplied on all three tests. A good leaf cannot do this. Thus one of the at most two raw positions of incomplete gates would have to be present at all three retained points. The common retained label of its mixed attachment would then have to be $L_\ell$. Each such erased position can serve this role for at most one kept line.

There are at least three kept lines, so some kept line has a good gate whose destination alone accepts. Take a different kept point with that line. This is a nonedge, but its singleton reaches the same $T$, which contains the line's requisite leaf. Adding the raw line activates the good gate and accepts. The contradiction excludes $M=1$.

Thus $M=2$, $w=4$, and, because all centers are lines, $\sigma=43$. Equality gives $s=58$.

## The maximum number of centers

If $c=14$, the bound forces equality, $\sigma=43$, $w=2$, and a unique fully raw-reachable nonadmissible gate $g$ with operands $a,b$. An isolated point leaves at most one erased union in the raw ancestries. Its raw support cannot have just one of $a,b$, since its at least three neighbors would each need a separate mixed attachment for the other position. If it has both, the unique pure union gives the [factoring reduction](first-star-cover.md#spanning-in-the-three-edge-case). Thus $H$ is spanning here too.

The raw sets reaching $a,b$ are each confined to one physical side and to the leaves of one center when nonsingleton. If they were disjoint, they would be on opposite sides to trigger on any missed edge. The missing edges between the sets would form a matching of size at most four. A vertex distinct from the other set's center can meet that set in at most one edge, and a center has no missing edge to its assigned leaves. A singleton set also gives at most one such missed edge, by the same argument if the other set is nonsingleton. Five missed edges therefore require overlapping raw sets. Their intersection consists of singleton triggers in one good star's leaf set and accounts for all five missed edges, with five distinct endpoints on the opposite side.

The [follow-up](first-star-five-saturation.md) excludes the saturated twelve-center form with two fully raw-reachable nonadmissible gates. The other branches of the five-edge case and the existence of a circuit at size 58 remain open.
