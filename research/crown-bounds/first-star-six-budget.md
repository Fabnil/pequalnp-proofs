# A neighbor bound with slack and the matching-deficient six-edge cases

For the deleted projective plane in [L-meta-9737](https://pequalnp.com/desk/row?gap=L-meta-9737), suppose exactly six edges of a minimum normalized circuit of size at most 58 lie outside the admissible raw AND stars. There are between eleven and fifteen distinct centers. If the star subgraph has no matching of size twelve, the projection-and-erasure bound cannot be tight with eleven or twelve centers. If there is an isolated line and eleven centers, at most four nonadmissible operand positions are raw-reachable, and if there are four they belong to two gates. With fourteen or fifteen centers the star subgraph has no isolated vertex.

## A bound that allows slack

Let $G$ be a graph without a four-cycle, of minimum degree at least one, and let $H$ be its subgraph of admissible raw stars for a minimum normalized monotone circuit. Take $n=|V(G)|$, and denote the set of distinct centers by $C$ and its cardinality by $c$. Let $\sigma$ count distinct oriented incidences, $w$ the nonadmissible operand positions reached by raw inputs, and $M$ the nonadmissible gates with both operands raw-reachable. Put

$$
\Delta=s-(\sigma+c-1+w).
$$

Suppose $k_0$, the number of isolated vertices in $H$, is at most $w$. For any vertex $v$ let $X$ be its neighbors in $G$ that are noncenters and use an edge outside $H$. Then

$$
|X|\le \mathbf{1}_{v\in C}+M+\Delta.
\tag{1}
$$

To show this, count repeated actual center slots by $R$, unions with an erased operand in raw ancestries by $A$, and unions outside those ancestries by $E$. Distinguishing actual center slots in the [projection count](first-star-five-cover.md#tracking-additional-positions) gives at least $\sigma+c+R-(n-k_0)$ retained unions. The erased count needs at least $w-k_0$ unions. Since there are $s+1-n$ unions in all,

$$
R+E+\epsilon\le\Delta,\qquad \epsilon=A-(w-k_0)\ge0.
$$

Track good center positions and raw-unreachable operand positions on the rejecting singleton at $v$. Suppose it fires $J$ of the $M$ gates. A raw double-reachable gate can emit one tracked position without consuming one. All other gates consume at least one tracked position. The [bound on newly emitted tracks](first-star-five-cover.md#tracking-additional-positions) allows at most $R+E$ additional positions from repeated slots and external unions. If $v$ is a center and has $m$ actual center slots, all $m$ are present initially and none can count as a newly emitted position later. In that case charge its $m-1$ repeats to the initial count and only the other repeats to the subsequent emissions. Thus the terminal tracked count is at most $\mathbf{1}_{v\in C}+J+R+E$.

The projected good leaves of the vertices in $X$ are pairwise disjoint. Two neighbors of $v$ already share that vertex, and a missing edge to $v$ does not supply one of its leaf positions. The [first-difference comparison](first-star-spanning.md#support-and-comparison-bounds-at-an-isolated-vertex) now divides the possibilities for accepting $(v,x)$ into the slots in the singleton's terminal tracked state and the $M-J$ fully raw-reachable gates not fired on the singleton. A waiting good center can read an extra leaf from at most one member of $X$. A waiting unreachable operand can read its erased raw mate from $x$. For an unfired gate with two raw-reachable operands, fix one absent operand in the singleton closure. If it is the first additional gate, that operand must be supplied by $x$.

To count the erased possibilities, let $P$ be the number of pure erased unions and $q$ the number of mixed attachments in the raw ancestries. Their pure erased network has $w+P$ vertices and $2P$ edges. Each of its weak components reaches at least one of the $q+k_0$ designated outlets, counting the empty inputs to mixed attachments and the isolated raw outputs with multiplicity. If a component has $r$ such outlets, every erased position in it can reach raw vertices of $X$ only via those outlets. Each outlet reaches at most one member of $X$, since their projected raw supports are pairwise disjoint and a mixed attachment propagates a common retained label. An isolated raw output is itself just one vertex. Thus any nonempty collection of erased possibilities from that component can add at most $r-1$ neighbors beyond its number of possibilities. The sum of $r-1$ over components is at most $q+k_0-(w-P)=\epsilon$, by the edge and vertex count. The total number served is at most

$$
\bigl(\mathbf{1}_{v\in C}+J+R+E\bigr)+(M-J)+\epsilon\le \mathbf{1}_{v\in C}+M+\Delta .
$$

This proves (1). At equality with $v$ a noncenter and $\Delta=0$, the earlier saturation count is recovered. In that case, if $|X|=M$, every one of the $M-J$ unfired fully raw-reachable gates has to be available as a first additional gate for some member of $X$, and exactly $J$ tracked positions must remain.

There is a useful strengthening at equality when $G$ is bipartite and all good centers are on one side. Even at a center $v$, $|X|\le M$. Otherwise reaching $|X|=M+1$ requires every track to contribute, starting from $C_v$, and every firing on the singleton must emit one tracked position. A good leaf can only be emitted from a raw support on the other side of the graph, which contains no tracked position. Thus no leaf is emitted, $h_v$ itself cannot fire, and the waiting center $C_v$ cannot be used by any member of $X$, whose edge to $v$ is missing. At least one of the purported $M+1$ possibilities is unavailable.

## Cover sizes at six deletions

Always $\sigma\ge42$ and $w\ge2$, hence $c+w\le17$ and $c\le15$. There is at most one isolated line. If there is one, restrict a shift matching that avoids the other two deleted edges to the eleven live lines. This gives a matching of size eleven. When there is no isolated line, the [Hall classification](first-star-five.md#the-matching-threshold) says that a matching of size twelve fails only if two lines keep just their edge to a common point, or two degree-three points are isolated. In those two cases the matching size is exactly eleven. Consequently $c\ge11$ and the possibilities for eleven centers are exhausted by the three cases below. In all cases $k_0\le2\le w$. Two isolated vertices can only be two degree-three points or an incident pair consisting of a line and a degree-three point.

### An isolated line

If $v$ is an isolated line and $c=11$, the center set consists of the other eleven lines. In fact, omitting $k>0$ live lines would require choosing $k$ point centers retaining at least $4k-2$ incidences of those lines. When $k=1$ a single point is insufficient for at least two retained edges. For $2\le k\le11$, the pair count on the chosen points would require $\binom{k}{2}\ge6(k-1)$, since their deficit from degree four is at most two. This is impossible.

All four neighbors of $v$ are noncenters, so (1) gives $4\le M+\Delta$. Here $\Delta\le6-w$ and $M\le\lfloor w/2\rfloor$. Thus $w\le4$, with $M=2$ required if $w=4$. Equality in the gate count would give $\Delta=0$ and $M\le3$, which cannot serve the four neighbors.

### Two lines with one retained common point

When two lines $u,v$ retain just their common point $p$, the only eleven-center cover consists of $p$ and the ten other lines. Indeed the omitted lines of an eleven-center cover form a Hall-deficient set. The only such set in this graph is $\{u,v\}$ by the six-deletion Hall classification. Both $u,v$ are noncenters, with three missing noncenter neighbors each.

If $\Delta=0$, (1) gives $M=3$, so $w=6$ and every raw-reachable erased position belongs to one of those three gates. Tight erasure gives one attachment for each position and places its raw set on one physical side. For an erased position reached in the singleton closure of $u$ that is raw-reachable on the line side, consider its gate at singleton $v$. If the position is absent there, the gate cannot have fired. It cannot be the first additional firing after adding a point neighbor either, since no point can supply that erased position. This violates the equality requirement for all $M$ gates at $v$. Hence the closure at $v$ reaches every line-side erased position reached at $u$. Together with their common retained leaf $L_p$, this includes the entire raw support of $u$. Raw-support dominance gives a contradiction.

### Two isolated degree-three points

The only eleven-center cover consists of the eleven live points, again by the deficient set classification. Each isolated point has three missing noncenter neighbors, all lines. If equality held, (1) would give $M=3$ and $w=6$ as before. Choose an erased position $e$ in the raw support of one of the isolated points $u$. Tight erasure makes it exclusive to raw $u$. All destinations containing $e$ have no tracked positions. A nonsingleton destination using it must lie in the pure erased raw support of $u$, since every union is used for a raw support.

At the other isolated point $v$, the three missing neighbors require equality in the tracking comparison, so every firing on singleton $v$ must emit one tracked position. No such firing can supply $e$, and its gate cannot be a first additional firing because the line neighbors cannot supply it either. This leaves one of the three gates unavailable at $v$, a contradiction. Thus neither of the two Hall-deficient patterns permits equality with eleven centers. In both cases $\Delta\ge1$ and $w\le5$.

## Matching deficiency with twelve centers

Now suppose $c=12$, $\Delta=0$, and there is no matching of size twelve. The budget gives $w\le5$ and $M\le2$.

If there is an isolated line, let $k$ count the omitted live lines. The $k+1$ point centers must cover at least $4k-2$ incidences of them, requiring $\binom{k}{2}\ge6k-12$. This excludes $3\le k\le10$. The case $k=2$ would require six incidences to three points across two lines, which have at most four by the common-neighbor bound. With $k=1$, both point centers must be on the omitted live line, so at most one lies on the isolated line. With $k=0$ there is only one point center. Both leave at least three missing noncenters at the isolated line, violating (1). With $k=11$ all centers are points and one point is unchosen. It must be isolated in $H$, and its at least three missing neighbors are all noncenters.

If two lines retain only their common point, let $r$ count omitted lines among the other ten, and $t\le2$ omitted lines of the special pair. The $r+t$ point centers must contain all incidences of the $r$ omitted full lines, so $\binom r2\ge6r-6t$ excludes $3\le r\le10$. For $r=1,2$, there are at most three or four chosen points respectively, too few for a full line or two full lines. Thus all ten full lines are chosen. If one special line is omitted, the only chosen point is the retained common point and all three missed neighbors of the omitted line are noncenters. If both special lines are omitted, the second chosen point can meet only one of the lines away from their common point. The other again has three missed noncenter neighbors. If neither is omitted, all centers are lines, and each special line has three missing noncenter neighbors. This contradicts the one-side strengthening of (1).

If two degree-three points are isolated, all remaining points keep their original degree and each line retains at least three neighbors because the isolated points have no common line. If $k$ lines are omitted, $k$ live points are chosen. The cases $k=1,2$ cannot contain three retained neighbors of a line. For $k=3,4$ two retained triples on at most four points would share a pair. For $k=5,6$ the retained triples of the omitted lines require at least $3k$ pairs of chosen points, more than $\binom{k}{2}$. At $k=7,8$ the incidence sum of the omitted lines into their chosen points is at least $4k-6$. For an incidence degree $d$ into the omitted line set, $\binom d2\ge2d-3$. The sum exceeds $\binom k2$ at $k=7$, and at $k=8$ the sum of the degrees exceeds $3k$, so at least one degree is four and the bound is strict, again giving more than $\binom k2$. At $k=9$ the inequality $\binom d2\ge3d-6$ forces all pairs of omitted lines to meet at a chosen point. Each isolated degree-three point then lies on at least two chosen lines, which is impossible with just three chosen lines because the two points have no common line. For $k=10$ the live point that remains unchosen needs all its at least three retained neighbors among two chosen lines, and $k=12$ would require twelve live points. With $k=11$ there is one chosen line, so at least one isolated point has all three missing neighbors unchosen.

The last possibility in this case is $k=0$, with all line centers. For an isolated point $v$, count together the tracked positions and all target leaves $L_\ell$ for $\ell\in N_G(v)$ ever emitted on its singleton. A support with a target leaf contains no tracked position and at most one target leaf, since it lies in one raw point support and any other point shares at most one line with $v$. As in the [five-edge isolated-point count](first-star-five.md#there-is-no-isolated-point), the combined count is at most $J$, the number of fully raw-reachable nonadmissible gates firing on the singleton. Adding a missing line either uses its target leaf, a waiting tracked position, or an unfired fully raw-reachable gate. Each of the latter possibilities can serve at most one neighbor since those lines have disjoint raw center slots and tight erasure permits no shared erased position across them. This serves at most $J+(M-J)=M$ neighbors, below three.

Thus no twelve-center case with matching deficiency attains equality.

## Isolated vertices at larger center counts

With $c\ge14$ there are at most three raw-reachable erased positions and one gate $g$ with both operands raw-reachable. Suppose there is an isolated vertex. There are at most $3-k_0$ erased unions, because the retained union count is at least $42+14-(25-k_0)$. If an isolated vertex lacks one of the two operands of $g$ in its raw support, every live neighbor must supply that operand. Those neighbors have disjoint projected good supports, so each requires a separate mixed attachment. For $k_0=1$ there are at least three such neighbors and at most two erased unions. For $k_0=2$ there are at least two live neighbors of each isolated vertex and at most one erased union. Both cases are impossible.

Both operands in the raw support of an isolated vertex require at least two pure unions by the [one-fork reduction](first-star-five-spanning.md#counting-the-supports-at-an-isolated-vertex). This is already impossible when $k_0=2$. With one isolated vertex those unions leave no mixed attachment for the missed edges away from it. Therefore $H$ spans at both fourteen and fifteen centers.

With fifteen centers the budget is tight and $w=2$. The [singleton-trigger argument](first-star-five-thirteen.md#equality-and-the-possible-placements-of-centers) puts the six missing edges at the leaves of a single good star, with distinct opposite endpoints. Every triggering vertex retains at least two edges. A chosen one needs its own assigned edge as well as its retained edge from the common star. An unchosen one with only the common edge would have its entire raw support contained in another trigger's support, contradicting dominance. In particular between three and four different vertices on the trigger side must account for the six misses, with at most two misses at each.

The six-edge exclusions above are conditional on the stated center counts or tightness. The existence of a circuit of size 58 remains open.
