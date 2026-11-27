# Excluding four uncovered edges at the 58-gate budget

For the deleted projective plane in [L-meta-9737](https://pequalnp.com/desk/row?gap=L-meta-9737), the [admissible raw AND stars](first-star-cover.md) of any minimum normalized monotone circuit of size at most 58 leave **at least five edges** uncovered. We exclude exactly four below. The [earlier argument](first-star-three.md) excludes at most three.

## Accounting for the last union

Suppose the star subgraph $H$ misses four edges. The [spanning result](first-star-spanning.md) and the [four-edge budget](first-star-thirteen.md) give size 58, 44 singly oriented edges in $H$, and 12 distinct centers. All twelve lines are centers, or eleven lines and one point are centers. There are exactly two raw-reachable operand positions away from the admissible stars. They are the two operands $a,b$ of one nonadmissible gate $g$, which is the first firing gate on every missing edge. All other nonadmissible gates have both operands raw-unreachable.

Write $R$ for the number of admissible gates in excess of the 12 distinct centers. In the [projection count](first-star-cover.md#projection-to-the-star-incidences), distinguish the actual center positions even at a repeated center and still identify the leaf positions by their center. Each actual center position is raw-reachable only at its one center vertex. Hence different raw supports still project to sets that intersect in at most one label. Their projected sizes now sum to $56+R$. All 25 are nonempty. The retained count requires at least $31+R$ unions in the ancestry of raw supports.

Let $A$ count the unions in those ancestries having an erased operand, and let $E$ count the unions unused by any raw support. The [erasure count](first-star-cover.md#charging-the-erased-positions) gives $A\ge2$. Hence

$$
31+R+A+E\le34,\qquad R+E\le1.
$$

Track the positions that are either good center positions or raw-unreachable operands. Every gate after $g$ consumes at least one tracked position. An emitted support belonging to the ancestry of a raw support contains at most one tracked position, except that when $R=1$ it can contain the two center positions of the single split star. In that case every such emission with two tracked positions uses the same pair. When $E=1$, the one exceptional union can combine two single positions or raw-ancestral supports, each with at most one tracked position. Again there is at most one pair of tracked positions that can be emitted together. Succeeding emissions of that pair add neither position anew. A position that was emitted already remains present until its gate reads it, and a later gate cannot emit a position already consumed.

It follows that a continuation starting with the output of one gate and with no other tracked positions can have at most two tracked positions at any time, provided $g$ has already fired or is too early to run. The first emission of the possible pair accounts for the one increase beyond one tracked position. This includes the case where the pair is present in the starting destination.

We use the [first-difference comparison](first-star-spanning.md#support-and-comparison-bounds-at-an-isolated-vertex). If a baseline rejects and becomes accepting when some raw leaves are added, a first additional gate must use one of the added leaves and a center left unconsumed in the baseline. Disjoint added leaf sets thus need distinct waiting centers. More generally, adding a single center to a rejecting baseline can change the result only if its own gate has not fired and the associated leaf is already in the baseline closure.

## Eleven line centers and one point center

The omitted line $\ell_0$ keeps one edge to the chosen point. Its three missing neighbors $x_1,x_2,x_3$ are noncenters. Their projected raw leaf sets are pairwise disjoint, since any common leaf label would give the corresponding pair of points a second common line besides $\ell_0$.

The raw support at $\ell_0$ contains both $a,b$. Otherwise the missing position must reach all three $x_i$. It needs a different mixed attachment to the retained projection for each $x_i$, since the attachment contributes a common retained label to all raw supports that use it. This would use all three available erased unions, leaving no pure erased union to combine $a,b$. Each of the three mixed attachments would therefore have an erased operand containing just the same missing position. The other position would have no mixed attachment to any of the 25 live raw supports, contrary to its raw reachability.

The singleton at $\ell_0$ now fires $g$ and starts with no tracked positions outside its destination. The three missing edge tests add only the respective good leaf sets once $a,b$ have been consumed. To differ from the rejecting singleton on all three tests requires at least three waiting centers. The bound of two excludes this distribution.

## All twelve line centers

### Which missing edges trigger on a singleton

In this case a mixed attachment can supply only one raw line, or a subset of the assigned leaves of one line center. This follows from the retained label common to all raw supports reached through the attachment. We show that all four missing edges have point endpoints in one such set $B$ of assigned leaves, and at least three fire $g$ on the point singleton. If $R+E=1$, all four do.

First suppose some mixed attachment carries both $a,b$ in its erased operand. Choose the folds in the transposed network to start with a retained contribution at every wire that has one. A pure erased union then occurs only at a forward wire with entirely erased support. If there is only one pure erased union in the ancestry of the raw supports, the union that joins $a,b$ identifies a raw-reachable wire with full support $\{a,b\}$. Its forward OR-only paths have just one fork and no destinations other than the two operands of $g$. The [absorption or factoring reduction](first-star-cover.md#spanning-in-the-three-edge-case) saves a gate. Thus a mixed attachment carrying both positions uses at least two pure erased unions. At most one mixed attachment remains, and both positions can reach raw vertices only through it. Its raw set must consist of points, since a single line cannot account for all four deletions in the spanning subgraph. This is the set $B$.

Otherwise every mixed attachment carries just one of $a,b$. There are at most three, so one position, say $b$, has a single mixed attachment. Its raw set cannot be one line for the same reason. Thus it is a point set $B$ in the assigned leaves of a line $c$. In either case every missing edge uses a point in $B$, its line differs from $c$, and its line has at most one neighbor in $B$. The four missing lines are therefore distinct.

In the case of separate attachments, $a$ can have at most two. It needs one on the point side, since two line attachments could not cover all four different missing lines. Thus at most one missing line can supply $a$. All other missing edges get both $a,b$ from the point singleton. With $R+E=1$ the erased count is tight at $A=2$, so there is no line attachment for $a$ in this case. The case of a combined attachment already makes every missing point a singleton trigger.

### Target leaves for the ordinary missing lines

Keep the missing edges that fire $g$ on the point singleton and whose line has a single good gate. There are at least three. If $R=0$, at most one missed edge is lost by the singleton restriction. If $R=1$, all four have singleton triggers and at most one of their lines has a split star. Let $Q$ consist of the target leaves $L_\ell$ for the kept lines, one distinct leaf for each. Let $X\subseteq B$ consist of the points of the kept edges.

For a kept edge $(x,\ell)$, the only addition to the singleton at $x$ beyond the consumed $a,b$ is its line center position $C_\ell$. The positive edge test must fire the good gate $h_\ell$ as its first difference. Thus $h_\ell$ follows $g$ in the gate order and the singleton at $x$ reaches $L_\ell$.

The destination of $h_\ell$ suffices to accept by itself. The line has three retained edges, all to points outside $B$. On each such test $g$ is initially disabled and $h_\ell$ is the unique first firing gate. After $h_\ell$, the three tests share its destination and differ only by their remaining raw leaf sets. The erased positions can be ignored since $g$ is earlier. The three extra sets are pairwise disjoint because their points already share $\ell$, whose unique leaf position was consumed. If the destination alone rejected, the three positive tests would require three waiting centers by the first-difference comparison. The bound of two proves the claim.

Consequently, for $x'\in X$ different from $x$, the singleton run at $x'$ cannot reach $L_\ell$. Otherwise adding $C_\ell$ would fire $h_\ell$ and wrongly accept the nonedge $(x',\ell)$. On the singleton runs of $X$, every emission of a leaf from $Q$ must occur at the one point incident to its missing edge. A destination contained in a single raw point support can contribute at most one leaf of $Q$ across all these runs. If the supporting point is the point of the run, it has none of its missing leaves. If it is a different point, those two points share at most one line.

### Counting the emissions after the first AND

After $g$, a destination is normally a singleton center position, a set of leaves in one raw point support, a singleton raw-unreachable position, or the output. The reason is that a raw line support has only its center positions and possibly earlier erased positions, and a raw point support has only leaf and earlier erased positions. The only possible exception is one fixed support $U$. When $R=1$ this is the pair of center positions at the split line. When $E=1$ it is the result of the one union outside raw ancestries. When neither holds there is no exception. On a rejecting singleton no emission can include the output.

Until the first emission of $U$, every run at a point in $X$ starts with $g$ and has at most one tracked position. After a leaf-only emission it cannot continue, because the last center was consumed. A single raw-unreachable position without a mate also stops the run. Thus all the runs that obtain a target leaf follow the same succession of center offers until a common leaf-only destination or the first emission of $U$. A missing leaf can stop this sequence but cannot select a different gate. If none reaches $U$, at most one raw point destination is used to emit target leaves.

If some run reaches $U$, every run in $X$ must also reach it through that common sequence before any target leaves have been emitted. The split-line support contributes no leaf. In the other exceptional case $E=1$, all four edges were kept, and there are at least two distinct points in $X$, since $H$ spans and a point loses at most three edges. If $U$ carried any target leaf, it would supply that leaf on every run in $X$, which would accept a nonedge. Thus $U$ contributes no target leaf. Subsequent emissions of $U$ contribute no new positions and can be treated as having an empty destination.

After $U$ is emitted, at most two tracked positions are pending. Follow each of these positions through the fixed successor whenever its center gate emits one new center position. Such a path is deterministic and strictly forward in the gate order. Leaf guards can delay or stop a path but cannot change its successors. A path terminates when its gate emits a leaf set, a raw-unreachable position, or nothing new. Paths may coalesce without creating another path. If a nonadmissible gate fires on two raw-unreachable positions, those positions must be the endpoints of both paths. In that case neither path has a leaf-set endpoint, and the nonadmissible gate can start at most one further path. A single path cannot enable a further nonadmissible gate, because its two operands would both have to be raw-unreachable. This shows that across all runs in $X$ there are at most two possible normal leaf-set destinations. They contribute at most two target leaves by the previous section. Since $|Q|\ge3$, this is impossible.

The all-line distribution is excluded as well. A minimum circuit of size at most 58 would have to leave at least five edges outside the admissible stars. The [five-edge analysis](first-star-five.md) restricts the tight twelve-center case. The existence of a 58-gate circuit remains open.
