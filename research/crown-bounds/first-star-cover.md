# Lower bounds from the stars that can activate before other AND gates

Let $G$ be a simple graph without a four-cycle. Consider a monotone fan-in-two circuit that computes the edge predicate of $G$ on all inputs of weight at most two. The argument applies in particular to circuits computing the edge predicate on every input.

Remove isolated vertices by setting them to zero and normalize the circuit to binary gates with distinct earlier operands in the output cone. Write $n$ for the number of nonisolated vertices and $s$ for the size of this circuit. For an AND gate $g$, let $A_g,B_g$ be the sets of raw vertices reaching its two operand positions along OR-only paths. Call $g$ admissible for the star count if both sets are nonempty, they are disjoint, and every pair in $A_g\times B_g$ is an edge of $G$. One set is then a singleton by the absence of four-cycles. Regard its raw vertex as the center of the star, choosing either endpoint when both sets have size one.

Let $H$ be the union of these stars, with $\tau(H)$ the vertex-cover number. Let $w$ count the distinct operand positions of all other AND gates that have a raw OR-only path to them. Then

$$
s\ \ge\ |E(H)|+\tau(H)-1+\max\!\left(w,\ n-|V(H)|\right).
\tag{1}
$$

Here $V(H)$ denotes the vertices touched by the stars. In particular, if these stars cover $G$, then $s\ge |E(G)|+\tau(G)-1$. This condition concerns only raw OR paths into AND operands. The circuit may have later AND activations on negative tests.

## Projection to the star incidences

Cut the AND gates and transpose the OR network as in the [support-set construction](crown-all.md#transposing-the-or-graph). The reversed graph computes the sets of reached positions $D(v)$ for every raw vertex and for every AND-output source. Its number of binary unions is $h=s+1-n$. Each $D(v)$ for a raw vertex excludes the final-output position because the singleton test is negative.

For every distinct center $c$ used by an admissible gate, create two labels, one for its center and one for its leaves. Project the center operand position of every admissible star with center $c$ to the center label, and its leaf operand to the leaf label. Erase all other positions. This map, denoted by $\pi$, preserves unions on sets. Let $\sigma$ count the distinct oriented center-to-leaf incidences of the stars and let $c_0$ count their distinct centers. The projected raw sets have total size $\sigma+c_0$. They are nonempty exactly on $V(H)$.

Any two distinct projected raw sets intersect in at most one label. A center label belongs to only its center. Sharing two leaf labels would give the two raw vertices two distinct common neighbors in $G$, a four-cycle. After collapsing unions with an empty projected operand, each raw output $D'(v)=\pi(D(v))$ of size at least two requires at least $|D'(v)|-1$ binary unions with projected support of size at least two. To see the count, cut its ancestor graph at operands of projected size one, treating these as sources. The connected graph computes at least $|D'(v)|$ distinct source labels. With $g$ binary union nodes and $k$ sources it has $2g$ edges, hence $2g\ge k+g-1$. The union nodes counted for different raw vertices are disjoint, since a projected support of size at least two cannot be a subset of two different raw outputs. The total retained count is at least $\sigma+c_0-|V(H)|$.

## Charging the erased positions

Put $k_0=n-|V(H)|$. Call a union mixed if it has one empty and one nonempty projected operand. Each mixed union collapses after projection. Count only mixed unions used in computing raw outputs, and call their number $q$.

Consider the empty-projection subnetwork leading to the empty operands of those $q$ unions or to the $k_0$ empty projected raw outputs. It has all $w$ erased source positions that appear in a raw $D(v)$. Indeed every path from such a source to a nonempty raw output first crosses a mixed union, and every path to an empty raw output stays in the empty subnetwork. Each weak component of this subnetwork reaches one of its at most $q+k_0$ designated outputs. The binary union count in it is consequently at least $w-q-k_0$: with $g$ union nodes it has $w+g$ vertices and $2g$ edges, and at most $q+k_0$ connected components. All those unions collapse too. Including the $q$ mixed unions, at least $w-k_0$ unions collapse, or zero if that bound is negative.

Adding the retained count gives

$$
s+1-n=h
\ \ge\ \sigma+c_0-|V(H)|+\max(0,w-k_0).
$$

Since $\sigma\ge |E(H)|$ and $c_0\ge\tau(H)$, this is (1). If an edge is outside $H$, its first firing AND cannot be an admissible star. Both of that gate's operand positions are directly reached by the two raw inputs considered together, so both count in $w$. In particular $w\ge2$ if $H\ne G$. Multiple different such gates each contribute their own two positions.

The edge predicate always has an upper construction of size $|E(G)|+\tau(G)-1$ when the graph has an edge. Assign each edge to a center in a minimum vertex cover. The OR of the leaves followed by its AND with the center costs as many gates as the number of assigned edges. An OR of the star outputs finishes the construction. Thus (1) gives the exact optimum in the class whose admissible first stars cover all edges.

## Application to L-meta-9737

The graph of [L-meta-9737](https://pequalnp.com/desk/row?gap=L-meta-9737) consists of 13 points and 12 lines, obtained from the projective plane of order three by removing a line. Its 48 edges split into four edge-disjoint matchings covering the 12 lines. In the cyclic labeling these are the four shifts $0,1,3,9$ of the line index among point labels modulo 13. At most three edge deletions leave at least one whole matching, so any such subgraph $H$ has $\tau(H)=12$. The exact graph, its degrees, and this robust cover fact are verified in Lean. [Graph and 59-gate circuit](PlaneCompletion.lean) · [Robust matching certificate](PlaneRobustCover.lean)

If $s\le58$, (1) excludes $|E(H)|=48$. It also excludes $|E(H)|=47,46$ because an uncovered edge gives $w\ge2$ and the cover number remains 12. Thus at least three edges are outside the admissible stars.

If exactly three edges are outside $H$, equality in the count forces $s=58$, $\sigma=45$, $c_0=12$ and $w=2$. There is exactly one nonadmissible AND with two raw-reachable operands, and every other nonadmissible AND has neither operand raw-reachable. The unique gate with the two erased positions $a,b$ is the first firing AND on all three uncovered edges. There are exactly $2-k_0$ union gates erased by empty projection, since the other gates are all needed for the projected raw outputs. In a minimum circuit, $H$ is spanning and this gate already fires on some singleton input, as follows.

### Spanning in the three-edge case

If $H$ has an isolated vertex $v$, all three deletions are incident to it since the minimum degree is three. It is the only isolated vertex of $H$. Its raw support projects to empty and is a nonempty subset of $\{a,b\}$. If it has only one of these two positions, each of its three neighbors must reach the other position, as the dirty gate fires first on all three missing edges. There is only one erased union gate since $k_0=1$. This gate must be the mixed attachment of the other position to a nonempty projected support. Thus the three neighbors have a projected label in common. It can only be the leaf label of a center in $H$, so these three vertices are also neighbors of that center. The center is different from $v$, contrary to the four-cycle condition.

It follows that $D(v)=\{a,b\}$. Every wire reached from $v$ by an OR-only path can reach only these two operand positions. Its full support projects to empty, so each excess outgoing OR edge contributes an erased union in the reversal. With only one erased union, there is exactly one branching wire in these paths, of outdegree two. After the fork, both OR-only branches have no other consumers and end at the two operands of the same AND. If a branch has zero intervening ORs, the AND is redundant by absorption. Otherwise remove the first OR on each branch and compute the AND of the resulting two disjunctions, then take one OR with the branching wire. This preserves the old AND's value by $(x\lor A)\land(x\lor B)=x\lor(A\land B)$. It saves one gate, contradicting minimum size.

### A singleton trigger in the three-edge case

Since $H$ is spanning, both erased positions reach raw outputs with nonempty projections. Suppose the sets of raw vertices reaching $a,b$ are disjoint. Each position must enter the nonempty subnetwork through a mixed union. Two different positions cannot use the same mixed entrance on a path to a raw output, as then that raw vertex reaches both. With exactly two erased gates, each position therefore has one such entrance. All raw vertices reaching one of the positions have a projected label in common, taken from the nonempty operand of that entrance. A set of two or more such vertices must belong to the leaf set of a center in $H$, since a center label belongs to only one vertex. Each raw set of the dirty gate is thus on one physical side. The two sets must be on opposite sides to trigger on an uncovered edge.

The 12 star centers cover $H$. If there are $p$ points among the centers, there are $p$ lines omitted from the center set. Let $d_t$ be the number of those omitted lines incident to a chosen center point $t$. The omitted lines have $4p$ incidences in $G$, and all but at most three are on the $p$ chosen points. Each $d_t\le4$. Using $6-\binom{d_t}{2}\le3(4-d_t)$ and the fact that two lines have at most one common point gives

$$
\binom{p}{2}\ \ge\ \sum_t\binom{d_t}{2}\ \ge\ 6p-9.
$$

This excludes $2\le p\le11$. The case $p=12$ would isolate the unchosen point in $H$. If $p=0$, every center is a line. The line side of the dirty gate's raw sets must be a singleton line, since two lines cannot share a projected center or leaf label. All three uncovered edges would be incident to this line. If $p=1$, the omitted line must retain its only covered neighbor in the center set, so all three uncovered edges are again incident to one line. In either case the three missing points must all belong to the point-side raw set of the dirty gate. That set lies in the neighbors of a line in $H$. It cannot be the line of the missing edges, and any other line shares at most one point with it. This contradicts the disjointness assumption.

Thus the two raw operand sets of the unique dirty gate intersect, giving an actual singleton trigger through OR-only paths. This restriction and the uncovered-edge count leave open whether a 58-gate circuit exists.
