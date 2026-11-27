# Excluding three uncovered edges at the 58-gate budget

For the deleted projective plane in [L-meta-9737](https://pequalnp.com/desk/row?gap=L-meta-9737), let $H$ be the union of [the admissible stars from raw OR paths into ANDs](first-star-cover.md). A minimum circuit with at most 58 gates must leave **at least four edges** outside $H$. This strengthens the three-edge restriction. The existence of a circuit on 58 gates remains open.

We use correctness on assignments of weight at most two. When reducing gates by a circuit identity, the identity preserves the function on all assignments and so also applies to a minimum circuit for the unrestricted edge predicate.

## Consequences of equality

Suppose there are exactly three uncovered edges. The previous count gives $s=58$, $H$ spanning, 12 distinct good star centers, no edge of $H$ covered in both orientations, and a unique nonadmissible AND $g$ with both operand positions $a,b$ raw-reachable. The only erased positions that reach any raw support are $a,b$. This gate fires first on each uncovered edge and already fires on a singleton input.

Consider the reversed union graph and its projection to good center and leaf labels. Exactly two union gates collapse because of empty operands. All other union gates are counted in the lower bound for the projected raw supports. Each of the two erased gates is also counted in the subgraph used to compute raw supports in the proof of the erasure bound. Thus **every original union gate is used in the ancestor graph of some raw output**. Every nontrivial support emitted by an AND is therefore a subset of a single raw support. This applies because such an output must be copied from a union node, with every position in that union also present in the raw output that uses it.

There are no repeated original positions mapping to the same retained label in the support of any raw vertex. To see this, collapse the empty-projection gates but still distinguish original retained source positions, including ones with the same label. At equality every remaining union gate has projected support of size at least two. It can be used by only one raw output, since projected supports pairwise intersect in at most one label. For a raw output reached from $k$ distinct retained source positions, its connected union subgraph needs at least $k-1$ gates. Equality in the lower count, which used the number of distinct projected labels instead, forces the two counts of positions and labels to agree.

In particular each center has exactly one good AND gate: its raw center port reaches a different original center position for every gate with that center. From now on write $C_z,L_z$ for the actual center and leaf positions of the unique good gate centered at $z$. A raw port reaches at most one center position, its own if it is a center. A good gate fires when its center position and its corresponding leaf position are both present. There is a unique good first firing gate on every edge of $H$, because the edges are covered in only one orientation and the good gate at a center is unique.

## The singleton triggers use one physical side

Compute reversed fanouts in the following order. When a forward wire has any outgoing contribution with nonempty projected support, use one such contribution first and fold in the others one at a time. Thus an empty-projection union with two empty operands arises only at a wire whose entire support projects to empty.

If either erased union has two empty operands, only one mixed attachment remains. Both erased positions $a,b$ must reach nonempty raw outputs through this single attachment. Its empty operand therefore contains both, produced by the one empty union. This identifies a forward wire whose whole support is $\{a,b\}$. Its OR-only descendants have exactly one fork, as every extra branch in that empty region costs an erased union. They reach just the two operands of $g$. With a direct branch $g$ is redundant by absorption. With an OR on each branch, factor the common wire out of the AND as in the [spanning argument](first-star-cover.md#spanning-in-the-three-edge-case) and save a gate. Either violates minimality.

Thus both erased unions are mixed attachments, one for each position. All raw ports reaching a given erased position share some retained label from the nonempty operand of its attachment. If two or more raw ports reach that erased position, the common label is a leaf label, and they are all neighbors of one center in $H$. A singleton set of raw ports is also on one side of the bipartition. Since the two sets for $a,b$ intersect, both sets lie on the same physical side. Let $S$ be their intersection. Then on every point-line test, $g$ fires from the raw starts exactly when the selected vertex of that side belongs to $S$. If $|S|\ge2$, its vertices lie in the leaf set of one good star.

## Consuming rule evaluation

Use the consuming evaluation of the [transposed rules](crown-all.md#transposing-the-or-graph). When an AND fires, remove its two positions and add its destination support. This preserves the result and each destination is later in the rule order.

After $g$ fires we no longer need its two raw positions. Every later destination either emits a singleton, or lies in a raw support and hence uses only good positions. It contains at most one center position. Emission of the output position means acceptance. A singleton position outside the good marks and the output cannot start another nonadmissible rule by itself. Both operands of every other nonadmissible rule are raw-unreachable. In the continuations below, whenever an emission of such a nonraw position leaves no good gate enabled, the run stops. There were no earlier nonraw positions in these runs, since the preceding emissions were all good marks.

In a state with at most one center position, at most one good gate is available. As long as only good gates fire, consuming its center and emitting at most one preserves this property. In particular consider two such states that differ only by some extra leaf positions. If the smaller state's run stops without accepting, the larger run has the same sequence until a first difference. A difference requires a still pending center and its missing leaf in the extra positions. If there is no remaining center, adding leaves cannot continue the run. This comparison applies also when a singleton nonraw emission stops the smaller run, because there is then no remaining center and no mate of that new position.

## All 12 centers are lines

Every raw point has only good leaf positions, and a raw line $\ell$ has just the good center position $C_\ell$. Write $B_x$ for the leaf positions at a raw point $x$. The leaf $L_j$ is in $B_x$ exactly when $x$ is an $H$-neighbor of line $j$. A post-$g$ destination containing a center must be just that center, since any raw support containing a center has no leaves and $a,b$ are earlier positions. A post-$g$ destination containing only leaves lies in some $B_z$ for a point $z$.

### The singleton triggers are lines

No two lines share a projected label, so $S$ consists of one line $\ell$. The three uncovered edges are all incident to $\ell$. Each missing point $x$ lacks $L_\ell$ in its raw support. If $g$ emits a center $C_j$, the newly enabled good gate must be $j$ with $L_j$ present in $B_x$, since $\ell$ is still disabled and there are no newly emitted leaves. If $j=\ell$ it cannot start. If $j\ne\ell$, at most one of the missing points can lie on $j$.

If $g$ emits only leaves, it must provide $L_\ell$ to make any missing test progress. Then the singleton $\ell$ itself starts the same first good gate as every missing pair. Compare their runs by the one-center rule above. To accept, each missing point needs to supply the leaf of the same first center at which the singleton run stalls. This center is a different line from $\ell$, since the gate at $\ell$ has fired and its positions cannot be output by a later rule. At most one point of $\ell$ lies on that different line. An output position from $g$ would accept the singleton, and a nonraw slot by itself cannot help an uncovered pair. This excludes the line-side case.

### The singleton triggers are points

Fix a point $x$ with an uncovered edge to $\ell$. The singleton $x$ triggers $g$. After $g$, the pair $(x,\ell)$ differs from that singleton only by the center $C_\ell$, which cannot fire until some gate emits its missing leaf $L_\ell$. If $g$ emits only leaves, call that set $T_x$. If it emits a center, follow the center sequence on the singleton $x$ until the first leaf-only emission, and call it $T_x$. Before then the extra center $C_\ell$ is inactive because no leaves have been added. A nonraw emission or a stalled center cannot get past this stage, and an output emission would accept the singleton. Therefore every uncovered edge from $x$ requires $L_\ell\in T_x$. The set $T_x$ lies in some $B_z$. If $z=x$ it contains no such missing leaf. Otherwise $x,z$ have at most one common line. Thus each point can be incident to at most one of the three uncovered edges.

The three distinct missing points are in $S$ and lie in the leaf set of one line $c$. If $g$ emits leaves directly, the set $T_x$ is the same for all three. If $g$ emits a center, it must be $C_c$, since all three points have to enable it, and any other line meets $c$ in at most one point. The good gate of $c$ must emit leaves, since redirecting to another center would again leave at most one of the three able to proceed before any leaves have been added. It cannot emit the output on the singleton tests. Hence the required leaves are a common set $T$ in either case.

For one uncovered edge $(x,\ell)$, we now have $L_\ell\in T$ and $\ell\ne c$. The line $\ell$ meets $c$ only at $x$, so the other missing points are not on $\ell$. There is no other missing edge at $\ell$ and every $H$-neighbor of $\ell$ is outside $S$. On each such $H$-edge the gate at $\ell$ fires first and $g$ is initially off. The gate at $\ell$ is later than $g$, since it is enabled by $T$ on the uncovered edge. It cannot activate $g$ later on an $H$-edge. After the gate at $\ell$ consumes the sole center, an accepting continuation must either emit the output or redirect to a new center whose leaf is at the chosen point. A different line meets $\ell$ at most once, so a redirection cannot accept even two of its three $H$-neighbors. The gate at $\ell$ must emit the output.

For another missing point $x'$ on $c$, the nonedge $(x',\ell)$ starts $g$ and the same initial continuation to $T$. The good gate at $\ell$ then fires and emits the output. This is a contradiction.

## One center is a point

The [cover count](first-star-cover.md#a-singleton-trigger-in-the-three-edge-case) and the fact that $H$ is spanning leave only one other possibility. There are 11 line centers and one point center $z$. All three missing edges are incident to the omitted line $\ell$, which keeps its one $H$-edge to $z$. Its three missing points have only line-leaf positions in their raw supports. Their sets of such positions are pairwise disjoint, since they already share $\ell$ as a common line, and $\ell$ is not a center.

The singleton triggers cannot be on the point side. They would have to include all three missing points, whereas a set of two or more singleton triggers shares a retained label. Thus $\ell$ is a singleton trigger. Its raw support has only the good leaf position of $z$ and the two dirty positions. Each uncovered edge differs from that singleton only by adding the leaf set of its missing point. This remains true immediately after firing $g$, and its destination provides at most one center in both tests.

Use the one-center comparison. To differ from the rejecting singleton run, the three accepting tests would all have to supply the same missing leaf at their first difference. Their extra leaf sets are pairwise disjoint. This is impossible, completing the exclusion.

## The next budget case

With exactly four missing edges, if no line is isolated, $H$ still has a 12-edge matching. If Hall's condition failed on $k$ lines, they would have at most $k-1$ neighboring points after the four deletions. At least $4k-4$ of their incidences remain. Every point has degree at most four, so outside the isolated-line case equality is forced and all $k-1$ neighbors have degree four into these lines. With $k\ge2$ and at most one common point per pair of lines, this requires $\binom{k}{2}\ge6(k-1)$ and so $k=12$. But only nine points have degree four in the original graph. [Checked point count](PlaneRobustCover.lean)

For this spanning-on-lines four-edge case, (1) gives $w\le3$ at size 58. There can be only one nonadmissible AND with both operands raw-reachable, and at most one further raw-reachable operand among the other nonadmissible ANDs.
