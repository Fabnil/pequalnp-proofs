# First AND stars in the full plane of order three

Consider a minimum monotone fan-in-two circuit that accepts all incident pairs and rejects every quadrangle input in the full plane of order three. If its size is at most 63, its admissible first AND stars leave **at least four incidences** uncovered. This applies to the test promise in [L-meta-17599](https://pequalnp.com/desk/row?gap=L-meta-17599).

The argument uses the general [first-star projection count](first-star-cover.md) and the three-omission case analysis for the plane with a line deleted. [PlaneQuadranglePairs.lean](PlaneQuadranglePairs.lean) checks the bridge to the full plane's promise. For each same-side pair or nonincident point-line pair, it certifies a quadrangle input containing both selected wires, including the case when the pair repeats a wire. Monotonicity then gives all negative tests of weight at most two. The incident tests give the positive pairs.

## Budget and geometry

Write $G$ for the full point-line incidence graph and $H$ for the union of the admissible stars. For a normalized circuit of size $s$, the projection count gives

$$s \ge |E(H)|+\tau(H)-1+\max(w,26-|V(H)|),$$

where $w$ counts raw-reachable operand positions of the other ANDs. An edge outside $H$ needs one such AND to fire first, so any omission implies $w\ge2$. The 52 edges of $G$ are partitioned into four perfect matchings, the shifts $0,1,3,9$ modulo 13. At most three deletions leave one of the matchings intact, so $\tau(H)=13$ in all four cases under consideration. The budget $s\le63$ excludes zero, one and two omissions immediately.

With three omissions, equality forces $s=63$, thirteen distinct centers, one orientation per covered edge and only two erased, raw-reachable positions. The same nonadmissible gate $g$ fires first on all three omissions. Every vertex keeps an incidence because $G$ is 4-regular. The erasure and retained bounds are both equalities with two erased unions used in raw ancestries. Every remaining union is needed by a raw support. The [equality argument](first-star-three.md#consequences-of-equality) gives one admissible gate per center and places every destination of size at least two inside some raw support.

The thirteen centers form a cover of $H$. Let $k$ be the smaller of the two numbers of centers on the two sides, so $k\le6$. For the side with $k$ chosen centers, let $T$ be the $k$ omitted vertices on the opposite side. In the full graph the number of edges internal to the cover equals the number of edges with both endpoints outside it. This follows because the 13 cover vertices have total degree 52 and $G$ has 52 edges. The internal count is $4k-e(S,T)$, where $S$ is the set of $k$ chosen centers. If $d_v$ counts the neighbors of $v\in S$ in $T$, then

$$\sum_{v\in S}\binom{d_v}{2}\le\binom{k}{2},\qquad 2d_v\le 3+\binom{d_v}{2}.$$

The first inequality uses the absence of four-cycles and the second holds for every integer $0\le d_v\le4$. Thus $4k-e(S,T)>3$ for $2\le k\le6$. If $k=1$, the two exceptional vertices must be incident, with the three omissions all at the noncenter on the side containing twelve centers. Up to exchanging the sides, the only possibilities are all thirteen line centers, or twelve line centers and one point center.

## Excluding equality

Each collapsed mixed union gives all the raw vertices reached through it a common retained label. If the two raw operand sets of $g$ were disjoint, they would use distinct mixed unions and hence each would be on a single side. Their sides would have to differ because $g$ fires on an omitted edge. With every line a center, the line-side set would consist of a single line, because different raw lines share no retained label. With a mixed cover, the three omissions already share the omitted line. In either case the three missing points at that line would also share an assigned leaf label of one covered star. Its center could only be their common line, whose three incidences to those points are absent from $H$. So the two raw operand sets intersect.

An empty-projection union merging both erased positions, together with the only mixed attachment, would give a forward wire with exactly the two operands of $g$ as its OR-only destinations. The [factoring argument](first-star-three.md#the-singleton-triggers-use-one-physical-side) removes a gate and contradicts minimality. The two erased unions are therefore mixed attachments. Their raw sets have a nonempty intersection $S_g$ on one side. If $|S_g|\ge2$, its vertices share an assigned leaf label.

Under these equality conditions, the consuming-rule proof for three omissions transfers to the full plane. Each good gate consumes its center and emits at most one later center. If a run with one center rejects and adding raw leaves makes it accept, its first difference must use an added leaf at the center where the baseline stalls. This gives the mixed-cover contradiction unchanged. The three missing neighbors of the omitted line have pairwise disjoint raw leaf sets. They require three different waiting centers in the baseline that starts from the omitted line singleton. [Mixed-cover argument](first-star-three.md#one-center-is-a-point)

For all line centers, line-side singleton triggers can use only one line. A redirection to another center helps at most one of the three missing neighbors, by uniqueness of line intersections. If $g$ enables the trigger line by supplying its own leaf, the same bound applies at the first later center where the singleton run stalls. [Line-side argument](first-star-three.md#the-singleton-triggers-are-lines)

For point-side triggers, each singleton run can obtain its first required leaf-only destination from only one raw point support. A point and any different point have at most one common line, so each trigger point can account for at most one omission. The three distinct trigger points lie on a common assigned star line. If $g$ emits a center, the runs that progress from all three points can only advance through that common line center before adding any leaves. The three runs therefore share the first leaf set that permits the uncovered pairs to proceed. Each missing line has at least two retained neighbors outside this common line. Its good gate has to emit the output because any redirection from it can help at most one of those retained neighbors. Its target leaf in the shared leaf set consequently accepts a nonincident pair at another trigger point. [Point-side argument](first-star-three.md#the-singleton-triggers-are-points)
