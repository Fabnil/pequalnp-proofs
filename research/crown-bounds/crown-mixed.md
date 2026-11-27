# Exact gate count for mixed disjoint unions of small crowns

Let $G$ be the disjoint union of $p$ isolated edges, $a$ crowns of size $3\times3$, and $b$ crowns of size $4\times4$, with $p+a+b>0$. Each crown has the off-diagonal entries of its square as edges. On the promise of one active row and one active column, its minimum monotone fan-in-two circuit size is

$$
s(G)=2p+\left\lceil\frac{15a}{2}\right\rceil+11b-1+\boldsymbol{1}_{b\text{ odd}}.
$$

The sole exception is a single edge with no other component, which needs zero gates since its only promised test accepts an input wire as the output. The lower bound allows arbitrary sharing and AND depth. In particular, a single crown of each size needs 19 gates. Lean checks the single-edge exception, the single and paired three-by-three constructions, and representative mixed circuits. [Lean witnesses](CrownMixed.lean)

## Upper bound

One three-by-three crown uses seven gates. Merge the three diagonal pairs by OR and compute the threshold-two function on the resulting $x,y,z$ as $(x\land y)\lor((x\lor y)\land z)$.

To pair two three-by-three crowns, merge each row input of one with the same-label column input of the other, by OR. Use both directions. The resulting six signals fall into two families $q_i,z_i$. The test is $\bigvee_{i=0}^2\bigl(q_i\land\bigvee_{j\ne i}z_j\bigr)$. It accepts the within-block off-diagonal tests and rejects cross-block tests, which have signals from only one family. The six merging ORs, three neighbor ORs, three ANDs and two final ORs cost 14 gates.

The [four-by-four constructions](crown-all.md#upper-bound) for one and two crowns cost 11 and 21 gates. Each isolated edge uses one AND. Form pairs within each size, leave one crown of that size if its count is odd, and OR all these outputs. Every constituent circuit rejects singleton assignments, so cross-constituent tests are negative. Counting the joining ORs gives the displayed formula.

## Counting in the reversed OR network

Use the [OR transposition and support normalization](crown-all.md#transposing-the-or-graph). Apart from the single-edge exception, each raw port has a positive and a negative cell, so the $2p+6a+8b$ raw ports are essential and have negative singleton tests. If the circuit has $s$ gates, the normalized reversed OR graph has $h\le s+1-(2p+6a+8b)$ union outputs of size at least two. A start is assigned to a raw port. Every assigned two-position start is terminal, using the replacement of matched pairs by their destinations. Starts on the same side form an antichain because the port neighborhoods on that side form an antichain. Write $J$ for the set of positions assigned to singleton ports on either side, where a singleton port means its start is a one-position set.

In a crown no two adjacent ports can be singleton. The proof uses degree at least two and incomparable neighborhoods, so it applies to both crown sizes. Therefore a three-by-three crown has at most three singleton ports and a four-by-four crown at most four. If a crown has at least three, they all lie on one side. An isolated edge has at most two singleton ports.

Let $\delta_3,\delta_4,\delta_{\rm edge}$ be the respective deficits from these maxima, summed within each type. The total number of nonsingleton ports is $N=3a+4b+\delta_3+\delta_4+\delta_{\rm edge}$. Let $m$ be the number of union outputs assigned to neither side. A nonsingleton start is shared if assigned to a port on each side, and otherwise its port is exclusive. The number of exclusive ports is $E=2(h-m)-N$.

Only the four-by-four blocks enter the required-triple count. For a block with four singleton ports, the four opposite ports require the four complementary triples of the four mates $B$. For a block with exactly three singleton ports, the opposite port of the missing label requires all three mates $U$. Call these blocks full and triple blocks, respectively, and call these ports the ports with required triples. On a fixed side let $P$ count its shared requirements with weight one for a full block and two for a triple block. The [helper inequality](crown-all.md#a-bound-for-shared-ports-on-one-side) gives $P\le2m$ on either side. Its argument only uses the selected required-triple groups and the neighborhood antichains. Adding the smaller components therefore preserves the inequality.

Let $\lambda_R,\lambda_C$ be the deficits $2m-P$ on the two sides. Partition the exclusive ports into $E_4,E_3,E_0$, according to whether they have a required triple from a full block, one from a triple block, or neither. Let $f_i$ count four-by-four blocks with $i$ singleton ports. The two values of $P$ sum to $4f_4+2f_3-E_4-2E_3$. Eliminating $E_3$ using $E_4+E_3+E_0=2(h-m)-N$ gives

$$
\begin{aligned}
4h-6a-12b
  &=2D+E_4+2E_0+\lambda_R+\lambda_C,\\
D&=\delta_3+\delta_{\rm edge}+f_1+2f_0.
\end{aligned}
$$

Indeed $4f_4+2f_3+2\delta_4=4b+2f_1+4f_0$. Thus $h\ge\lceil3a/2\rceil+3b$ and

$$
s\ge 2p+\left\lceil\frac{15a}{2}\right\rceil+11b-1.
$$

It remains to show that this budget implies even $b$. At the budget, $h=\lceil3a/2\rceil+3b$ and the left side of the counting identity is zero or two according to the parity of $a$.

## What equality on one side gives

Call a side tight when $\lambda=0$. At a tight side, the argument proving that [every helper is a disjoint pair](crown-all.md#every-helper-is-a-disjoint-pair) applies as written. It uses equality in the helper inequality for that side. It permits full groups in which only some of the demands are shared, since the correction for a missing position in the count concerns only full groups with all four demands shared. In particular all $m$ unassigned outputs are admissible helpers, each a pair, and these pairs are disjoint. Let $W$ be their union, of size $2m$.

Here are the relevant consequences when some full group is only partially shared. For a fixed orientation, let $B^*$ be the union of groups with at least one shared demand. With just pair helpers, the [refined saturation set](crown-all.md#every-position-of-w-is-useful-for-both-orientations) $K'$ in $B^*$ suffices. It consists of $W\cap B^*$ and the useful positions $V$ produced by saturating $W$. Its size is at most $|W|-|V|$. Any counted triple contains at least two positions of $K'$. If a required position $x$ is missing from $K'$, its start has the form $H\cup\{x\}$ and the other two positions must form the terminal pair obtained from a helper $H$. Such a terminal pair is one of the declared pair helpers. This follows because a complete pair, if consumed, is replaced entirely by its destination, which has size at most two.

In a full group with at least three shared demands, no position of $B$ can be outside $K'$. For a missing position, at least two of the shared complementary triples use that position. They would require two distinct pairs of its complementary three-set, contradicting disjointness. Thus for $q=1,2,3,4$ shared demands the minimum $K'$-intersection with that group is at least $2,2,4,4$, respectively. A counted triple block contributes at least two.

On a tight side these costs sum to at least $P=2m$, so $K'=W$ and $V$ is empty. Each grouped count must be exact. In particular no full group on a tight side has exactly one or exactly three shared demands. A full group with two shared demands has exactly two positions of $W$, one with four has all four, and each counted triple group has exactly two positions of $W$. The groups exhaust $W$.

Every position in $W$ is thus mated with a singleton port on the physical side opposite the tight side. This fact is enough to make **every shared start terminal on both sides**. Shared starts and their single-port runs avoid $J$. A large shared start is a union of two helpers or a helper and one position. It has at most one position outside $W$, so it cannot initiate a rule since all mates of positions of $W$ lie in $J$. Assigned pairs are terminal by normalization.

If both sides are tight, every position of $W$ is mated with a singleton port on each physical side. In this case an exclusive port whose support is earliest among the exclusive supports, if it has a required triple, starts from helpers and at most one further position. Its nontrivial operands cannot be earlier exclusive starts by choice, or shared starts by same-side incomparability. This exclusive port also cannot initiate a rule, since the mates of positions of $W$ on its physical side are absent in its single-port run. In particular this earliest exclusive start cannot provide a required triple with two or more positions outside $W$.

## Shared starts and connected components

Consider the induced bipartite graph on the ports with shared starts. Exchange the two ports with each shared start. The exchange is a side-swapping involution preserving edges because the test depends on the union of starts. The ports within each exchanged pair are nonadjacent, since their test uses a single start and singleton assignments are negative.

If the same position $q$ is assigned to singleton ports on the two sides, they have the same adjacent shared starts. For such a port, count its shared neighbors and how many of them are nonisolated in the induced graph. These counts agree across the two sides for the same $q$. In a full block with all four demands shared, a singleton port has three shared neighbors, all isolated. In a triple block with its center and three leaves shared and its required triple shared, a singleton port has three shared neighbors, two of them nonisolated. Here the center is the lone nonsingleton port on the singleton side. Its three nonsingleton neighbors are the leaves.

The nontrivial components of the shared graph for four-by-four blocks are as follows when the only possible exclusive ports have required triples from triple blocks.

| Singleton counts on the two sides | Nontrivial component |
| --- | --- |
| $(4,0)$ or $(0,4)$ | None |
| $(3,0)$ or $(0,3)$ | A star with side sizes $(1,3)$ or $(3,1)$ |
| $(2,0)$ or $(0,2)$ | A connected component with side sizes $(2,4)$ or $(4,2)$ |
| $(1,1)$ | A connected three-by-three crown |

In a triple block the port with the required triple is isolated in this induced graph when it is shared. Omitting it when it is exclusive leaves the star unaffected. Two singleton ports on opposite sides of a crown must have the same label. A three-by-three block with three singleton ports contributes only isolated vertices. An edge with at most one nonsingleton port contributes no nontrivial component.

Suppose there is a fixed three-by-three component of the indicated $(1,1)$ type in a four-by-four block, and a tight orientation in which every position of $W$ comes from a full or counted triple group with the stated shared-neighbor counts $(3,0)$ or $(3,2)$. The three pairs of shared starts within the fixed component must be diagonal. Let $\alpha,\beta$ be the mates of its two singleton positions. Neither is in $W$. On the physical side supplying the singleton mates for the tight orientation this follows by injectivity of singleton positions and disjoint blocks. On the other side a coincidence would give equal neighbor counts with a singleton position from a full or counted triple group. The singleton of the fixed component has counts $(3,3)$, since all three of its neighbors belong to the connected three-by-three crown.

The three shared starts in the fixed component each need both $\alpha$ and $\beta$. If the mates differ, no large start accommodates both outside $W$, and all three pairs would be equal. If they coincide at $\gamma$, a large start lies inside $W\cup\{\gamma\}$, all of whose positions are mated to positions in $J$. Its union with another terminal shared start cannot fire a rule because that other start avoids $J$. So all three must be pairs $\{\gamma,x_i\}$ with distinct extras. The three positive tests between pairs would require the extras to be pairwise mated, which is impossible. This excludes the fixed component.

## The budget cannot remove the parity term

The counting identity at the budget allows $E_4=2$ with both sides tight, or $E_4=1$ with one side tight and the other of deficit one. We first exclude both possibilities.

**Two exclusive full demands.** Neither orientation has a full group with three shared demands, by tightness. The two exclusive demands must therefore come from one full group with two shared demands. Its intersection with $W$ has size two. Each shared start for the group can have at most one position outside $W$, so the two shared triples are the two that contain both positions of this intersection. Both other triples require two positions outside $W$. The only other possible exclusive ports are in triple blocks with an exclusive demand. Their required triples are disjoint from $W$, because their groups do not contribute to the counted groups on their side. The earliest exclusive start cannot supply any of these demands.

**One exclusive full demand.** Its full group has three shared demands, so it is on the side of deficit one. The other side is tight, with disjoint pair helpers. On the side of deficit one the refined set $K'$ must include all four positions of this partial group, costing one beyond its weight. The other groups cost at least their weight. Hence $|K'|\ge P+1=2m$ and $K'=W$ also on this side. Its partial full group has three singleton ports with exactly two shared neighbors each, since they lose the exclusive neighbor. Their mates are in $W$, whereas every mate in $W$ on the tight orientation belongs to a singleton with three shared neighbors. Equality of neighbor sets under a shared singleton position gives a contradiction.

We are left with $E_4=0$. If the total side deficit is two, one side is tight and the other has deficit two. Indeed $P=4f+2g$ is even on each side when all full demands are shared. Otherwise both sides are tight. At least one orientation supplies $W$ with disjoint pair helpers and entirely terminal shared starts.

When the other side has deficit two, every full group on that side still has all four positions in $W$. If some position is missing, the three shared demands containing it need three distinct pair helpers in its complementary three-set, because their terminal starts can use at most one position outside $W$. Disjoint helpers cannot do this. Each counted triple of that side has at least two positions in $W$ by the same one-extra-position property. Consequently at most two positions of $W$ lie outside the counted groups on that side.

It remains to handle the limited ways that the nontrivial-component census could change. The counting identity leaves at most one of $D=1$ and $E_0=1$, and either forces both sides tight.

- **One unit of $D$.** There is no exclusive port without a triple requirement. If any exclusive port remains, its required triple belongs to an uncounted triple group and is disjoint from $W$. This is impossible for the earliest exclusive start. So all nonsingleton ports are shared. If a four-by-four block has only one singleton, it contributes a connected $(3,4)$ or $(4,3)$ component, with no possible transpose partner. If a three-by-three block has a deficit of one, its two singletons cannot be on the same side. That would give a $(1,2)$ or $(2,1)$ star with no transpose partner. With two opposite-side singletons it contributes only two balanced one-edge components. If the deficit is on an isolated edge, it contributes at most one isolated vertex. In the last two cases the census for the four-by-four blocks is unchanged.
- **One exclusive port without a required triple.** All three-by-three blocks are full of singleton ports on one side, each isolated edge has both ports singleton, and every four-by-four block has at least two singleton ports. Inside a triple block, removing a leaf would leave an unmatched $(1,2)$ or $(2,1)$ component. If the center is exclusive and its opposite triple demand is shared, the two positions of $W$ from that group have neighbor counts $(3,0)$ in place of $(3,2)$. These are the only exceptional positions. In the orientation of the exceptional group the total number of $(3,0)$ positions in $W$ is $4f+2$, counting its full groups and that triple. On the other orientation the count is a multiple of four. Every position of $W$ has a mate singleton on both sides with the same counts, a contradiction. If the center and opposite triple demand are both exclusive, their $U$ is disjoint from $W$. The three shared leaves need the three pairs of $U$, respectively, so their terminal starts are exactly those pairs. The center's terminal support avoids the singleton mates of the positions in $U$ by same-side incomparability. Thus it cannot trigger a rule with any leaf pair, contrary to the three center–leaf edges.

  The remaining exceptional exclusive port can be in a three-by-three block, where it removes an isolated vertex, or in a four-by-four block with two singleton ports. Removing a nonsingleton vertex from a $(1,1)$ block leaves a connected $(2,3)$ or $(3,2)$ component with no transpose partner. In a block of orientation $(2,0)$ or $(0,2)$, removing a port from the side with four nonsingletons also leaves such an unmatched component. Removing from the side with two nonsingletons leaves a star and an isolated vertex. This changes only the type of its single unbalanced component, from a rectangular component to a star.

Now every position in $W$ that belongs to counted groups on both sides can belong to a full group on one side only if it belongs to a full group on the other. This follows from the counts $(3,0)$ for full groups and $(3,2)$ for counted triple groups. All full groups on both sides lie in $W$. With both sides tight the numbers of full groups are equal. If one side has deficit two, the full positions on that side are a subset of the full positions on the other. At most two additional full positions of the tight side can lie outside the counted groups on the deficit side. The difference is a multiple of four, so it is zero.

Thus full blocks occur an even number of times. So do the total number of triple blocks and blocks of orientation $(2,0)$ or $(0,2)$, counted together. Each contributes exactly one unbalanced component after the exclusions above, and all unbalanced components occur in transpose pairs. Any exceptional components contributed by smaller blocks are balanced or isolated. Therefore if $b$ is odd, there are an odd number of intact connected three-by-three components from four-by-four blocks of orientation $(1,1)$. The side-swapping involution must fix one. The fixed-component obstruction excludes it.

This proves that the lower budget requires even $b$, establishing the formula together with the zero-gate single-edge case.
