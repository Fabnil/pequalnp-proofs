# Two isolated points are impossible with six omitted edges

In [L-meta-9737](https://pequalnp.com/desk/row?gap=L-meta-9737), let $H$ be the union of the admissible raw AND stars of a minimum normalized circuit of at most 58 gates. If exactly six edges lie outside $H$, at most one vertex is isolated. In particular, the only remaining way to lose a matching covering all twelve lines is for two lines to retain only their edge to their common point.

An [isolated line is already excluded](first-star-six-isolated.md). If $u,v$ are isolated points, both have degree three. Their line neighborhoods $X_u,X_v$ are disjoint and their incident edges are exactly the six omissions. The live neighbors of each isolated point have pairwise disjoint projected raw supports. A mixed attachment can therefore reach at most one member of each triple. We say an attachment supplies an erased position to a raw output when the path carrying the position uses the empty operand of the attachment to enter the nonempty subnetwork.

Use $D(v)$ for the raw support of $v$ and use $c,w,M,\Delta,R,E$ from the [six-edge budget](first-star-six-budget.md). Let $P$ count pure erased unions, $q$ mixed attachments and $A=P+q$. With 23 live raw supports the retained count gives

$$
P+q+R+E\le15-c .
$$

The [center and saturation bounds](first-star-six-budget.md#cover-sizes-at-six-deletions) leave $c=11,12,13$, with $w\le5$ for $c=11$ and $w\le4$ for $c=12,13$. With eleven centers, all eleven live points are centers. With twelve centers, the [cover count](first-star-six-budget.md#matching-deficiency-with-twelve-centers) gives either all line centers or all live points and one line center. The supports $D(u)$ and $D(v)$ are nonempty erased sets, incomparable by [raw-support dominance](first-star-five-saturation.md#setup-and-raw-support-dominance). If either contains both operands of an AND, it uses at least two pure unions by the [factoring argument](first-star-six-isolated.md#six-omitted-edges-leave-no-isolated-line). We fold fanouts with a nonempty projection first as in that argument.

## Tracking the targets when all lines are centers

For an isolated point $v$, compare its rejecting singleton with the positive pairs $(v,\ell)$, $\ell\in X_v$. As before, count the pending good center positions and raw-unreachable operands. If all line neighbors are noncenters, this gives the [erased component bound](first-star-six-isolated.md#the-erased-components-at-equality) $3\le M+\Delta-\kappa$, with cycle rank $\kappa$.

The same bound holds if all centers are lines. Then also count the distinct targets $\ell\in X_v$ for which a leaf position of a star centered at $\ell$ was ever emitted on singleton $v$. An ancestral support with such a leaf lies inside a raw point support. It has no tracked position and can have only one target since that point shares at most one line with $v$. A single source position can also add at most one track or target. The [tracking argument with external unions](first-star-five-cover.md#tracking-additional-positions) applies with these additional targets. Each boundary support with a new target accounts for one, and each beyond the first boundary support in an emission costs an external union. The extra positions in a boundary support with repeated centers are still charged to $R$. The sum of pending tracks and targets is at most $J+R+E$ after the singleton fires $J$ of the $M$ gates. An added line center can cause a first difference only with its own target leaf. The other first differences use erased operands, from a pending track or from one of the $M-J$ fully raw-reachable gates. Each mixed outlet reaches at most one neighbor, giving $3\le M+\Delta-\kappa$ as before.

In either cover, if $3=M+\Delta$, the equality argument makes $D(v)$ private to $v$. A component containing its raw outlet cannot use that outlet for one of the targets, and a component with more than one outlet at equality needs all of them.

## One gate with two raw-reachable operands

Suppose $M=1$ and let $a,b$ be the operands of its gate $g$. If exactly one of $D(u),D(v)$ contains both, it needs at least two pure unions. The other point is missing an operand and needs three mixed attachments, one for each of its neighbors. This exceeds the budget of at most four erased unions.

If neither support contains both, at least three mixed attachments are necessary and at most one pure union is available. A single attachment cannot supply both $a,b$. Its empty operand would have to be the sole pure union with full support $\{a,b\}$, and the resulting single fork can be factored to save a gate. Thus if either point lacks both operands, its neighbors require six attachments. If the two points lack different operands, they likewise require six. If they lack the same operand, their incomparable raw supports both contain the other one and at least one distinct further position each. Their different nonsingleton outputs require at least two pure unions.

If both supports contain $a,b$, incomparability makes both of size at least three, requiring at least three pure unions to compute the two distinct outputs. This is impossible for $c=13$. For $c=11,12$ it leaves $q\le1$ and $R+E\le1$. Use a singleton with all line neighbors noncenters, available unless all centers are lines. Its run fires $g$ and leaves at most $1+R+E$ tracked positions. Every line in its triple can be served only by a waiting track. The added leaf sets are disjoint and a raw erased position can reach at most one line in the triple through the at most one attachment. Thus at most two of the three neighbors can be served. If all centers are lines, then $c=12$ and $P\ge3$ exhausts the budget, so $q=R=E=0$. Counting the target leaves together with the pending tracks allows just one neighbor. This excludes $M=1$.

## Five erased positions at eleven centers

Here $M=2$ and one erased position belongs to a gate with only one raw-reachable operand. Both isolated points have three missing noncenter neighbors. Since $\Delta\le1$, both comparisons attain $3=M+\Delta$. Both raw supports are private, $\kappa=0$, and the outlet surplus of the erased components is at most one. A fixed missing operand can therefore be supplied to at most two members of a neighbor triple.

Suppose $D(v)$ contains both operands of one fully raw-reachable gate. The only possible first gate on tests at $u$ is the other fully raw-reachable gate. Both of its operands must be outside $D(v)$ by privacy. In an acyclic erased component with just one private raw outlet, a raw support consisting exactly of two positions of one AND is impossible. It would require at least two pure unions on two sources, producing positive cycle rank. Thus $D(v)$ also contains the fifth position. The other isolated point $u$ can only get positions of the second gate and cannot get both, by the same two-source count. The second gate then serves at most two neighbors of $u$.

Consequently neither singleton can initially fire either fully raw-reachable gate. At least one of the two disjoint nonempty raw supports contains a position from one of those gates, since there is only one other position. Privacy makes that gate unavailable as the first gate on all three tests at the other point. The remaining gate lacks a fixed operand at that point and can serve at most two neighbors there.

## Four erased positions at twelve or thirteen centers

Suppose $c=12$. There is an isolated point $v$ with all three line neighbors noncenters unless all centers are lines, in which case use the target count. In either case $3=M+\Delta$ since $\Delta\le1$. Thus $D(v)$ is private and $\kappa=0$. The fully raw-reachable gate serving an edge at the other point avoids $D(v)$, so $D(v)$ is a subset of the other gate's pair. A two-position support of that form would have a cycle, so write $D(v)=\{a\}$ for the first gate with operands $a,b$ and write $d,e$ for the second gate's operands.

Each of the three tests at $v$ needs at least one attachment into its line's raw support. The budget is three, so there are exactly three mixed attachments and no pure unions, one attachment serving each tested line. Therefore the second gate cannot fire initially since it would require both $d,e$ from the line. All three attachments must supply $b$. Then $d,e$ must both reside at the other isolated point, whose raw support is a singleton since there are no pure unions.

Suppose $c=13$. With $w=4$ the budget is tight. Every erased component has one outlet, so both isolated supports are private. Each isolated point must have both operands of some gate in its raw support. Otherwise each of the at most two gates has a missing operand which its one outlet can supply to at most one neighbor. The two supports then consist of the different full pairs, needing at least two pure unions apiece in disjoint components, above the budget of two.

## Four erased positions at eleven centers

Here at most four erased unions are available and all centers are points. Denote the two gates by $g_1,g_2$. All other nonadmissible gates have two raw-unreachable operands.

### At most one pure union

If $P\le1$, no isolated support or empty operand of an attachment can contain both operands of one gate. A sole pure union for such a pair would have only one fork and could be factored. Therefore each line in either triple needs at least one attachment.

If $P=0$, the isolated raw supports are distinct singletons. Write $D(v)=\{a\}$ and the gate pairs as $a,b$ and $d,e$. If a line in $X_v$ initially fires the second gate with $v$, it needs separate attachments for $d,e$. The other two lines in $X_v$ each need an attachment supplying $b$, exhausting the four attachments. At $u$, the first gate is then unavailable because $a$ is private, and the second gate serves at most one neighbor because each of $d,e$ has one live outlet. If no line in $X_v$ fires the second gate initially, three attachments supply $b$ to the first gate. At $u$ each gate needs some operand other than $b$ from the line, and at most one remaining attachment can supply one.

If $P=1$, all three attachments must reach the three distinct lines of each triple. Each tested line thus receives its erased positions from a single attachment. If one isolated support is a pair, the other is a singleton outside that pair by incomparability. Relabel the gate pairs as $a,b$ and $d,e$, with $D(v)=\{a,d\}$ and $D(u)=\{b\}$. Every line at $u$ must get $a$, since its one attachment cannot supply both $d,e$. Thus all attachments carry $a$ and none can carry $b$ or $e$ since the sole pure union computes $\{a,d\}$. No line test at $v$ can fire initially.

Otherwise both isolated supports are singletons. For each singleton, all three attachments must supply the other operand of its own gate, since one attachment cannot supply both operands of the other gate. If the singletons hold the two operands of the same gate, this would require the excluded one-fork pair. Otherwise write $D(v)=\{a\}$ and $D(u)=\{d\}$, with gate pairs $a,b$ and $d,e$. The three attachments now all carry the full empty support $\{b,e\}$, and $R=E=0$. On the three tests at $v$, firing $g_1$ gives the same state $T=D(g_1)\cup\{e\}$ plus disjoint sets of good leaves, writing $D(g_1)$ for its destination. If $T$ accepted by itself, every raw firing of $g_1$ would accept because every raw vertex reaching $b$ also reaches $e$ and raw $a$ occurs only at $v$. This would make $g_1$ admissible. The rejecting run from $T$ starts with at most one track and only $g_2$ can increase that count. At most two pending good centers can be available, fewer than the three first differences required.

### At least two pure unions

Now $q\le2$, so both points must contain a gate's full raw pair in their raw supports. Otherwise the three line neighbors of one point would need three attachments. As the distinct outputs are incomparable and each requires at least two pure unions in its ancestry, at least three pure unions are necessary. Indeed with just two union nodes both outputs would have to use both and hence coincide.

At most one unit is left for $q+R+E$. If a singleton fired just one of $g_1,g_2$, its at most $1+R+E$ pending tracks and the at most $q$ neighbors able to supply a fixed missing operand of the other gate would serve at most two tests. Therefore both fully raw-reachable gates fire on both singletons. The three missing neighbors now require three different terminal good centers. This needs $R+E=1$ and leaves $P=3$, $q=0$.

Choose a position $f\in D(u)\setminus D(v)$. It must be emitted on singleton $v$ before its gate fires. No live raw support contains $f$ because $q=0$, so it is private to $u$. The emission must also add a track. Otherwise the loss of one emission in the tracking count leaves at most $2+R+E-1=2$ pending tracks. When $E=0$ a destination containing $f$ is either a singleton or contained in $D(u)$, and has no track. Hence $E=1$ and $R=0$. The unique external union must combine a support containing $f$ with another support. Its operand containing $f$ has no track, and the other has at most one. Thus all destinations contain at most one track, including the external union, and the two fully raw-reachable firings cannot leave three.

All cases with two isolated points are excluded. The [spanning follow-up](first-star-six-spanning.md) excludes a single isolated point as well.
