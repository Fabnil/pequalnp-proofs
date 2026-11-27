# Exact monotone circuit size for disjoint four-by-four crowns

Let $A_k$ be the $4k\times4k$ block-diagonal Boolean matrix of $k$ four-by-four crowns. In each diagonal block the entry is one exactly when the two labels differ. Let $s(k)$ be the least number of AND and OR gates of fan-in at most two in a circuit computing $A_k$ on the promise that exactly one row input and one column input are active. For every $k\ge1$,

$$
s(k)=
\begin{cases}
11k-1 & \text{if $k$ is even},\\
11k & \text{if $k$ is odd}.
\end{cases}
$$

The lower bound is combinatorial and permits arbitrary sharing and AND depth. The argument below includes the model reduction and the case of equality. Lean checks the constructions for [one](CrownBlocks.lean#L178), [two](CrownBlocks.lean#L161) and [eight](CrownBlocks.lean#L219) crowns, as well as the [one-extra-position lemma](CrownDemand.lean#L150) used in the lower bound.

## Upper bound

For two blocks $A,B$, use eight ORs to create $q_i=r^A_i\lor c^B_i$ and $z_i=r^B_i\lor c^A_i$, for $0\le i<4$. A test within a block gives one $q$ and one $z$. A cross-block test gives signals from only one family. Thus $\bigvee_i(q_i\land\bigvee_{j\ne i}z_j)$ gives the required values. The four inner triples use six ORs by sharing $z_0\lor z_1$ and $z_2\lor z_3$. There are then four ANDs and three output ORs, for a total of $8+6+4+3=21$.

For a single crown, merge the four diagonal pairs by OR. For each of the two bits of a label, OR the two merged signals on either side of its bit partition and AND the two results. OR the two bit tests. This uses $4+4+2+1=11$ gates. Both constructions reject singleton inputs. Pair the blocks, leave one single block if $k$ is odd, and combine the outputs by binary OR. The total is $21(k/2)+(k/2-1)$ for even $k$ and $21((k-1)/2)+11+(k-1)/2$ for odd $k$.

## Transposing the OR graph

Monotonicity and the negative diagonal tests force the output to be zero on each singleton input. Every raw port is essential because it has a positive neighbor. Take a minimum circuit with $s=s(k)$ gates. Constant and unary operations can be eliminated, and all the gates lie in the output cone. Cut the circuit at each AND. For AND gate $i$ create separate operand positions $a_i,b_i$ and use its result $p_i$ as a new source. There is also a position $o$ for the circuit output. The remaining OR graph has $8k+t$ sources, $s-t$ binary ORs, and $2t+1$ terminal positions, where $t$ is the number of ANDs.

Reverse the OR graph and assign a singleton to each terminal position. Each old source $v$ now computes the support $D(v)$ of positions it reaches. A vertex with $d$ outgoing edges in the original graph takes $d-1$ binary unions after reversal. Summing over the nonterminal vertices gives $(s-t)+(2t+1)-(8k+t)=s+1-8k$ unions. Identifying equal supports and identifying singleton supports with their positions leaves $h\le s+1-8k$ distinct union outputs. Each of these has a construction by two proper subsets, each a position or an earlier union output.

To evaluate a test, start from the union of the selected port supports. If both premises $a_i,b_i$ are present, rule $i$ adds $D(p_i)$. All its destinations are later premises or $o$. The test is positive if $o$ is reached. Each premise position has a unique rule that reads it. Call $a_i,b_i$ mates. We may *consume* the two premises when firing a rule. Replacing an active complete pair by its destinations preserves the output under any added initial set. The removed positions affect only this rule, and its entire result has already been supplied. Write $F(D)$ for the terminal support obtained by consuming in rule order. Equivalently, form the ordinary closure, which retains all positions, and remove the premises of rules that fired. In particular, a position whose mate cannot appear is present in the terminal support exactly when it is present in ordinary closure.

We may replace the assigned support of a port whenever it is exactly a complete pair, using the destination support of that rule. Repeat until the assigned support is a singleton, an unmatched pair, or has size at least three. The replacements terminate by the rule order, preserve all tests, and use supports already computed in the reversed graph. The same starting support gives the same replacement on either side. Use $D(v)$ henceforth for the assigned support after these replacements. In particular, every assigned support of size two is terminal.

On either physical side the assigned supports form an antichain because the corresponding neighborhoods form an antichain. Call a port *singleton* if its assigned support has one position. A port of size at least two is *shared* if its support is also assigned on the other physical side, and *exclusive* otherwise. A position assigned to a singleton port on a side cannot appear in the ordinary closure of a different port on that side. Its presence would make the latter accept every neighbor of the singleton port. The same argument applies to an output of a rule whose support contains that of a different port on the same side. A rule firing on a single port also cannot output a superset of that port's own support. At least one position in its start must be no later than the rule for the rule to fire. The output position is absent from every single-port closure.

If $\{q\}$ is a singleton port adjacent to $v$, then its mate must be present in $F(D(v))$. Otherwise adding $q$ to that terminal support cannot initiate a rule. No two opposite-side singleton ports can be adjacent. An edge between them would force their positions to be mates. Any other neighbor of one of these ports would then have the other port's singleton position in ordinary closure, contradicting the antichain on that side. Such another neighbor exists because each degree is three.

Each block therefore has at most four singleton ports, and any block with at least three has them all on one side. A *full block* has four and a *triple block* has three. In a full block, let $B$ be the four mates of its singleton positions. The four ports on the opposite side each need one of the four complementary triples of $B$ in their terminal supports. In a triple block, the port opposite the missing singleton label needs the whole triple $U$ of mates. Call these the *required triples*. For a fixed physical side of the ports that need these triples, their groups $B,U$ are pairwise disjoint. Indeed the singleton ports opposite that side have distinct positions and taking mates is injective.

## A bound for shared ports on one side

Fix the physical side of the ports with required triples. Denote by $P_4$ and $P_3$ the numbers of shared ports on this side with a required triple from a full block or a triple block, respectively. Let $m$ be the number of union outputs of size at least two assigned to no port on either side. We prove

$$
P_4+2P_3\le 2m. \tag{1}
$$

### Saturation of helper supports

Let $J$ be the union of the singleton positions of both physical sides. Call an unassigned union output an *admissible helper* if its support avoids $J$ and $o$ and contains no support of a port of size at least two from either side. A helper's nonsingleton operands satisfy the same conditions. Let $m_0\le m$ count the admissible helpers and let $W$ be the union of their supports.

In the single-port run of a shared port, all positions of $J$ are excluded by the antichain on the corresponding side. Every rule that fires therefore outputs either a singleton outside $J\cup\{o\}$ or an admissible helper. For the latter conclusion, any assigned support contained in a rule output would violate either the antichain or the rule order, as above. Retain only the rules with these two types of outputs. This keeps the whole single-port run of any shared port, and also the run of any subset of its start. All operands of size at least two of an assigned shared support are admissible by the antichain on both sides. For each of the ports counted by $P_4,P_3$, the start has size at least three because singletons and assigned pairs are terminal. Consequently its start is $H\cup H'$ or $H\cup\{x\}$, for admissible helpers $H,H'$ and a position $x$ outside $J\cup\{o\}$.

Let $B^*$ be the union of the $B,U$ groups on the fixed side with at least one counted port. A position in $B^*$ will be called useful. Its mate lies in $J$, so a useful position is never consumed in retained runs starting from sets that avoid $J\cup\{o\}$. In ordinary closure from $W$ or $W\cup\{x\}$ we can discard all rules whose outputs are contained in $W$. The remaining rules each produce a single position outside $W$.

Run these remaining rules on $W$ with consumption and let $T$ be the terminal set. Put $V=T\cap(B^*\setminus W)$, $v=|V|$, and $a=|W\setminus B^*|$. There are at most $a-2v$ auxiliary positions in $T$, because each new useful position costs two auxiliary premises and all other rules also decrease the number of auxiliary positions. Replacing $W$ by $T$ before adding an extra $x$ preserves all useful positions reached. A useful extra $x$ contributes itself and cannot fire a rule. An auxiliary extra can start a rule only if its mate is in $T$. Every additional firing must consume a position outside the original $T$ and can emit at most one new such position. Thus at most one new useful position is reached, and there are at most $a-2v$ possible extra positions that could start such a run. Denote the set of all resulting useful positions by $E_{\mathrm{pos}}$, and put

$$
K=(W\cap B^*)\cup V\cup E_{\mathrm{pos}}.
$$

Then $|K|\le |W|-v$. Each counted start is contained in $W$ or $W\cup\{x\}$. By monotonicity of ordinary closure and persistence of useful positions, each counted terminal support contains at most one useful position outside $K$. If its required triple contains such a position $x$, the actual start must be $H\cup\{x\}$ with $H$ an admissible helper and $x$ useful. Adding $x$ to $H$ changes no rule firing, so the other two required positions belong to $F(H)$ in the retained program before discarding rules with outputs in $W$.

### Charging the missing positions

When a full block has $q$ counted ports, the minimum number of its positions in $K$, for $q=0,1,2,3,4$, is bounded below by $0,2,2,3,3$, respectively. A required triple needs two positions in $K$. Two positions of a four-set belong together to only two of its complementary triples, which explains the bound for $q\ge3$. A counted triple block needs two positions of its $U$ in $K$. Thus

$$
P_4+2P_3\le |K|+c,
$$

where $c$ counts full blocks whose four ports are shared and whose $B$ has a position outside $K$. For each of these blocks the missing position $x$ is unique. For the three requirements containing $x$, the corresponding supports $F(H)$ must contain the three pairs of $B\setminus\{x\}$, one each. These three normalized supports must be distinct. If two were equal, adding the same $x$ would give equivalent starts for two ports on the same side.

Among the $m_0$ admissible helpers, call a support of size two a base pair and call the other supports large. Fix the two operands of each helper in the union graph. Let $\ell_1$ count large helpers with one earlier helper and one position as operands and let $\ell_2$ count large helpers with two earlier helper operands. Put $\ell=\ell_1+\ell_2$ and let $\omega$ count repeated positions among the base pairs, so

$$
 \omega=2(m_0-\ell)-\left|\bigcup_{\text{base pairs }H}H\right|.
$$

A large helper contributes at most one new position to the union of earlier supports in the first case and zero in the second. Hence

$$
 |W|\le 2m_0-\ell-\ell_2-\omega. \tag{2}
$$

Split the $c$ blocks into $c_2$ blocks with at least two declared base pairs inside $B\setminus\{x\}$ and $c_1=c-c_2$ other blocks. Two pairs in the same three-set overlap. The three-sets of these blocks are disjoint, so $c_2\le\omega$.

For a block counted by $c_1$, at least two of the three pair requirements must be realized by normalizations of large helpers. To see this, start from a base pair. Every firing while the current support has size two replaces the entire pair by the next output. If the run terminates without reaching a large helper, any resulting pair must be a declared base pair. If the run reaches a large helper $H'$, the remaining run is exactly the normalization from $H'$, by the rule order. Thus at most one of the three requirements can be met exclusively by base pairs. The other two normalized supports of large helpers are distinct and together contain all three positions of $B\setminus\{x\}$.

Let $W_L$ be the union of the large helper supports. In topological order of their construction, each large helper contributes at most three new positions if it has one helper operand and at most four if it has two. For the first assertion, its helper operand is either a pair or already in the union of earlier large supports. For the second, a base pair contributes at most two and any earlier large support contributes zero. Therefore $|W_L|\le 3\ell_1+4\ell_2=3\ell+\ell_2$.

Start the retained program from $W_L$ and drop rules whose outputs lie entirely in $W_L$. These rules do not enlarge its ordinary closure. The rules left have output size at most two, so consumption never increases the size of the state. All useful positions in $F(H)$ for any large helper $H$ appear in the ordinary closure of $W_L$, and cannot be consumed in its reduced run. The $c_1$ groups furnish $3c_1$ distinct such positions. It follows that

$$
3c_1\le |W_L|\le 3\ell+\ell_2,\qquad
c\le \ell+\ell_2/3+\omega.
$$

Combining these estimates with (2) gives

$$
P_4+2P_3
 \le |K|+c
 \le 2m_0-\tfrac23\ell_2-v
 \le 2m.
$$

## Combining the two sides

Write $h=2k+b$. If $\delta$ is the deficit of the total number of singleton ports from $4k$, the number of nonsingleton ports is $4k+\delta$. One union output can be assigned at most once per side. The number of exclusive ports is thus $E=2b-\delta-2m$. Let $f_4,f_3$ denote the numbers of full and triple blocks, and partition $E$ into $E_4,E_3,E_0$ according to whether the port has a required triple from a full block, a required triple from a triple block, or neither.

Sum (1) over the two sides to get $4f_4+2f_3-E_4-2E_3\le4m$. Substituting for $E$ gives

$$
4b\ge 4f_4+2f_3+2\delta+E_4+2E_0\ge4k.
$$

In the last step the contributions to $4f_4+2f_3+2\delta$ for blocks with $4,3,2,1,0$ singleton ports are $4,4,4,6,8$. Therefore $h\ge3k$, and $s\ge8k-1+h\ge11k-1$.

## Equality in the lower bound

Assume $s=11k-1$. Then $b=k$ and every block has at least two singleton ports. Also $E_4=E_0=0$, so every exclusive port must have the required triple of a triple block. On each side $P_4+2P_3=2m$. We analyze the consequences of equality in (1) with that physical side fixed.

### Every helper is a disjoint pair

All the charging inequalities are equalities. In particular $m_0=m$, $\ell_2=v=0$, $|K|=|W|=2m-\ell-\omega$, and $c_1=\ell,\ c_2=\omega$. Also $|W_L|=3\ell$. Each large helper contributes three new positions to $W_L$, so it has a base pair and one position as its operands, and the large supports are disjoint triples.

The reduced run from $W_L$ that drops rules with outputs in $W_L$ ends with at least $3\ell$ useful positions from the $c_1$ groups. As its size cannot increase, its terminal set has size $3\ell$ and consists entirely of useful positions. No rule dropped in this run can fire on an individual start $H$ from the family of large helpers. Otherwise, both of its premises would be reached in ordinary closure from $W_L$, also after dropping such rules. The dropped rule is their unique consumer and both premises are auxiliary. They would then persist in the reduced terminal set, a contradiction.

Thus in the normalization from any large $H$ all fired rules have outputs of size at most two, so $|F(H)|\le3$. The union of these $\ell$ normalizations contains the $3\ell$ useful positions of the $c_1$ groups. They must themselves be pairwise disjoint useful triples. For each $c_1$ group, two distinct normalizations contain two pairs of its three-set. These pairs intersect, contradicting disjointness when $c_1>0$. Hence $\ell=0$.

With only base pairs, every block counted by $c$ needs all three pairs of its remaining three-set as declared helpers. These contribute three repeated positions per block, or $\omega\ge3c$. But equality also gave $c=\omega$, so $c=\omega=0$ and the helpers are disjoint pairs.

### Every position of $W$ is useful for both orientations

When all helpers are pairs, the saturation argument for the counted ports works with $K'=(W\cap B^*)\cup V$, dropping $E_{\mathrm{pos}}$. For a start contained in $W$ or with a useful extra position the earlier argument already works with $K'$. If the start has an auxiliary extra outside $W$, its size is three. A rule emitting one position would reduce the size to at most two, and all rule outputs have size at most two. The terminal support requires three useful positions, so no such rule fires. All pair outputs are subsets of $W$, and the extra position is auxiliary, so all useful terminal positions in this case lie in $W$.

A full block cannot have a position outside $K'$. All four of its requirements are shared, so a missing position again needs all three pairs of its complementary three-set, impossible for disjoint helpers. The disjoint groups therefore need at least $P_4+2P_3=2m$ positions in $K'$. As $v=0$ and $|W|=2m$, we have $K'=W$. Every full group $B$ lies in $W$, and every counted triple group $U$ has exactly two positions in $W$. They exhaust $W$. This holds on both sides with the same family of helpers, since $m_0=m$. Every position in $W$ is consequently the mate of a singleton port on each physical side.

There are no exclusive ports. If one exists, take one whose assigned support is first in the union graph. Its nontrivial operands must be unassigned, since an earlier exclusive support is impossible by choice and an earlier shared support violates the antichain on its side. All unassigned supports are admissible helpers, hence are contained in $W$. The exclusive port requires a triple and therefore its start has size at least three and lies in $W$ plus at most one extra position. A first firing is impossible. No position of $W$ can participate, because each of its mates is the position of a different port on the exclusive port's side and so is absent. One extra position alone cannot start a rule. But this port needs the triple $U$ of a triple block not counted on this side, so $U$ is disjoint from $W$. This contradicts its terminal requirement.

### Parity

All nonsingleton ports now have shared supports. Each such support pairs a row with a column. Swapping all these pairs preserves adjacency in the graph induced by the nonsingleton ports, since evaluation on the union of two supports is symmetric in them. It also preserves graph degrees. The two ports in a pair are nonadjacent since the test is equivalent to activating one port alone.

If a singleton position $q$ occurs on both sides, the two ports have the same set of neighboring shared supports. This follows by evaluating each test starting with $\{q\}$ and the shared support. Consider $w\in W$ and its mate $q$, which is a singleton position on both sides. For a singleton in a full block, all its neighbors are isolated vertices of the induced graph, because none of the ports on its own side in its block are nonsingleton. For a singleton in a triple block, two of its three neighbors are nonisolated, because they are also adjacent to the unique nonsingleton port on the singleton's side in that block. Thus a position of $W$ associated with a full group on one side must be associated with a full group on the other side. Each full group contributes four positions, and each triple group contributes two. The counts of full blocks in the two orientations are equal, as are the counts of triple blocks. Both types therefore occur an even number of times.

Among the blocks with two singleton ports, those of orientations $(2,0)$ and $(0,2)$ contribute connected induced components with respective side sizes $2,4$ and $4,2$. These counts are equal by the side-swapping involution. A block of type $(1,1)$ has its two singletons at the same label since they are nonadjacent. Its induced graph is a connected three-by-three crown. Other blocks have no component of these side sizes. If $k$ were odd, an odd number of such three-by-three crowns would remain, so one would be fixed by the involution.

Within that fixed block, the three nonsingleton pairs must be diagonal, since each pair is nonadjacent. Let $\alpha,\beta$ be the mates of the singleton row and singleton column of the block. They lie outside $W$ by disjointness of groups in each orientation. Each of the three shared supports must contain $\alpha,\beta$ in its terminal support. In fact all assigned nonsingleton supports are terminal in the equality case. Assigned pairs are terminal by the initial replacements. A large assigned support starts with positions of $W$ and at most one outside, and therefore cannot initiate a rule on its own because the mates of positions of $W$ are absent.

If $\alpha\ne\beta$, no large start can contain both. Each of the three starts would have to be the same pair $\{\alpha,\beta\}$, against the antichain. If $\alpha=\beta=\gamma$, any large start must be contained in $W\cup\{\gamma\}$. Every position in this set is mated to an element of $J$, and no shared start contains an element of $J$. The union of this large start and another terminal shared start could therefore initiate no rule, though the corresponding off-diagonal test is positive. So the three starts must be pairs $\{\gamma,x_i\}$ with distinct $x_i$. To initiate a rule on the union of any two, their $x_i$'s must be mates, since the mate of $\gamma$ is absent. This is impossible for three distinct positions.

The fixed three-by-three component is impossible. Thus $s=11k-1$ requires even $k$, and the upper constructions give the claimed formula for every $k\ge1$.
