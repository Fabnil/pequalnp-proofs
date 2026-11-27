# A five-by-five crown with one edge removed needs 15 gates

The matrix with mask $32435687$ in [L-meta-25467](https://pequalnp.com/desk/row?gap=L-meta-25467) has minimum size **15** in the one-row/one-column promise model with monotone gates of fan-in at most two. The lower bound allows arbitrary sharing and AND depth. Lean checks the original mask, its relabeling, its neighborhood inclusions, and the 15-gate witness. [Lean file](CrownMissingCell.lean)

## Matrix and upper bound

Number the rows $0,\ldots,4$ and read the columns in the original order $3,4,2,1,0$. The normalized adjacency is

$$
A_{ij}=1\quad\Longleftrightarrow\quad i\ne j\ \text{and}\ (i,j)\ne(0,1).
$$

Call $0,1$ special labels and $2,3,4$ ordinary. The only strict neighborhood inclusion among rows is $N(r_0)\subset N(r_1)$, and among columns it is $N(c_1)\subset N(c_0)$. In particular every ordinary port is incomparable with every other port on its side.

Merge each ordinary diagonal pair by OR and denote the three signals by $x,y,z$. Compute both $T=xy\lor((x\lor y)z)$ and $U=(x\lor y)\lor z$ with five gates, sharing $x\lor y$. Compute $V=r_0\lor r_1\lor c_0\lor c_1$ with three gates. Finally OR together $T$, $U\land V$, and $r_1\land c_0$ with four gates. The three terms cover ordinary–ordinary cells, ordinary–special cells, and the single positive special–special cell, respectively. Including the diagonal merges gives $3+5+3+4=15$ gates.

## Supports after transposing ORs

Take a minimum circuit with $s$ gates. Every port is essential with a negative singleton test. Remove unused gates, constants, and unary operations. Cut each AND into two distinct operand positions and one new source at its output, and reverse all OR edges as in the [general transposition argument](crown-all.md#transposing-the-or-graph). The ten raw ports and the AND outputs now denote sets of reached positions. There are $s+1-10$ binary unions before deduplicating supports. Each position other than the final output has a unique mate, the other operand position of its AND. A pair of mates fires its rule and produces a set of strictly later positions or the final output.

Write $h$ for the number of distinct nonsingleton outputs of the union graph. Each such output is a union of two proper subsets from earlier outputs or singleton positions. If $s\le14$, then $h\le5$. For a raw port $v$, let $D(v)$ denote its assigned start. Let $F_v$ denote its terminal version, obtained by consuming matched pairs in rule order and adding their destinations. These replacements preserve the results of all tests with $v$. For a start of size two, make the replacements on the entire assigned set until it is a singleton, an unmatched pair, or a larger support. This keeps it among the supports computed by the union graph and ensures every assigned pair is terminal. A *singleton port* has $D(v)=\{q\}$. To be adjacent to it, a port must have the mate of $q$ in its terminal support.

If $D(v)$ or $F_v$ contains another port's start from the same side, the latter's neighborhood is contained in $N(v)$ by monotonicity. This also holds if the other start is reached partway through the ordinary, non-consuming closure. Hence assigned starts are distinct on each side and so are the corresponding terminal supports. In particular, if $v$ is ordinary, no singleton position of a different port of its side can be reached on $v$ alone. An AND firing on $v$ alone also cannot emit $D(v)$, since some position of $D(v)$ must be at or before that rule, and all destinations are later.

A nonsingleton start shared across the sides pairs one row with one column. This pair must be a zero cell since the union of their two equal starts gives a negative single-port test. If two shared starts pair $(r_i,c_j)$ and $(r_{i'},c_{j'})$, the cross-tests $A_{ij'}$ and $A_{i'j}$ must agree by symmetry of the union of the starts. An ordinary shared start can only pair the row and column of its ordinary label. Distinct ordinary shared starts are thus pairwise adjacent in both directions.

## Two consequences for terminal supports

**Two pairs with a common mate.** Suppose terminal pairs $\{\gamma,x\}$ and $\{\gamma,y\}$ are adjacent, where the mate of $\gamma$ is absent from both. Their union must fire at least one rule, so $x,y$ are mates. A third terminal support avoiding the mate of $\gamma$ cannot be adjacent to both pairs. Its union with the first pair would require $y$ in the third support, and its union with the second would require $x$. This is incompatible with terminality. In particular three pairwise adjacent pairs cannot share $\gamma$ in the absence of its mate.

**Three ordinary shared starts needing the same two distinct mates.** Let $m$ count union outputs assigned to no raw port on either side. Suppose three ordinary shared starts all need $\alpha,\beta$ in their terminal supports, where $\alpha\ne\beta$ and both are mates of singleton positions. This is impossible if $m\le1$.

Indeed, any nonsingleton operand of an ordinary shared start has to be unassigned. An assigned operand would violate incomparability on the side of its assignment. If $m=0$, the three starts are terminal pairs and all would equal $\{\alpha,\beta\}$.

For $m=1$, at most one terminal support can equal $\{\alpha,\beta\}$, so two or more must have size at least three. Each such start has the form $H\cup\{x\}$ with $H$ the sole unassigned helper. The proper subsets used to build $H$ must also be unassigned if nonsingleton, so $H$ is a pair. During an ordinary shared port's single-port run, any nonsingleton output other than $H$ would be an assigned start. An assigned start from a different port is excluded by incomparability on the side of that assignment. Emitting its own start is excluded by rule order. If a first rule fires on $H\cup\{x\}$, it consumes a position of $H$. It cannot emit $H$, and neither can any later rule. All outputs in this run are then singletons, so its terminal support has size at most two.

The two larger terminal supports therefore are distinct unchanged triples $H\cup\{x\}$ containing $\alpha,\beta$. Their intersection is $H=\{\alpha,\beta\}$. Each of the three terminal supports contains $H$ and at most one extra position. The mates of $\alpha,\beta$ are singleton positions and are excluded from every ordinary shared run by incomparability on their respective sides. Thus a positive test between two of the three supports would require their extra positions to be mates. Three pairwise positive tests are impossible under this requirement.

## Excluding five or fewer unions

First, two opposite-side singleton ports cannot be adjacent. Their positions would be mates, and each other row adjacent to the singleton column would reach the singleton row's position on its own. Its neighborhood would then contain that of the singleton row. Each column has at least two such other neighbors, while every row has at most one strict upper neighbor in the inclusion order. This is impossible. Therefore the rectangle between the singleton sets lies in the zero cells, namely the diagonal and $(0,1)$.

### A side without singleton ports

If there are no singletons on either side, both sides use all five union outputs and all five starts are shared. The full matching between starts must be diagonal. Using the extra zero cell $(0,1)$ would leave column $0$ unmatched. The two special shared starts then violate cross-test symmetry.

Otherwise assume that only columns have singleton ports. The case of only rows is obtained by transposing and exchanging labels $0,1$, which preserves $A$. All five union outputs are assigned to rows. A row start of size at least three needs a smaller nonsingleton operand assigned to a row, and the only permitted inclusion is from $r_0$ to $r_1$. Thus all other row starts are terminal pairs.

If there are at least four singleton columns, every ordinary row needs at least three mates. With exactly three singleton columns, an ordinary row whose label is absent from the three also needs all three mates. If the three are precisely the ordinary columns, $r_0$ needs all three. These all conflict with the pair sizes. With two singleton columns including at least one special label, two of the ordinary rows are adjacent to both columns. If both singleton columns are ordinary, the remaining ordinary row and $r_0$ are adjacent to both. In each case two distinct row pairs would have to contain both mates.

With one singleton column of ordinary label, both special columns have shared starts. Column $0$ can only share with row $0$, so column $1$ must share with row $1$. Their cross-tests disagree. If the singleton column is special, all three ordinary columns have shared starts that are terminal pairs, since their matching rows are ordinary. Each pair contains the mate of the singleton column's position. The singleton position is absent from each by column incomparability. These three pairs contradict the two-pair observation.

### Two nonempty singleton sets

The zero rectangle between the singleton sets has sizes $(1,1),(1,2)$, or $(2,1)$. Each size-two set must use both special labels. Consequently $h\ge4$. Cases $(1,2)$ and $(2,1)$ are transposes after relabeling, so take the singleton ports to be $r_0,c_0,c_1$. The four nonsingleton rows and three nonsingleton columns give $7-h+m$ shared starts, all ordinary. There is at most one unassigned helper, because the rows assign four outputs. If there is none, at least two ordinary shared terminal pairs require the same two distinct mates of $c_0,c_1$, impossible. If $m=1$, necessarily $h=5$ and there are three ordinary shared starts. They are excluded by the two-distinct-mates argument.

It remains to consider one singleton row and one singleton column. There are $8-h+m\ge3$ shared starts with $m\le1$.

- **Different singleton labels.** The only possible zero cell of distinct labels is $(0,1)$. The other ports can share only at the three ordinary labels. Thus $h=5,m=0$ and all three ordinary starts are shared terminal pairs. Each needs both singleton mates. Distinct mates force equal pairs. If the mates coincide, the two-pair observation forbids the three positive cross-tests.
- **The same special label.** At least two ordinary starts are shared. If $m=0$ and the singleton mates differ, both ordinary shared pairs would be equal. If the singleton mates coincide, the singleton positions also coincide, so a shared start at the other special label would make the two unequal special cross-tests equal. For $m=0$, this forces all three ordinary starts to be shared pairs, which the two-pair observation excludes. For $m=1$, there are four shared starts, including the other special label, so the mates must be distinct. The three ordinary shared starts then violate the two-distinct-mates argument.
- **The same ordinary label.** Both special labels cannot share starts at once, since then their matching would be diagonal and their cross-tests would disagree. There are thus exactly three shared starts, consisting of the other two ordinary labels and one special row-column pair. This forces $h=5,m=0$. The ordinary shared starts are terminal pairs and need both singleton mates. Distinct mates force equality. With one common mate $\gamma$, the mate of $\gamma$ is absent from the three terminal supports, because the singleton ordinary label's neighborhood cannot be contained in that of any other port on its side. The two ordinary pairs are adjacent and the third support must be adjacent to both. The two-pair observation gives a contradiction.

This exhausts $h\le5$ and hence excludes $s\le14$. The 15-gate upper bound gives the minimum.
