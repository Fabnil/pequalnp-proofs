# A necessary read bound for L-meta-10025

Let \(R_i=A_i\times B_i\) be a cover by at most 15 all-zero rectangles of the [Desk matrix for L-meta-10025](https://pequalnp.com/desk/row?gap=L-meta-10025). At least **16 of the 25 rows** belong to at least three of the sets \(A_i\). The argument uses two finite computations described below. It leaves the existence of a 15-rectangle cover open.

The 25 rows are points of \(\mathbb F_5^2\), the 30 columns are affine lines, and the ones are incidences. In the order of the Desk matrix, point \((x,y)\) has index \(5x+y\), and the line \(y=sx+b\) has index \(5s+b\). The vertical line \(x=b\) has index \(25+b\). Each line has five points and each point has 24 zero columns.

## Rows with at most two reads

Write \(S(p)=\{i:p\in A_i\}\) for a point's read set. If \(p\ne q\), then \(S(p)\not\subseteq S(q)\). A line through \(q\) avoiding \(p\) gives a zero in row \(p\) which any rectangle containing \(q\) cannot cover. More generally, if \(p,q,r\) are distinct and \(S(p)\subseteq S(q)\cup S(r)\), then \(p,q,r\) are collinear. Otherwise the line through \(q,r\) gives the same contradiction.

Let \(m\) be the number of points with at most two reads, so \(H=25-m\) points have at least three. For each of the \(t\) low-read points that belongs to a rectangle with a singleton row set, select one such rectangle. The other \(r=m-t\) low-read points each have exactly two reads. A single read in a nonsingleton row set would violate the previous paragraph. For a point \(p\) with two nonsingleton reads \(i,j\), the row sets \(A_i,A_j\) intersect only at \(p\). For every \(q\in A_i\setminus\{p\}\) and \(v\in A_j\setminus\{p\}\), the three points \(p,q,v\) lie on a line. Holding either of \(q,v\) fixed shows that both row sets lie on a single line, which we assign to \(p\).

The \(q_0\) rectangles read by these \(r\) points can each be labelled by a unique line. Every such rectangle has at least two rows, so its label is the same for each point inducing it. There are \(u\) rectangles left over, hence the total is \(s=q_0+t+u\le15\). Call a line *active* if it labels one of the \(q_0\) rectangles. Write \(k\) for the number of rectangles with that label, and \(a\) for the number of points assigned to the line. Over the active lines, \(\sum k=q_0\), \(\sum a=r\), and \(q_0\le 2r\). Also \(1\le a\le\min(5,\binom{k}{2})\), since each assigned point reads a distinct pair of rectangles on the line.

For each active line put \(d=5k-4a\). Checking \(k=2,3\) and then using \(k\ge4\), \(a\le5\) gives

\[
 d\ge0,\qquad 3(5-a)\le 2d,\qquad \sum d+t=5s-5u-4m.
\]

In particular, \(4m\le5(s-u)\). A point with at least three reads cannot read a selected singleton. If such a point lies on no active line, its read set is contained in the \(u\) leftover rectangles. If there are \(o\) such points, then

\[
 3(25-m-o)\le 2\sum d\le 2(75-5u-4m). \tag{1}
\]

## Zero, one, or two leftover rectangles

For \(u\le2\), every high-read point lies on an active line. If a high-read point is on exactly one active line then it uses only rectangles labelled by this line and leftover rectangles. Count an incidence for each high-read point on each active line, with a second count for those on exactly one. Each high-read point contributes at least twice. A line contributes at most \(5-a+U\), where \(U\) is an upper bound on its high-read points on no other active line.

| \(u\) | \(U\) for \(k=2\) | \(U\) for \(k=3\) | \(U\) for \(k\ge4\) | Upper bound for \(5-a+U\) |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 1 | \(5-a\) | \(3k-2a\) |
| 1 | 1 | \(5-a\) | \(5-a\) | \((11k-7a)/3\) |
| 2 | 2 | \(5-a\) | \(5-a\) | \((14k-10a)/3\) |

When the available pool has exactly three rectangles, at most one point can read three of them, by distinctness of the read sets. For \(u=2,k=2\), the single paired point on the line reads both labelled rectangles. No other point can read both, so any high-read point on this line alone must read both leftover rectangles and one of the two labelled rectangles. This gives \(U\le2\). The last column follows by substituting the ranges of \(a\) for \(k=2,3\) and using \(5-a+U\le2(5-a)\) for \(k\ge4\).

Summing the last column and using \(2H\le\sum(5-a+U)\) gives the following exclusions.

- \(u=0\) gives \(50-2m\le3s-t-2m\le45-2m\).
- \(u=1\) gives \(150+m+4t\le11(s-1)\le154\). Thus \(s=15\), \(t=0\) and \(m\le4\), while \(14=q_0\le2r=2m\).
- \(u=2\) gives \(150+4m+4t\le14(s-2)\). Since \(s-2\le2m-t\), the only possibilities for \((s,m,t)\) are \((15,7,0),(15,8,0),(15,7,1)\).

For the last three possibilities the total slack in the last column, after multiplying by three, is at most \(4,0,0\), respectively. For \((k,a)=(2,1),(3,3),(3,2)\) the line slack is \(0,0,4\). It is at least 8 for \((3,1)\) and at least 6 for \(k\ge4\). Matching \(\sum k=q_0\) and \(\sum a=r\) forces the following cases.

| \((m,t)\) | Number of \((2,1)\) lines | Number of \((3,3)\) lines | Number of \((3,2)\) lines |
| --- | ---: | ---: | ---: |
| \((7,0)\) | 5 | 0 | 1 |
| \((8,0)\) | 5 | 1 | 0 |
| \((7,1)\) | 6 | 0 | 0 |

The slack is exhausted in each case, so every \((2,1)\) line has exactly two high-read points on no other active line. Pick such points \(p,x\) on two distinct \((2,1)\) lines. The one labelled rectangle read by \(p\) also contains the paired point \(v\) on \(p\)'s line. The line through \(v,x\) avoids \(p\) because \(x\) is off \(p\)'s line. This line cannot be in the labelled rectangle read by \(p\), since it contains \(v\). It cannot be in either leftover rectangle, since \(x\) reads both. The zero for \(p\) and this line is therefore uncovered. This excludes \(u=2\).

## Three or more leftover rectangles

For \(u=3,4\) the antichain of read sets contained in the leftover rectangles has at most 1 or 4 members, respectively. Every member has size at least three. Inserting these bounds for \(o\) in (1) gives \(m\le9\) in both cases.

For \(u=5\), there are at most eight high-read points whose read sets are contained in the leftover rectangles. To see this, suppose there are at least nine. A five-element set would exclude all others. With \(b>0\) four-element sets, the triples must avoid being contained in any of them, so their number is at most \(\binom{5-b}{2}\). The total \(b+\binom{5-b}{2}\) is at most seven. Thus there are at least nine of the ten possible triples. Choose two, \(S(p)\) and \(S(q)\), sharing two elements. There are six triples containing the element in \(S(p)\setminus S(q)\), and at least five occur. One is \(S(p)\) and at least four others each belong to some point \(v\) satisfying \(S(p)\subseteq S(q)\cup S(v)\). These four points must all lie on the line through \(p,q\), which has only five points. Now (1) with \(o\le8\) gives \(m\le9\).

For \(u=6\), \(m\le11\). If \(m=11\), the total deficit is at most one, so every active line is full with \(a=5\). None of the 14 high-read rows can read a labelled rectangle. They need \(14\cdot24=336\) zero cells, while the six leftover rectangles contain at most \(6\cdot54=324\). Here 54 is the maximum rectangle area computed below.

If \(u=6\) and \(m=10\), then \(\sum d\le5\). There can be at most one active line with \(a<5\), whose type must be \((k,a)=(4,4)\) or \((3,3)\). The first has at most one high-read point, hence can contribute at most 24 distinct high-read zero cells. With \((3,3)\), the three paired points read all three pairs of labelled rectangles. Each of the at most two high-read points on the line can read at most one of these rectangles, by the antichain property. Such a rectangle contains two paired points and the high-read point. Three collinear points meet 16 lines, so the rectangle has at most 14 columns. The contribution is at most 28 cells. In all cases the total from labelled and leftover rectangles is at most \(28+324=352<360=15\cdot24\).

For \(u=7\), the deficit bound gives \(m\le10\). Equality forces \(s=15\), \(t=0\), and zero deficit. The only zero-deficit active type is \((k,a)=(4,5)\), so there are two full active lines. They are parallel because a point at their intersection would be assigned both labels. The seven leftover rectangles would therefore have to cover all 360 zero cells for points on the other three parallel lines. The finite search below excludes this case. Finally, \(u\ge8\) gives \(4m\le5(15-u)\le35\). Together the cases give \(m\le9\).

## Finite checks

Each maximal rectangle is obtained by intersecting the zero masks of a set of rows, then including every row whose zero mask contains that intersection. This generates every maximal rectangle with nonempty sides. On all 25 rows the enumeration gives 360,905 maximal rectangles and maximum area 54. In any 15-rectangle cover at least one rectangle has area at least 40. There are 53 affine equivalence classes of maximal rectangles of area at least 40, giving 53 possibilities for such an anchor up to symmetry.

For the case \(u=7,m=10\), normalize the two removed parallel lines to \(x=0,1\). Each of the seven rectangles would need area at least \(360-6\cdot54=36\), and at least one must have area 54 because the next largest area is 50. There are 11,075 candidate maximal rectangles of area at least 36 on the remaining 15 points. The 50 candidates of area 54 form one orbit under affine maps preserving the two removed lines as a set. Fix an area-54 representative.

The search chooses one uncovered cell and branches over every viable rectangle covering it. If there are \(b\) slots and \(M\) uncovered cells, each chosen rectangle must cover at least \(M-54(b-1)\) uncovered cells. The search also rejects a branch where some uncovered cell has no viable rectangle or the sum of the \(b\) largest gains is below \(M\). Both the required gain and the filtering are valid for all remaining rectangles, since using a slot adds at most 54 new cells. The search exhausts the single anchored case in 147 nodes.

```sh
c++ -O3 -std=c++17 search_seven.cpp -o search_seven
python3 enumerate_rectangles.py > restricted-seven.txt
./search_seven < restricted-seven.txt
```

The expected final line is `anchor 0 excluded 147 nodes`.
