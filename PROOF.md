# Proof

This file gives the complete argument. Section numbers match the PDF in `paper/`.

## 0. Definitions and standard facts

A 0/1 matrix $T$ with row set $R$ and column set $C$ is identified with its set of ones. A *rectangle* is a set $R'\times C'$ with $R'\subseteq R$, $C'\subseteq C$. The **binary rank** $\mathrm{br}(T)$ (Watson writes $\mathrm{rank}_{0,1}$) is the least number of all-ones rectangles that partition the ones of $T$. The Kronecker power $T^{\otimes k}$ has rows $R^k$, columns $C^k$, and entry $\prod_i T(r_i,c_i)$.

We use the following standard facts.

- (F1) $\mathrm{br}$ does not change under transposition or permutation of rows and columns, and does not increase when rows or columns are deleted.
- (F2) $\mathrm{br}(A\otimes B)\le \mathrm{br}(A)\,\mathrm{br}(B)$: products of the rectangles of two partitions form a partition of $A\otimes B$.
- (F3) If $\{(r_j,c_j)\}_{j\in J}$ is a *fooling set* of $T$ (all $T(r_j,c_j)=1$, and for $j\ne j'$ one of $T(r_j,c_{j'})$, $T(r_{j'},c_j)$ is $0$), then $\mathrm{br}(T)\ge |J|$: no two of the pairs lie in one all-ones rectangle. If $J$ is a fooling set of $T$, then $J^k$ is a fooling set of $T^{\otimes k}$: two different tuples differ in some coordinate $i$, and a zero in coordinate $i$ makes the whole product zero.

**Watson's matrix.** In the proof of Theorem 2(2) of Watson (2016),
$$
M=\begin{pmatrix}1&1&1&0&0&0\\1&0&0&1&1&0\\0&1&0&1&0&1\\0&0&1&0&1&1\\1&1&1&1&1&1\end{pmatrix},
$$
with $\mathrm{rank}_+(M)=4$ and $\mathrm{br}(M)=5$. Watson states:

> Conjecture 1. For all $k$, $\mathrm{rank}_{0,1}(M^{\otimes k})=5^k$.

Watson also notes that $\mathrm{rank}_+(M^{\otimes k})=\mathrm{fool}(M^{\otimes k})=4^k$.

**Graph matrices.** Let $G=(V,E)$ be a finite loopless multigraph. $T_G$ has rows $E$ and columns $\{0\}\sqcup V$, and
$$
T_G(e,0)=1,\qquad T_G(e,v)=1\iff v\text{ is an endpoint of }e .
$$
For $K_4$ with vertices $1,2,3,4$ and edges $12,13,14,23,24,34$, the transpose $M^{\mathsf T}$ is exactly $T_{K_4}$: the columns of $M$ are the edges, row $i\le 4$ of $M$ is vertex $i$, and the all-ones bottom row is the column $0$. By (F1), $\mathrm{br}(M^{\otimes k})=\mathrm{br}(T_{K_4}^{\otimes k})$.

## 1. The code rule

Fix $k$. For $x\in(\{0\}\sqcup V)^k$ write $Z(x)=\{i: x_i=0\}$. A set $C\subseteq\mathbb F_2^k$ has the **face property for $Z\subseteq[k]$** if every face $\{y': y'_i=y_i\ (i\notin Z)\}$ contains exactly one point of $C$.

Give each edge $e$ a labelling $\lambda(e,\cdot)$ of its two endpoints by $0$ and $1$ (one endpoint each). For $e\in E^k$ and $v\in V^k$ with $v_i\in e_i$ put $y(e,v)=(\lambda(e_i,v_i))_i\in\mathbb F_2^k$.

**Theorem 1.** Let $(C_Z)_{Z\subseteq[k]}$ be a family such that $C_Z$ has the face property for $Z$, and let $t$ be the number of distinct sets among the $C_Z$. Then
$$
\mathrm{br}\big(T_G^{\otimes k}\big)\ \le\ |V|^k\, t .
$$

*Proof.* For $v\in V^k$ and a set $C$ of the family, let
$$
\mathcal R_{v,C}=\{e\in E^k:\ v_i\in e_i\ \forall i,\ y(e,v)\in C\}\ \times\ \{x:\ x_i\in\{0,v_i\}\ \forall i,\ C_{Z(x)}=C\}.
$$
There are at most $|V|^k t$ of these sets. Each is a rectangle. It is all-ones: in coordinate $i$, either $x_i=0$, or $x_i=v_i$, which is an endpoint of $e_i$.

Let $(e,x)$ be a one of $T_G^{\otimes k}$ and $Z=Z(x)$. For $i\notin Z$, the column $x_i$ is an endpoint of $e_i$; let $y_i=\lambda(e_i,x_i)$. By the face property there is exactly one $y^\circ\in C_Z$ with $y^\circ_i=y_i$ for $i\notin Z$. Put $v_i=x_i$ for $i\notin Z$, and for $i\in Z$ let $v_i$ be the endpoint of $e_i$ with label $y^\circ_i$. Then $y(e,v)=y^\circ\in C_Z$, so $(e,x)\in\mathcal R_{v,C_Z}$.

Conversely, suppose $(e,x)\in\mathcal R_{v',C'}$. Then $C'=C_{Z(x)}=C_Z$, and $v'_i=x_i=v_i$ for $i\notin Z$. So $y(e,v')$ agrees with $y$ outside $Z$ and lies in $C_Z$, hence $y(e,v')=y^\circ$. For $i\in Z$, $v'_i$ is then the endpoint of $e_i$ with label $y^\circ_i$, which is $v_i$. So $(v',C')=(v,C_Z)$, and every one lies in exactly one set. $\square$

## 2. Families from parity-check matrices

**Lemma 2.** Let $H$ be an $m\times k$ matrix over $\mathbb F_2$ and $|Z|=m$. If the columns of $H$ indexed by $Z$ form an invertible matrix $H_Z$, then $\ker H$ has the face property for $Z$.

*Proof.* Split $y=(y_Z,y_{\bar Z})$. Then $Hy=H_Zy_Z+H_{\bar Z}y_{\bar Z}$, so for fixed $y_{\bar Z}$ the unique solution is $y_Z=H_Z^{-1}H_{\bar Z}\,y_{\bar Z}$. $\square$

**Lemma 3.** Fix $m\le k$ and $N\ge 1$. Let $g_m=|\mathrm{GL}_m(\mathbb F_2)|=\prod_{i<m}(2^m-2^i)$ and
$$
\mathrm{bad}(m)=2^{m(k-m)}\big(2^{m^2}-g_m\big),
$$
the number of $m\times k$ matrices $H$ with $H_Z$ singular, for a fixed $m$-set $Z$. If
$$
\binom{k}{m}\,\mathrm{bad}(m)^N<2^{mkN},
$$
then there are matrices $H_1,\dots,H_N$ such that every $m$-set $Z$ has some $j$ with $(H_j)_Z$ invertible.

*Proof.* A union bound over the $\binom km$ sets $Z$. For a fixed $Z$, exactly $\mathrm{bad}(m)^N$ of the $2^{mkN}$ tuples fail for $Z$. $\square$

Let $t(k)$ be the least number of distinct sets in a family as in Theorem 1. Choosing, for every $m=0,\dots,k$, a number $N_m$ as in Lemma 3, and putting $C_Z=\ker H_j$ for a matrix that works for $Z$, gives
$$
t(k)\le\sum_{m=0}^{k}N_m .
$$

**A uniform choice.** For every $m$, $\prod_{i=1}^{m}(1-2^{-i})\ge \tfrac14+2^{-m-1}$. This holds for $m=1$ and passes from $m$ to $m+1$ because
$$
\big(\tfrac14+2^{-m-1}\big)\big(1-2^{-m-1}\big)=\tfrac14+2^{-m-2}\big(\tfrac32-2^{-m}\big)\ge\tfrac14+2^{-m-2}.
$$
So $\mathrm{bad}(m)\le\tfrac34\,2^{mk}$. With $\binom km\le 2^k$, Lemma 3 applies when $2^k(3/4)^N<1$, that is $N>k\ln2/\ln(4/3)=2.4094\ldots k$. The value $N=\lfloor 2.41k\rfloor+1$ works for every $m$, so
$$
t(k)\le (k+1)\big(\lfloor 2.41k\rfloor+1\big).
$$

## 3. Main results

**Theorem 4.** For every $k\ge 1$,
$$
4^k\ \le\ \mathrm{br}\big(M^{\otimes k}\big)\ \le\ 4^k\,(k+1)\big(\lfloor 2.41k\rfloor+1\big).
$$
In particular $\lim_k \mathrm{br}(M^{\otimes k})^{1/k}=4=\mathrm{rank}_+(M)$.

*Proof.* The upper bound follows from Theorem 1 with $G=K_4$, together with $M^{\mathsf T}=T_{K_4}$ and the bound on $t(k)$. For the lower bound, the pairs $(1,1),(2,4),(3,2),(4,3)$ (row, column) form a fooling set of $M$, so (F3) gives a fooling set of size $4^k$ in $M^{\otimes k}$. $\square$

**Corollary 5 (Watson's Conjecture 1 is false).** $\mathrm{br}(M^{\otimes 33})\le 4^{33}\cdot 1431<5^{33}$. Hence $\mathrm{br}(M^{\otimes k})<5^k$ for every $k\ge 33$.

*Proof.* Take $k=33$ and the values
$$
(N_0,\dots,N_{33})=(1,6,14,22,29,35,41,45,49,52,54,56,58,60,61,61,62,62,61,61,60,58,56,54,52,49,45,41,37,32,26,19,11,1).
$$
Each satisfies the inequality of Lemma 3 (exact integer check), and their sum is $1431$. Theorem 1 gives $\mathrm{br}(M^{\otimes 33})\le 4^{33}\cdot1431$. Since $(5/4)^{33}>1577>1431$, this is less than $5^{33}$. For $k>33$, (F2) and $\mathrm{br}(M)\le 5$ give $\mathrm{br}(M^{\otimes k})\le \mathrm{br}(M^{\otimes 33})\,5^{k-33}<5^k$. $\square$

The crude bound of Theorem 4 alone already gives $\mathrm{br}(M^{\otimes k})<5^k$ for all $k\ge 37$.

**Corollary 6 (Shitov's matrix).** Let $B$ be the $5\times5$ matrix of Shitov (2026), which is $M$ with one column deleted. Then
$$
4^k\le\mathrm{br}(B^{\otimes k})\le 4^k(k+1)\big(\lfloor 2.41k\rfloor+1\big),
$$
so the rate of $B$ is exactly $4$.

*Proof.* $B^{\otimes k}$ is a submatrix of $M^{\otimes k}$, so (F1) gives the upper bound. For the lower bound, $\mathrm{rank}_{\mathbb Q}(B)=4$ and real rank is multiplicative under Kronecker products, and $\mathrm{br}\ge\mathrm{rank}$. $\square$

Shitov proved $\mathrm{br}(B\otimes B)\le 24$, which gives the rate bound $\sqrt{24}\approx4.90$. Corollary 6 determines the rate.

**Corollary 7 (all graphs).** For every finite loopless multigraph $G$ and every $k$,
$$
\mathrm{br}\big(T_G^{\otimes k}\big)\le |V|^k(k+1)\big(\lfloor 2.41k\rfloor+1\big),
$$
so $\lim_k\mathrm{br}(T_G^{\otimes k})^{1/k}\le|V|$, although $T_G$ has $|V|+1$ columns.

## 4. Remarks and scope

- The proof of Corollary 5 is an existence argument (the matrices $H_j$ are chosen by counting). No explicit partition of $M^{\otimes 33}$ is given; it would have about $10^{23}$ rectangles.
- For $k=1$ the conjecture holds ($\mathrm{br}(M)=5$, Watson). For $k=2$, an unpublished SAT computation of ours (without a DRAT certificate) gives $\mathrm{br}(M\otimes M)=25$, so the conjecture appears to hold there too. The least $k$ with $\mathrm{br}(M^{\otimes k})<5^k$ is at most $33$ and is not known.
- Watson's motivation: under Conjecture 1, the matrices $M^{\otimes k}$ would separate unambiguous nondeterministic communication from the corresponding sampling problem by a factor $\log_4 5$. Theorem 4 shows that for this family the two measures agree up to $O(\log k)$ bits, since $\log_2\mathrm{br}(M^{\otimes k})=2k+O(\log k)$.
- Shitov (2026) and Poindexter (2026) showed that binary rank is not multiplicative, answering Watson's question. Their results concern squares of $5\times5$ matrices. Shitov's $B$ is $M$ with a column removed, so an upper bound for $B$ does not bound $M$. Our results do not apply to Poindexter's matrix $A$, whose rate is at least $9/2$ by his fractional bound.
- All statements are about binary rank (exact partitions). Nothing is claimed about Boolean rank (covers) or about other matrices.

## 5. What is formalized in Lean

The directory `lean/` proves Theorem 1 for every graph and every family, Lemmas 2 and 3, Corollary 5 for $k=33$ (`watson_conjecture_fails`), and the lower bound $4^k\le\mathrm{br}(M^{\otimes k})$ for every $k$ (`four_pow_le_binRank`). The extension to all $k\ge 33$, the crude bound on $t(k)$, and Corollaries 6 and 7 are proved here on paper only.
