# Watson's Binary-Rank Conjecture Is False

**Kronecker powers of a rank-five 0/1 matrix need only $4^{k+o(k)}$ rectangles.**

[![verify](https://github.com/ObuchiYuki/watson-binary-rank/actions/workflows/verify.yml/badge.svg)](https://github.com/ObuchiYuki/watson-binary-rank/actions/workflows/verify.yml)
[![lean](https://github.com/ObuchiYuki/watson-binary-rank/actions/workflows/lean.yml/badge.svg)](https://github.com/ObuchiYuki/watson-binary-rank/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24586599.svg)](https://doi.org/10.5281/zenodo.24586599)

**Author:** Yuki Obuchi  
**First published:** 2026-11-27  
**DOI:** [10.5281/zenodo.24586599](https://doi.org/10.5281/zenodo.24586599) (all versions; per-version DOIs are listed on Zenodo)  
**Status:** research note (not peer-reviewed). The disproof at $k=33$ and the lower bound $4^k$ are machine-checked in Lean 4 with Mathlib ([lean/](lean/)).

The **binary rank** $\mathrm{br}(T)$ of a 0/1 matrix is the least number of all-ones rectangles that partition its ones. Watson (2016) gave a $5\times6$ matrix $M$ with $\mathrm{br}(M)=5$ and nonnegative rank $4$, and conjectured:

> **Conjecture 1 (Watson 2016).** For all $k$, $\mathrm{br}(M^{\otimes k})=5^k$.

This note shows that the conjecture is false and determines the growth rate.

$$
\boxed{\ 4^k\ \le\ \mathrm{br}\big(M^{\otimes k}\big)\ \le\ 4^k\,(k+1)\big(\lfloor 2.41k\rfloor+1\big)\quad\text{for every }k\ }
$$

In particular $\mathrm{br}(M^{\otimes 33})\le 4^{33}\cdot 1431<5^{33}$, and $\mathrm{br}(M^{\otimes k})<5^k$ for every $k\ge 33$. The asymptotic rate $\lim_k\mathrm{br}(M^{\otimes k})^{1/k}$ equals $4$, the nonnegative rank of $M$.

```
M = 1 1 1 0 0 0
    1 0 0 1 1 0
    0 1 0 1 0 1
    0 0 1 0 1 1
    1 1 1 1 1 1
```

## The idea

The transpose of $M$ is the incidence matrix of the complete graph $K_4$ with an extra all-ones column: the six columns of $M$ are the edges, the top four rows are the vertices, and the bottom row is the extra column.

In the $k$-th power, a row is a $k$-tuple of edges $e$ and a column is a $k$-tuple $x$ whose entries are vertices or the extra column "0". The entry is $1$ when every $x_i$ is $0$ or an endpoint of $e_i$.

- **Boxes.** For each $v\in V^k$, the ones with $x_i\in\{0,v_i\}$ and $v_i\in e_i$ form an all-ones box. There are $4^k$ boxes. They cover all ones, but they overlap: a coordinate with $x_i=0$ could use either endpoint of $e_i$.
- **Breaking ties with a code.** Label the two endpoints of each edge $0$ and $1$. Where $x_i=0$, the endpoint is chosen by a codeword: for each set $Z$ of zero coordinates we fix a set $C_Z\subseteq\mathbb F_2^k$ that meets every face "fixed outside $Z$" exactly once. Then each one lands in exactly one box, and each box splits into one rectangle per distinct set $C_Z$.
- **Few codes suffice.** Kernels of random parity-check matrices have this property, and a union bound shows that $O(k^2)$ kernels serve all $2^k$ sets $Z$. This gives $4^k\cdot O(k^2)$ rectangles.

The lower bound $4^k$ comes from a fooling set of size $4$ in $M$, which Watson already observed.

## Results

| Statement | Range | Type |
| :--- | :--- | :--- |
| $\mathrm{br}(T_G^{\otimes k})\le \lvert V\rvert^k\,t$ for any loopless multigraph $G$ and code family of size $t$ (Theorem 1) | all $k$ | constructive |
| $t(k)\le(k+1)(\lfloor2.41k\rfloor+1)$ | all $k$ | counting |
| $4^k\le\mathrm{br}(M^{\otimes k})\le 4^k(k+1)(\lfloor2.41k\rfloor+1)$, rate $=4$ | all $k$ | theorem |
| $\mathrm{br}(M^{\otimes 33})\le 4^{33}\cdot1431<5^{33}$, so Conjecture 1 fails | $k\ge33$ | existence |
| Shitov's $5\times5$ matrix $B$ (= $M$ minus a column) also has rate exactly $4$ | all $k$ | theorem |

## Proof and verification

- [PROOF.md](PROOF.md): the complete argument.
- [verify.py](verify.py): a standalone verifier that uses only the Python standard library (Python 3.10+).

Run:

```sh
python3 verify.py          # about one second
python3 verify.py --deep   # also builds the k = 4 partition
```

The verifier performs these checks:

- $M^{\mathsf T}$ is the $K_4$ incidence matrix with an all-ones column. $M$ has rank $4$ and a fooling set of size $4$.
- Shitov's matrix is $M$ with one column deleted.
- For $k\le3$ (and $k=4$ with `--deep`), the construction with random code families gives exact partitions of $M^{\otimes k}$, and every family has the required property.
- The 34 counting inequalities for $k=33$ hold as exact integer inequalities, their values sum to $1431$, and $4^{33}\cdot1431<5^{33}$.

## Lean formalization

The directory [lean/](lean/) proves the following in Lean 4 with Mathlib. There is no `sorry`, and every theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The CI checks this on every push.

| Lean theorem | Statement |
| :--- | :--- |
| `code_rule` | Theorem 1 for every loopless multigraph, every $k$ and every code family |
| `faceProp_kerSet` | the kernel of a parity-check matrix that is invertible on $Z$ meets every face once |
| `exists_good` | the union bound (uses Mathlib's count of $\mathrm{GL}_m(\mathbb F_2)$) |
| `watson_conjecture_fails` | `binRank (kronPow watsonM 33) < 5 ^ 33` |
| `four_pow_le_binRank` | `4 ^ k ≤ binRank (kronPow watsonM k)` for every `k` |

All statements are phrased with the definitions in [lean/WatsonBinaryRank/Defs.lean](lean/WatsonBinaryRank/Defs.lean): 0/1 matrices as `Bool`-valued functions, exact partitions into all-ones rectangles, binary rank as the least size of such a partition, and Kronecker powers indexed by `Fin k`. `watsonM` is entered literally from Watson's paper. A reader who wants to trust the formal result should check that these definitions match the intended notions.

The extension from $k=33$ to all $k\ge33$, the polynomial bound on $t(k)$, and the corollaries on Shitov's matrix and on general graphs are proved in PROOF.md only.

Build (Lean toolchain from `lean-toolchain`, Mathlib pinned in `lakefile.toml`):

```sh
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Scope

- The disproof at $k=33$ is an existence argument: the parity-check matrices are chosen by counting. No explicit partition is given; it would have about $10^{23}$ rectangles.
- The conjecture holds for $k=1$. For $k=2$, an unpublished SAT computation of ours (without a DRAT certificate) gives $\mathrm{br}(M\otimes M)=25$. The least $k$ at which the conjecture fails is at most $33$ and is not known.
- Watson's motivation was that the conjecture would give a $\log_4 5$ factor separation between unambiguous nondeterministic communication and the corresponding sampling problem. For the family $M^{\otimes k}$ there is no such asymptotic separation: $\log_2\mathrm{br}(M^{\otimes k})=2k+O(\log k)$.

## Related work

Watson asked whether binary rank can drop under Kronecker powers. Shitov (2026) answered this with a $5\times5$ matrix $B$ with $\mathrm{br}(B)=5$ and $\mathrm{br}(B\otimes B)\le24$, and Poindexter (2026) independently gave a different $5\times5$ matrix with an exact square of $24$. Both concern squares. Shitov's $B$ is $M$ with one column removed, so a bound for $B$ does not bound $M$, and Conjecture 1 about $M$ itself was still open in their papers. Poindexter asks whether higher powers can improve the rate $\sqrt{24}$. For Shitov's $B$ this note shows that the rate is exactly $4$.

To the best of our knowledge, the failure of Conjecture 1 and the exact rate are new. Our search (web search, arXiv, OpenAlex, citations of Watson 2016, Shitov 2026 and Poindexter 2026, as of 2026-11-27) found no earlier result on the rate of these powers. This is a research note, not a peer-reviewed publication.

## References

1. Thomas Watson. [Nonnegative rank vs. binary rank](https://doi.org/10.4086/cjtcs.2016.002). *Chicago Journal of Theoretical Computer Science* 2016:2. [doi:10.4086/cjtcs.2016.002](https://doi.org/10.4086/cjtcs.2016.002); [arXiv:1603.07779](https://arxiv.org/abs/1603.07779). See Theorem 2(2) and Conjecture 1.
2. Yaroslav Shitov. Factoring Kronecker squares of nonnegative matrices with GPT-5.6 Sol. Preprint, 2026. [doi:10.13140/RG.2.2.26449.90723](https://doi.org/10.13140/RG.2.2.26449.90723).
3. Donald D. Poindexter, Jr. Exact nonmultiplicativity of binary rank under Kronecker products. Preprint, 2026. [doi:10.5281/zenodo.21669565](https://doi.org/10.5281/zenodo.21669565).
4. Angikar Ghosal and Andreas Karrenbauer. [Engineering insights into biclique partitions and fractional binary ranks of matrices](https://doi.org/10.4230/LIPIcs.SEA.2025.18). SEA 2025. [doi:10.4230/LIPIcs.SEA.2025.18](https://doi.org/10.4230/LIPIcs.SEA.2025.18); [arXiv:2502.06730](https://arxiv.org/abs/2502.06730).
5. Michal Parnas. Mathematical and computational perspectives on the Boolean and binary rank and their relation to the real rank. Survey, 2026. [arXiv:2601.13900](https://arxiv.org/abs/2601.13900).

## How to cite

Use GitHub's "Cite this repository" button, or see [CITATION.cff](CITATION.cff).

> Yuki Obuchi. *Watson's Binary-Rank Conjecture Is False: Kronecker Powers of a Rank-Five 0/1 Matrix Need Only 4^{k+o(k)} Rectangles.* Research note, 2026. Zenodo. https://doi.org/10.5281/zenodo.24586599

## Acknowledgments

The construction was found, and its proofs, verifier and Lean formalization were drafted and checked, with the help of AI assistants (Claude by Anthropic; Gemini by Google for an independent cross-check). The author reviewed the final statements.

## License

- Code ([verify.py](verify.py), [lean/](lean/) and the CI configuration): [MIT License](LICENSE).
- Text, proofs and the PDF note ([README.md](README.md), [PROOF.md](PROOF.md), `paper/`): [Creative Commons Attribution 4.0 International (CC BY 4.0)](LICENSE-docs).

**Keywords:** binary rank, biclique partition, Kronecker product, tensor power, nonnegative rank, unambiguous communication complexity, Watson's conjecture, Lean 4.
