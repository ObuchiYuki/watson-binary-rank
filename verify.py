#!/usr/bin/env python3
"""Standalone verifier for "Watson's binary-rank conjecture fails".

Uses only the Python standard library (Python 3.10+).

  python3 verify.py          # about one second
  python3 verify.py --deep   # also builds the k = 4 partition (a few seconds)

Checks:
  1. Watson's matrix M: its transpose is T_{K4} (the incidence matrix of K4 with an
     extra all-ones column), rank 4 over Q, and a fooling set of size 4.
  2. Shitov's matrix B is M with one column deleted (up to permutations), rank 4.
  3. Theorem 1 (code rule): for k = 1, 2, 3 (and 4 with --deep) the construction,
     run with random parity-check families, is an exact partition of the ones of
     T_{K4}^{(x)k} into at most 4^k * t rectangles; every family has the face property.
  4. Lemma 3 / Corollary 4: the table N_z for k = 33 satisfies
     C(33, z) * bad(z)^N_z < 2^(33 z N_z) exactly, sums to 1431, and
     4^33 * 1431 < 5^33.
  5. The crude bound: prod_{i<=z} (1 - 2^-i) >= 1/4 + 2^-(z+1) for z <= 300, and
     4^k (k+1)(floor(2.41 k)+1) < 5^k first holds at k = 37.
"""
import itertools
import math
import random
import sys
from fractions import Fraction

# ---------------------------------------------------------------- matrices

# Watson (2016), proof of Theorem 2(2)
M = [[1, 1, 1, 0, 0, 0],
     [1, 0, 0, 1, 1, 0],
     [0, 1, 0, 1, 0, 1],
     [0, 0, 1, 0, 1, 1],
     [1, 1, 1, 1, 1, 1]]

# Shitov (2026), Section 3
B_SHITOV = [[1, 1, 0, 0, 1],
            [0, 1, 1, 0, 0],
            [0, 0, 1, 1, 1],
            [1, 0, 0, 1, 0],
            [1, 1, 1, 1, 1]]

V4 = [1, 2, 3, 4]
E4 = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]


def t_graph(V, E):
    """rows = edges, columns = [0] + vertices; 1 iff column is 0 or an endpoint"""
    return [[1] + [1 if v in e else 0 for v in V] for e in E]


TK4 = t_graph(V4, E4)


def transpose(A):
    return [list(r) for r in zip(*A)]


def rank_q(A):
    A = [[Fraction(x) for x in row] for row in A]
    r = 0
    for c in range(len(A[0])):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r


def equal_up_to_perm(A, Bm):
    if len(A) != len(Bm) or len(A[0]) != len(Bm[0]):
        return False
    for pr in itertools.permutations(range(len(A))):
        for pc in itertools.permutations(range(len(A[0]))):
            if all(A[pr[i]][pc[j]] == Bm[i][j]
                   for i in range(len(A)) for j in range(len(A[0]))):
                return True
    return False


def is_fooling(T, pairs):
    if any(T[r][c] != 1 for r, c in pairs):
        return False
    return all(T[a][d] == 0 or T[b][c] == 0
               for (a, c), (b, d) in itertools.combinations(pairs, 2))


# ---------------------------------------------------------------- Theorem 1

def gf2_rank(rows):
    rows = list(rows)
    rank = 0
    width = max((r.bit_length() for r in rows), default=0)
    for b in range(width):
        piv = next((i for i in range(rank, len(rows)) if rows[i] >> b & 1), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] >> b & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def kernel(H, k):
    return frozenset(y for y in range(1 << k)
                     if all(bin(h & y).count("1") % 2 == 0 for h in H))


def face_property(C, Z, k):
    out = [i for i in range(k) if i not in Z]
    seen = {}
    for y in C:
        key = tuple((y >> i) & 1 for i in out)
        seen[key] = seen.get(key, 0) + 1
    return len(seen) == 2 ** len(out) and all(v == 1 for v in seen.values())


def random_family(k, rng):
    """For every Z, the kernel of a random |Z| x k matrix invertible on the columns Z."""
    fam = {}
    for z in range(k + 1):
        todo = [frozenset(Z) for Z in itertools.combinations(range(k), z)]
        while todo:
            H = [rng.getrandbits(k) for _ in range(z)]
            C = None
            rest = []
            for Z in todo:
                sub = [sum(((h >> i) & 1) << j for j, i in enumerate(sorted(Z))) for h in H]
                if gf2_rank(sub) == z:
                    C = C or kernel(H, k)
                    fam[Z] = C
                else:
                    rest.append(Z)
            todo = rest
    return fam


def code_rule(V, E, k, fam):
    """The partition of Theorem 1. Returns the number of nonempty rectangles after
    checking that they are all-ones and cover every one exactly once."""
    T = t_graph(V, E)
    cols0 = [0] + V
    label = {}
    for e in E:
        label[(e, e[0])] = 0
        label[(e, e[1])] = 1
    rows = list(itertools.product(range(len(E)), repeat=k))
    cols = list(itertools.product(cols0, repeat=k))

    def entry(e, x):
        return all(T[e[i]][cols0.index(x[i])] for i in range(k))

    cover = {}
    count = 0
    for v in itertools.product(V, repeat=k):
        R = [e for e in rows if all(v[i] in E[e[i]] for i in range(k))]
        groups = {}
        for x in itertools.product(*[(0, v[i]) for i in range(k)]):
            Z = frozenset(i for i in range(k) if x[i] == 0)
            groups.setdefault(fam[Z], []).append(x)
        for C, xs in groups.items():
            rs = [e for e in R
                  if sum(label[(E[e[i]], v[i])] << i for i in range(k)) in C]
            if not rs:
                continue
            count += 1
            for e in rs:
                for x in xs:
                    assert entry(e, x), "a rectangle contains a zero"
                    cover[(e, x)] = cover.get((e, x), 0) + 1
    for e in rows:
        for x in cols:
            assert cover.get((e, x), 0) == (1 if entry(e, x) else 0), "not an exact partition"
    return count


# ---------------------------------------------------------------- Lemma 3

def gl(z):
    p = 1
    for i in range(z):
        p *= 2 ** z - 2 ** i
    return p


def bad(z, k):
    return 2 ** (z * (k - z)) * (2 ** (z * z) - gl(z))


N33 = [1, 6, 14, 22, 29, 35, 41, 45, 49, 52, 54, 56, 58, 60, 61, 61, 62, 62, 61, 61, 60,
       58, 56, 54, 52, 49, 45, 41, 37, 32, 26, 19, 11, 1]


# ---------------------------------------------------------------- main

def main():
    deep = "--deep" in sys.argv
    ok = True

    def check(name, cond):
        nonlocal ok
        print(("PASS " if cond else "FAIL ") + name)
        ok = ok and cond

    # 1. Watson's matrix
    check("M^T equals T_{K4} (rows of M = columns 1,2,3,4,0 of T_{K4}; columns of M = edges)",
          all(M[r][c] == TK4[c][[1, 2, 3, 4, 0][r]] for r in range(5) for c in range(6)))
    check("rank_Q(M) = 4", rank_q(M) == 4)
    check("{(1,1),(2,4),(3,2),(4,3)} is a fooling set of M",
          is_fooling(M, [(0, 0), (1, 3), (2, 1), (3, 2)]))

    # 2. Shitov's matrix
    check("Shitov's B equals M with one column deleted, up to permutations",
          any(equal_up_to_perm([row[:j] + row[j + 1:] for row in M], B_SHITOV)
              for j in range(6)))
    check("rank_Q(B) = 4", rank_q(B_SHITOV) == 4)

    # 3. Theorem 1
    rng = random.Random(2026)
    for k in range(1, (4 if deep else 3) + 1):
        fam = random_family(k, rng)
        faces = all(face_property(C, Z, k) for Z, C in fam.items())
        t = len(set(fam.values()))
        n = code_rule(V4, E4, k, fam)
        check(f"k={k}: family has the face property; exact partition of T_K4^(x{k}) "
              f"into {n} <= 4^k*t = {4 ** k * t} rectangles", faces and n <= 4 ** k * t)

    # 4. k = 33
    check("N_z table: C(33,z) * bad(z)^N_z < 2^(33 z N_z) for z = 0..33",
          all(math.comb(33, z) * bad(z, 33) ** N33[z] < 2 ** (33 * z * N33[z])
              for z in range(34)))
    check("sum N_z = 1431", sum(N33) == 1431)
    check("4^33 * 1431 < 5^33  (Watson's Conjecture 1 fails at k = 33)",
          4 ** 33 * 1431 < 5 ** 33)

    # 5. crude bound
    check("prod_{i=1..z} (1 - 2^-i) >= 1/4 + 2^-(z+1) for z = 1..300",
          all(Fraction(gl(z), 2 ** (z * z)) >= Fraction(1, 4) + Fraction(1, 2 ** (z + 1))
              for z in range(1, 301)))
    first = next(k for k in range(1, 200)
                 if 4 ** k * (k + 1) * (math.floor(2.41 * k) + 1) < 5 ** k)
    check(f"crude bound 4^k (k+1)(floor(2.41k)+1) < 5^k first holds at k = {first}", first == 37)

    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
