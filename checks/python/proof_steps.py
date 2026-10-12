#!/usr/bin/env python3
"""Exact checks of the intermediate identities in the proof of the paper.

(a) The oscillator map phi : E -> -d^2/4, F -> z^2, H -> -(z d + d z)/2 respects the sl(2)
    relations, and phi(C_D) is the scalar w_D(-3/32) in the Weyl algebra (Proposition 3.2).
(b) (phi (x) phi)(t) = -1/32 (pi_13 pi_24 + pi_14 pi_23)  (Lemma 4.3).
(c) The supertrace tau(z^i d^j) = delta_ij (-1)^j j!/2^j is twisted cyclic, and the Wick
    formula holds on random words (Lemma 3.3).
(d) The sign lemma cr(P) + cr(M) + cyc(P, M) + des(P, M) = 0 mod 2 for all pairs of perfect
    matchings on at most 8 points and for random pairs on 10 and 12 points (Lemma 4.1).
(e) tau(X_P) = 4^{-m} (-1)^{cr P} L_P(-2) for all matchings P on 4m points, m <= 2, and for
    the matchings P_beta of all diagrams with 3 chords (Proposition 4.2).
(f) sum_beta (-1)^{cr P_beta} L_{P_beta}(N) = 4^n S_Gamma(N) for N = 0..6 and every diagram
    with at most 3 chords (Proposition 5.3).
"""
import itertools
import random
from fractions import Fraction
from math import comb, factorial

# ------------------------------------------------------------------ Weyl algebra
# An element is a dict {(i, j): coefficient} for the normally ordered monomials z^i d^j,
# with d z - z d = 1.


def wmul(a, b):
    out = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            # d^j z^k = sum_r C(j, r) k!/(k-r)! z^(k-r) d^(j-r)
            for r in range(min(j, k) + 1):
                c = x * y * comb(j, r) * (factorial(k) // factorial(k - r))
                key = (i + k - r, j + l - r)
                out[key] = out.get(key, 0) + c
    return {k: v for k, v in out.items() if v != 0}


def wadd(a, b, s=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v != 0}


def wscale(a, s):
    return {k: s * v for k, v in a.items() if s * v != 0}


Z = {(1, 0): Fraction(1)}
D = {(0, 1): Fraction(1)}
ONE = {(0, 0): Fraction(1)}
PHI = {
    0: {(0, 2): Fraction(-1, 4)},                      # E
    1: {(2, 0): Fraction(1)},                          # F
    2: wscale(wadd(wmul(Z, D), wmul(D, Z)), Fraction(-1, 2)),  # H
}


def tau(a):
    return sum((v * Fraction((-1) ** i * factorial(i), 2 ** i) for (i, j), v in a.items() if i == j),
               Fraction(0))


def word(letters):
    """Product of letters 'z', 'd' in the Weyl algebra."""
    out = ONE
    for x in letters:
        out = wmul(out, Z if x == 'z' else D)
    return out


def bracket(x, y):
    """[x, y] for letters: [z, d] = -1, [d, z] = 1."""
    if x == y:
        return 0
    return -1 if x == 'z' else 1


def wick(letters):
    if not letters:
        return Fraction(1)
    if len(letters) % 2:
        return Fraction(0)
    x, rest = letters[0], letters[1:]
    return sum((Fraction(bracket(x, y), 2) * wick(rest[:s] + rest[s + 1:])
                for s, y in enumerate(rest) if y != x), Fraction(0))

# ------------------------------------------------------------------ matchings


def matchings(points):
    if not points:
        yield []
        return
    a = points[0]
    for j in range(1, len(points)):
        rest = points[1:j] + points[j + 1:]
        for m in matchings(rest):
            yield [(a, points[j])] + m


def crossings(m):
    c = 0
    for (a, b), (x, y) in itertools.combinations(m, 2):
        a, b = min(a, b), max(a, b)
        x, y = min(x, y), max(x, y)
        if a < x < b < y or x < a < y < b:
            c += 1
    return c


def cycles(P, M, npts):
    """Cycles of P u M, each as the cyclic sequence of points visited, alternating P, M."""
    pp, mm = {}, {}
    for a, b in P:
        pp[a], pp[b] = b, a
    for a, b in M:
        mm[a], mm[b] = b, a
    seen, out = set(), []
    for s in range(npts):
        if s in seen:
            continue
        cyc, x = [], s
        while True:
            cyc.append(x)
            seen.add(x)
            y = pp[x]
            cyc.append(y)
            seen.add(y)
            x = mm[y]
            if x == s:
                break
        out.append(cyc)
    return out


def descents(cyc):
    return sum(1 for k in range(len(cyc)) if cyc[k] > cyc[(k + 1) % len(cyc)])


_MATCHINGS = {}
_LPOLY = {}


def L(P, npts, N):
    """L_P(N) = sum_M (-1)^{cr M} N^{cyc(P, M)}, stored as its coefficient list."""
    if npts not in _MATCHINGS:
        _MATCHINGS[npts] = [(M, (-1) ** crossings(M)) for M in matchings(list(range(npts)))]
    key = (npts, tuple(sorted(P)))
    if key not in _LPOLY:
        coef = [0] * (npts // 2 + 1)
        for M, sg in _MATCHINGS[npts]:
            coef[len(cycles(P, M, npts))] += sg
        _LPOLY[key] = coef
    return sum(c * N ** e for e, c in enumerate(_LPOLY[key]))


def X(P, npts):
    """X_P = sum over the orientations of the edges of P: z at the tail, d at the head, sign
    +1 when the edge goes up and -1 when it goes down."""
    out = {}
    for orient in itertools.product((0, 1), repeat=len(P)):
        letters = [None] * npts
        sign = 1
        for (a, b), o in zip(P, orient):
            t, h = (a, b) if o == 0 else (b, a)
            letters[t], letters[h] = 'z', 'd'
            if t > h:
                sign = -sign
        out = wadd(out, word(letters), sign)
    return out

# ------------------------------------------------------------------ chord diagrams


def chord_diagrams(n):
    for m in matchings(list(range(2 * n))):
        s = [0] * (2 * n)
        for a, b in m:
            s[a], s[b] = b, a
        yield s


def chords(s):
    return [(i, s[i]) for i in range(len(s)) if i < s[i]]


def P_beta(s, beta):
    """Point i carries the legs 2i < 2i+1.  A chord (p, q) with beta = 0 pairs (p1, q1),
    (p2, q2); with beta = 1 it pairs (p1, q2), (p2, q1)."""
    out = []
    for (p, q), b in zip(chords(s), beta):
        if b == 0:
            out += [(2 * p, 2 * q), (2 * p + 1, 2 * q + 1)]
        else:
            out += [(2 * p, 2 * q + 1), (2 * p + 1, 2 * q)]
    return out


def S_graph(s, N):
    """S_Gamma(N): sum over p : chords -> 2-subsets of [N] of the edge signs."""
    ch = chords(s)
    n = len(ch)
    edges = [(u, v) for u in range(n) for v in range(u + 1, n)
             if ch[u][0] < ch[v][0] < ch[u][1] < ch[v][1] or ch[v][0] < ch[u][0] < ch[v][1] < ch[u][1]]
    pairs = list(itertools.combinations(range(N), 2))
    tot = 0
    for p in itertools.product(pairs, repeat=n):
        e = sum(len(set(p[u]) & set(p[v])) for u, v in edges)
        tot += (-1) ** e
    return tot, n, edges


def casimir_phi(s):
    """phi(C_D) in the Weyl algebra."""
    tens = [(0, 1, Fraction(1, 4)), (1, 0, Fraction(1, 4)), (2, 2, Fraction(1, 8))]
    ch = chords(s)
    out = {}
    for choice in itertools.product(tens, repeat=len(ch)):
        lett = [None] * len(s)
        w = Fraction(1)
        for (p, q), (a, b, c) in zip(ch, choice):
            lett[p], lett[q] = a, b
            w *= c
        prod = ONE
        for l in lett:
            prod = wmul(prod, PHI[l])
        out = wadd(out, prod, w)
    return out


def main():
    rng = random.Random(20261012)
    # (a) sl(2) relations and phi(C_D) scalar
    E, F, H = PHI[0], PHI[1], PHI[2]
    assert wadd(wmul(H, E), wmul(E, H), -1) == wscale(E, 2)
    assert wadd(wmul(H, F), wmul(F, H), -1) == wscale(F, -2)
    assert wadd(wmul(E, F), wmul(F, E), -1) == H
    import importlib.util
    import os
    spec = importlib.util.spec_from_file_location("chk", os.path.join(os.path.dirname(__file__), "check.py"))
    chk = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(chk)
    cnt = 0
    for n in range(0, 4):
        for s in chord_diagrams(n):
            val = casimir_phi(s)
            w = chk.w_at(s, Fraction(-3, 32))
            assert val == (wscale(ONE, w) if w else {}), (s, val, w)
            cnt += 1
    print(f"(a) phi(C_D) = w_D(-3/32) in the Weyl algebra for {cnt} diagrams")
    # (b) the image of the Casimir tensor on four legs, as an element of A_1 (x) A_1,
    # represented by the products u1 u2 (x) u3 u4 of letters
    lhs = {}
    for a, b, c in [(0, 1, Fraction(1, 4)), (1, 0, Fraction(1, 4)), (2, 2, Fraction(1, 8))]:
        for k1, v1 in PHI[a].items():
            for k2, v2 in PHI[b].items():
                lhs[(k1, k2)] = lhs.get((k1, k2), 0) + c * v1 * v2
    rhs = {}
    pi = [('z', 'd', 1), ('d', 'z', -1)]
    for (x1, y1, e1), (x2, y2, e2) in itertools.product(pi, repeat=2):
        for left, right in (((x1, x2), (y1, y2)), ((x1, x2), (y2, y1))):
            l, r = word(left), word(right)
            for k1, v1 in l.items():
                for k2, v2 in r.items():
                    rhs[(k1, k2)] = rhs.get((k1, k2), 0) + Fraction(-1, 32) * e1 * e2 * v1 * v2
    lhs = {k: v for k, v in lhs.items() if v}
    rhs = {k: v for k, v in rhs.items() if v}
    assert lhs == rhs
    print("(b) (phi x phi)(t) = -1/32 (pi_13 pi_24 + pi_14 pi_23)")
    # (c) twisted cyclicity and the Wick formula
    for i in range(6):
        for j in range(6):
            a = {(i, j): Fraction(1)}
            assert tau(wmul(Z, a)) == -tau(wmul(a, Z))
            assert tau(wmul(D, a)) == -tau(wmul(a, D))
    for _ in range(300):
        m = rng.randrange(0, 11)
        letters = [rng.choice('zd') for _ in range(m)]
        assert tau(word(letters)) == wick(letters)
    print("(c) tau is twisted cyclic; Wick formula on 300 random words")
    # (d) the sign lemma
    tot = 0
    for npts in (2, 4, 6, 8):
        ms = list(matchings(list(range(npts))))
        for P in ms:
            for M in ms:
                cy = cycles(P, M, npts)
                q = crossings(P) + crossings(M) + len(cy) + sum(descents(c) for c in cy)
                assert q % 2 == 0
                tot += 1
    for npts in (10, 12):
        for _ in range(3000):
            pts = list(range(npts))
            rng.shuffle(pts)
            P = [(pts[2 * i], pts[2 * i + 1]) for i in range(npts // 2)]
            rng.shuffle(pts)
            M = [(pts[2 * i], pts[2 * i + 1]) for i in range(npts // 2)]
            cy = cycles(P, M, npts)
            assert (crossings(P) + crossings(M) + len(cy) + sum(descents(c) for c in cy)) % 2 == 0
            tot += 1
    print(f"(d) sign lemma on {tot} pairs of matchings")
    # (e) tau(X_P)
    tot = 0
    for m in (1, 2):
        npts = 4 * m
        for P in matchings(list(range(npts))):
            assert tau(X(P, npts)) == Fraction((-1) ** crossings(P) * L(P, npts, -2), 4 ** m)
            tot += 1
    for s in chord_diagrams(3):
        for beta in itertools.product((0, 1), repeat=3):
            P = P_beta(s, beta)
            assert tau(X(P, 12)) == Fraction((-1) ** crossings(P) * L(P, 12, -2), 4 ** 3)
            tot += 1
    print(f"(e) tau(X_P) = 4^-m (-1)^cr(P) L_P(-2) for {tot} matchings")
    # (f) the Clifford identity, and the assembled formula at N = -2
    tot = 0
    for n in range(0, 4):
        for s in chord_diagrams(n):
            for N in range(0, 7):
                lhs = sum((-1) ** crossings(P_beta(s, b)) * L(P_beta(s, b), 4 * n, N)
                          for b in itertools.product((0, 1), repeat=n))
                assert lhs == 4 ** n * S_graph(s, N)[0]
                tot += 1
            lhs = sum((-1) ** crossings(P_beta(s, b)) * L(P_beta(s, b), 4 * n, -2)
                      for b in itertools.product((0, 1), repeat=n))
            assert Fraction(lhs, (-128) ** n) == chk.w_at(s, Fraction(-3, 32))
    print(f"(f) Clifford identity on {tot} pairs (diagram, N)")
    print("PROOF STEPS: all checks passed")


if __name__ == "__main__":
    main()
