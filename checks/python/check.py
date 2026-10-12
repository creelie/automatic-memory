#!/usr/bin/env python3
"""Independent check of the theorem in exact rational arithmetic.

(1) For every chord diagram with at most 5 chords, and for random diagrams with 6 chords,
    the sl(2) weight system w_D(c) is interpolated from the traces of the Casimir word in the
    irreducible representations of dimension d = 1, ..., n+1, and w_D(-3/32) is compared with
    xi of the intersection graph.
(2) The four-term relation of xi (and of every T_k) is checked on all labelled graphs with at
    most 4 vertices, for all ordered pairs of distinct vertices, and on random graphs with 5
    and 6 vertices.
(3) T_k is computed both by direct enumeration (graphs with at most 3 vertices) and by the
    generating function T_k = [prod x_v^2] f^k with f = sum_{S nonempty} (-1)^{e(S)} x^S.
"""
import itertools
import random
import sys
from fractions import Fraction
from math import comb

# ---------------------------------------------------------------- chord diagrams


def chord_diagrams(n):
    """All fixed-point-free involutions of {0, ..., 2n-1}."""
    def rec(free):
        if not free:
            yield {}
            return
        a = free[0]
        for j in range(1, len(free)):
            b = free[j]
            rest = free[1:j] + free[j + 1:]
            for m in rec(rest):
                m2 = dict(m)
                m2[a] = b
                m2[b] = a
                yield m2
    for m in rec(list(range(2 * n))):
        yield [m[i] for i in range(2 * n)]


def random_diagram(n, rng):
    pts = list(range(2 * n))
    rng.shuffle(pts)
    s = [0] * (2 * n)
    for i in range(n):
        a, b = pts[2 * i], pts[2 * i + 1]
        s[a], s[b] = b, a
    return s


def intersection_graph(s):
    n = len(s) // 2
    firsts = [i for i in range(2 * n) if i < s[i]]
    edges = set()
    for u in range(n):
        for v in range(u + 1, n):
            a, b = firsts[u], firsts[v]
            if (a < b < s[a] < s[b]) or (b < a < s[b] < s[a]):
                edges.add((u, v))
    return n, edges

# ---------------------------------------------------------------- weight system


# Letters 0 = E, 1 = F, 2 = H.  The Casimir tensor t = 1/4 E(x)F + 1/4 F(x)E + 1/8 H(x)H.
TENSOR = [(0, 1, Fraction(1, 4)), (1, 0, Fraction(1, 4)), (2, 2, Fraction(1, 8))]


def act(letter, d, s):
    """The letter applied to the basis vector e_s of the d-dimensional representation:
    E e_s = s(d-s) e_{s-1}, F e_s = e_{s+1}, H e_s = (d-1-2s) e_s.
    Returns (target index, coefficient) or None."""
    if letter == 0:
        return (s - 1, s * (d - s)) if s >= 1 else None
    if letter == 1:
        return (s + 1, 1) if s + 1 < d else None
    return (s, d - 1 - 2 * s)


def word_trace(word, d):
    """Trace of rho(w_0) rho(w_1) ... rho(w_{m-1}) in the d-dimensional representation."""
    tot = 0
    for s0 in range(d):
        s, c = s0, 1
        for letter in reversed(word):
            r = act(letter, d, s)
            if r is None:
                c = 0
                break
            s, c = r[0], c * r[1]
        if c and s == s0:
            tot += c
    return tot


def W(s, d):
    """Trace of the Casimir word in dimension d, divided by d."""
    n = len(s) // 2
    firsts = [i for i in range(2 * n) if i < s[i]]
    tot = Fraction(0)
    for choice in itertools.product(TENSOR, repeat=n):
        word = [None] * (2 * n)
        wt = Fraction(1)
        for (a, b, c), i in zip(choice, firsts):
            word[i], word[s[i]] = a, b
            wt *= c
        tot += wt * word_trace(word, d)
    return tot / d


def interpolate_at(xs, ys, x):
    tot = Fraction(0)
    for i, (xi, yi) in enumerate(zip(xs, ys)):
        term = Fraction(yi)
        for j, xj in enumerate(xs):
            if j != i:
                term *= Fraction(x - xj, xi - xj)
        tot += term
    return tot


def w_at(s, c):
    n = len(s) // 2
    ds = list(range(1, n + 2))
    xs = [Fraction(d * d - 1, 8) for d in ds]
    ys = [W(s, d) for d in ds]
    return interpolate_at(xs, ys, c)

# ---------------------------------------------------------------- xi


def T_bruteforce(n, edges, k):
    pairs = list(itertools.combinations(range(k), 2))
    tot = 0
    for p in itertools.product(pairs, repeat=n):
        if set().union(*map(set, p)) != set(range(k)):
            continue
        e = sum(len(set(p[u]) & set(p[v])) for (u, v) in edges)
        tot += (-1) ** e
    return tot


def T_all(n, edges):
    """T_0, ..., T_{2n} by the generating function in Z[x_v]/(x_v^3)."""
    adj = [0] * n
    for (u, v) in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    terms = []
    for m in range(1, 1 << n):
        e = sum(bin(adj[u] & m).count("1") for u in range(n) if (m >> u) & 1) // 2
        terms.append((m, -1 if e % 2 else 1))
    P = {(0,) * n: 1}
    target = (2,) * n
    out = []
    for k in range(2 * n + 1):
        out.append(P.get(target, 0))
        Q = {}
        for mono, c in P.items():
            for m, sg in terms:
                new = list(mono)
                ok = True
                for v in range(n):
                    if (m >> v) & 1:
                        new[v] += 1
                        if new[v] > 2:
                            ok = False
                            break
                if ok:
                    t = tuple(new)
                    Q[t] = Q.get(t, 0) + sg * c
        P = Q
    return out


def xi(n, edges):
    T = T_all(n, edges)
    return Fraction(sum((-1) ** k * (k + 1) * T[k] for k in range(2 * n + 1)), (-32) ** n)

# ---------------------------------------------------------------- graph moves


def toggle(edges, a, b):
    e = (min(a, b), max(a, b))
    return set(edges) ^ {e}


def tilde(n, edges, a, b):
    nb = {y for y in range(n) if y not in (a, b) and (min(b, y), max(b, y)) in edges}
    return set(edges) ^ {(min(a, y), max(a, y)) for y in nb}


def four_term_ok(n, edges, a, b, f):
    G1 = toggle(edges, a, b)
    G2 = tilde(n, edges, a, b)
    G3 = toggle(G2, a, b)
    return f(n, edges) - f(n, G1) == f(n, G2) - f(n, G3)

# ---------------------------------------------------------------- main


def main():
    rng = random.Random(20261012)
    c0 = Fraction(-3, 32)
    count = 0
    # (1) the extension property
    for n in range(0, 6):
        for s in chord_diagrams(n):
            m, E = intersection_graph(s)
            assert w_at(s, c0) == xi(m, E), (s,)
            count += 1
    for _ in range(25):
        s = random_diagram(6, rng)
        m, E = intersection_graph(s)
        assert w_at(s, c0) == xi(m, E), (s,)
        count += 1
    print(f"extension: w_D(-3/32) = xi(Gamma(D)) for {count} chord diagrams")
    # one chord: w = c; two crossing chords: w = c^2 - c/2
    assert w_at([1, 0], Fraction(5)) == 5
    assert w_at([2, 3, 0, 1], Fraction(5)) == Fraction(45, 2)
    # (3) T_k by enumeration agrees with the generating function
    for n in range(0, 4):
        allpairs = list(itertools.combinations(range(n), 2))
        for r in range(len(allpairs) + 1):
            for E in itertools.combinations(allpairs, r):
                T = T_all(n, set(E))
                for k in range(2 * n + 1):
                    assert T[k] == T_bruteforce(n, set(E), k)
    print("T_k: enumeration agrees with the generating function on all graphs with <= 3 vertices")
    # (2) four-term relation
    def Tk(k):
        return lambda n, E: T_all(n, E)[k]
    checked = 0
    for n in range(2, 5):
        allpairs = list(itertools.combinations(range(n), 2))
        for r in range(len(allpairs) + 1):
            for E in itertools.combinations(allpairs, r):
                E = set(E)
                for a in range(n):
                    for b in range(n):
                        if a != b:
                            assert four_term_ok(n, E, a, b, xi)
                            for k in range(2 * n + 1):
                                assert four_term_ok(n, E, a, b, Tk(k))
                            checked += 1
    for n in (5, 6):
        allpairs = list(itertools.combinations(range(n), 2))
        for _ in range(40):
            E = {e for e in allpairs if rng.random() < 0.5}
            a, b = rng.sample(range(n), 2)
            assert four_term_ok(n, E, a, b, xi)
            checked += 1
    print(f"four-term relation: {checked} instances (graph, ordered pair a != b)")
    # isomorphism invariance on random relabellings
    for _ in range(30):
        n = 5
        allpairs = list(itertools.combinations(range(n), 2))
        E = {e for e in allpairs if rng.random() < 0.5}
        perm = list(range(n))
        rng.shuffle(perm)
        E2 = {(min(perm[u], perm[v]), max(perm[u], perm[v])) for (u, v) in E}
        assert xi(n, E) == xi(n, E2)
    print("isomorphism invariance: 30 random relabellings")
    print("PYTHON: all checks passed")


if __name__ == "__main__":
    sys.exit(main())
