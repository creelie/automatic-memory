/*
 * Independent check in C, in arithmetic modulo the prime p = 2^61 - 1.
 *
 * (1) For every chord diagram with at most 6 chords (10395 diagrams with 6 chords) the value
 *     w_D(-3/32) is obtained by Lagrange interpolation from tr(C_D)/d, d = 1, ..., n+1, and is
 *     compared with xi of the intersection graph.  All quantities are rationals whose
 *     denominators are products of powers of 2 and of small integers, hence invertible mod p.
 * (2) The four-term relation for xi on all labelled graphs with at most 5 vertices and all
 *     ordered pairs of distinct vertices, and on 3000 random graphs with 6 and 7 vertices.
 *
 * Build: cc -O2 -o check check.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;
static const u64 P = (((u64)1) << 61) - 1;

static u64 md(u128 x) {
    u64 lo = (u64)(x & P), hi = (u64)(x >> 61);
    u64 r = lo + hi;
    r = (r & P) + (r >> 61);
    return r >= P ? r - P : r;
}
static u64 mul(u64 a, u64 b) { return md((u128)a * b); }
static u64 add(u64 a, u64 b) { u64 r = a + b; return r >= P ? r - P : r; }
static u64 sub(u64 a, u64 b) { return a >= b ? a - b : a + P - b; }
static u64 fromll(long long x) { return x >= 0 ? (u64)x % P : sub(0, (u64)(-x) % P); }
static u64 pw(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = mul(r, a); a = mul(a, a); e >>= 1; } return r; }
static u64 inv(u64 a) { return pw(a, P - 2); }

#define MAXN 8
static int sigma[2 * MAXN];
static int nch;

/* --------------------------------------------------------------- weight system */

/* letter 0 = E, 1 = F, 2 = H acting on e_s in dimension d; returns 0 if the result is 0 */
static int act(int letter, int d, int s, int *t, long long *c) {
    if (letter == 0) { if (s < 1) return 0; *t = s - 1; *c = (long long)s * (d - s); return 1; }
    if (letter == 1) { if (s + 1 >= d) return 0; *t = s + 1; *c = 1; return 1; }
    *t = s; *c = d - 1 - 2 * s; return 1;
}

static u64 word_trace(const int *word, int len, int d) {
    u64 tot = 0;
    for (int s0 = 0; s0 < d; s0++) {
        int s = s0; u64 c = 1; int alive = 1;
        for (int i = len - 1; i >= 0; i--) {
            int t; long long cc;
            if (!act(word[i], d, s, &t, &cc)) { alive = 0; break; }
            s = t; c = mul(c, fromll(cc));
        }
        if (alive && s == s0) tot = add(tot, c);
    }
    return tot;
}

static u64 W(int d) {
    int n = nch, firsts[MAXN], k = 0;
    for (int i = 0; i < 2 * n; i++) if (i < sigma[i]) firsts[k++] = i;
    int la[3] = {0, 1, 2}, lb[3] = {1, 0, 2};
    u64 tw[3]; tw[0] = inv(4); tw[1] = inv(4); tw[2] = inv(8);
    int total = 1; for (int i = 0; i < n; i++) total *= 3;
    u64 tot = 0; int word[2 * MAXN];
    for (int code = 0; code < total; code++) {
        int x = code; u64 wt = 1;
        for (int j = 0; j < n; j++) {
            int ch = x % 3; x /= 3;
            word[firsts[j]] = la[ch]; word[sigma[firsts[j]]] = lb[ch];
            wt = mul(wt, tw[ch]);
        }
        tot = add(tot, mul(wt, word_trace(word, 2 * n, d)));
    }
    return mul(tot, inv((u64)d));
}

static u64 w_at(u64 c) {
    int n = nch, m = n + 1;
    u64 xs[MAXN + 2], ys[MAXN + 2];
    for (int i = 0; i < m; i++) { int d = i + 1; xs[i] = mul(fromll((long long)d * d - 1), inv(8)); ys[i] = W(d); }
    u64 tot = 0;
    for (int i = 0; i < m; i++) {
        u64 term = ys[i];
        for (int j = 0; j < m; j++) if (j != i) term = mul(term, mul(sub(c, xs[j]), inv(sub(xs[i], xs[j]))));
        tot = add(tot, term);
    }
    return tot;
}

/* --------------------------------------------------------------- xi */

static int pow3[16];

/* xi of the graph with adjacency bitmasks adj[0..n-1], modulo P */
static u64 xi(int n, const int *adj) {
    int N3 = pow3[n];
    static u64 A[6561], B[6561];
    static int sg[256];
    for (int m = 1; m < (1 << n); m++) {
        int e = 0;
        for (int u = 0; u < n; u++) if ((m >> u) & 1) e += __builtin_popcount(adj[u] & m);
        sg[m] = ((e / 2) % 2) ? -1 : 1;
    }
    memset(A, 0, sizeof(u64) * N3); A[0] = 1;
    int target = 0; for (int v = 0; v < n; v++) target += 2 * pow3[v];
    u64 num = 0;
    for (int k = 0; k <= 2 * n; k++) {
        u64 coef = fromll((k % 2 ? -1LL : 1LL) * (k + 1));
        num = add(num, mul(coef, A[target]));
        memset(B, 0, sizeof(u64) * N3);
        for (int idx = 0; idx < N3; idx++) {
            if (!A[idx]) continue;
            int allowed = 0, x = idx;
            for (int v = 0; v < n; v++) { if (x % 3 < 2) allowed |= 1 << v; x /= 3; }
            for (int m = allowed; m; m = (m - 1) & allowed) {
                int sh = 0; for (int v = 0; v < n; v++) if ((m >> v) & 1) sh += pow3[v];
                B[idx + sh] = sg[m] > 0 ? add(B[idx + sh], A[idx]) : sub(B[idx + sh], A[idx]);
            }
        }
        memcpy(A, B, sizeof(u64) * N3);
    }
    return mul(num, inv(pw(fromll(-32), (u64)n)));
}

static void graph_of_diagram(int *adj) {
    int n = nch, firsts[MAXN], k = 0;
    for (int i = 0; i < 2 * n; i++) if (i < sigma[i]) firsts[k++] = i;
    for (int u = 0; u < n; u++) adj[u] = 0;
    for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) {
        int a = firsts[u], b = firsts[v], sa = sigma[a], sb = sigma[b];
        if ((a < b && b < sa && sa < sb) || (b < a && a < sb && sb < sa)) { adj[u] |= 1 << v; adj[v] |= 1 << u; }
    }
}

static long checked_diagrams = 0;
static int failures = 0;
static u64 C0;

static void rec(int *used) {
    int n = nch, a = -1;
    for (int i = 0; i < 2 * n; i++) if (!used[i]) { a = i; break; }
    if (a < 0) {
        int adj[MAXN];
        graph_of_diagram(adj);
        if (w_at(C0) != xi(n, adj)) failures++;
        checked_diagrams++;
        return;
    }
    used[a] = 1;
    for (int b = a + 1; b < 2 * n; b++) if (!used[b]) {
        used[b] = 1; sigma[a] = b; sigma[b] = a;
        rec(used);
        used[b] = 0;
    }
    used[a] = 0;
}

/* --------------------------------------------------------------- graph moves */

static void toggle(int n, const int *adj, int a, int b, int *out) {
    for (int v = 0; v < n; v++) out[v] = adj[v];
    out[a] ^= 1 << b; out[b] ^= 1 << a;
}
static void tilde(int n, const int *adj, int a, int b, int *out) {
    for (int v = 0; v < n; v++) out[v] = adj[v];
    for (int y = 0; y < n; y++) if (y != a && y != b && ((adj[b] >> y) & 1)) { out[a] ^= 1 << y; out[y] ^= 1 << a; }
}
static int four_term(int n, const int *adj, int a, int b) {
    int g1[MAXN], g2[MAXN], g3[MAXN];
    toggle(n, adj, a, b, g1); tilde(n, adj, a, b, g2); toggle(n, g2, a, b, g3);
    return sub(xi(n, adj), xi(n, g1)) == sub(xi(n, g2), xi(n, g3));
}

static u64 rng_state = 20261012ULL;
static u64 rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

int main(void) {
    pow3[0] = 1; for (int i = 1; i < 16; i++) pow3[i] = 3 * pow3[i - 1];
    C0 = mul(fromll(-3), inv(32));
    for (nch = 0; nch <= 6; nch++) { int used[2 * MAXN] = {0}; rec(used); }
    printf("extension: %ld chord diagrams with at most 6 chords, %d failures\n", checked_diagrams, failures);
    if (failures) return 1;
    long inst = 0; int bad = 0;
    for (int n = 2; n <= 5; n++) {
        int np = n * (n - 1) / 2;
        for (int mask = 0; mask < (1 << np); mask++) {
            int adj[MAXN] = {0}, k = 0;
            for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++, k++)
                if ((mask >> k) & 1) { adj[u] |= 1 << v; adj[v] |= 1 << u; }
            for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (a != b) { if (!four_term(n, adj, a, b)) bad++; inst++; }
        }
    }
    for (int t = 0; t < 3000; t++) {
        int n = 6 + (int)(rnd() % 2), adj[MAXN] = {0};
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (rnd() & 1) { adj[u] |= 1 << v; adj[v] |= 1 << u; }
        int a = (int)(rnd() % n), b = (int)(rnd() % (n - 1)); if (b >= a) b++;
        if (!four_term(n, adj, a, b)) bad++;
        inst++;
    }
    printf("four-term relation: %ld instances, %d failures\n", inst, bad);
    if (bad) return 1;
    printf("C: all checks passed\n");
    return 0;
}
