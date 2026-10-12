// Independent check in C++, in arithmetic modulo the prime p = 2^61 - 1.
//
// (1) xi agrees with the values at c = -3/32 published by Fomichev, Karev, Pavutnitskiy and
//     Usanov (repository fomichev-d/sl2_at_-3_32, file at_-3_32.black_sl2.10.csv) on the 63
//     graphs with 9 and 10 vertices stored in ../data/fkpu_table_sample.txt.
// (2) w_D(-3/32) = xi(Gamma(D)) on 400 random chord diagrams with 7 and 8 chords.
// (3) Negative controls: the same comparison at c = 0 and at c = 1 fails on random diagrams,
//     so the test in (2) is not vacuous.
// (4) xi is invariant under random relabellings of graphs with 9 vertices.
//
// Build: c++ -O2 -std=c++17 -o check check.cpp ; run from this directory.
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>

using u64 = std::uint64_t;
using u128 = unsigned __int128;
static const u64 P = (u64(1) << 61) - 1;

static u64 md(u128 x) {
    u64 r = u64(x & P) + u64(x >> 61);
    r = (r & P) + (r >> 61);
    return r >= P ? r - P : r;
}
static u64 mul(u64 a, u64 b) { return md(u128(a) * b); }
static u64 add(u64 a, u64 b) { u64 r = a + b; return r >= P ? r - P : r; }
static u64 sub(u64 a, u64 b) { return a >= b ? a - b : a + P - b; }
static u64 fromll(long long x) { return x >= 0 ? u64(x) % P : sub(0, u64(-x) % P); }
static u64 pw(u64 a, u64 e) { u64 r = 1; while (e) { if (e & 1) r = mul(r, a); a = mul(a, a); e >>= 1; } return r; }
static u64 inv(u64 a) { return pw(a, P - 2); }

// xi of a graph given by adjacency bitmasks, via T_k = [prod x_v^2] f^k.
static u64 xi(int n, const std::vector<int>& adj) {
    std::vector<int> p3(n + 1, 1);
    for (int i = 1; i <= n; i++) p3[i] = 3 * p3[i - 1];
    int N3 = p3[n];
    std::vector<int> sg(1 << n, 1);
    for (int m = 1; m < (1 << n); m++) {
        int e = 0;
        for (int u = 0; u < n; u++) if ((m >> u) & 1) e += __builtin_popcount(adj[u] & m);
        sg[m] = ((e / 2) & 1) ? -1 : 1;
    }
    std::vector<int> shift(1 << n, 0);
    for (int m = 1; m < (1 << n); m++) { int v = __builtin_ctz(m); shift[m] = shift[m & (m - 1)] + p3[v]; }
    std::vector<int> allowed(N3, 0);
    for (int idx = 0; idx < N3; idx++) { int x = idx, a = 0; for (int v = 0; v < n; v++) { if (x % 3 < 2) a |= 1 << v; x /= 3; } allowed[idx] = a; }
    std::vector<u64> A(N3, 0), B(N3, 0);
    A[0] = 1;
    int target = N3 - 1;  // all digits equal to 2
    u64 num = 0;
    for (int k = 0; k <= 2 * n; k++) {
        num = add(num, mul(fromll((k & 1 ? -1LL : 1LL) * (k + 1)), A[target]));
        if (k == 2 * n) break;
        std::fill(B.begin(), B.end(), 0);
        for (int idx = 0; idx < N3; idx++) {
            u64 a = A[idx];
            if (!a) continue;
            int al = allowed[idx];
            for (int m = al; m; m = (m - 1) & al) {
                u64& b = B[idx + shift[m]];
                b = sg[m] > 0 ? add(b, a) : sub(b, a);
            }
        }
        std::swap(A, B);
    }
    return mul(num, inv(pw(fromll(-32), u64(n))));
}

// graph6 decoding
static int decode_g6(const std::string& s, std::vector<int>& adj) {
    int n = s[0] - 63;
    adj.assign(n, 0);
    std::vector<int> bits;
    for (size_t i = 1; i < s.size(); i++) { int x = s[i] - 63; for (int j = 5; j >= 0; j--) bits.push_back((x >> j) & 1); }
    int k = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) { if (bits[k]) { adj[i] |= 1 << j; adj[j] |= 1 << i; } k++; }
    return n;
}

// big decimal string modulo P
static u64 dec_mod(const std::string& s) {
    bool neg = !s.empty() && s[0] == '-';
    u64 r = 0;
    for (size_t i = neg ? 1 : 0; i < s.size(); i++) r = add(mul(r, 10), u64(s[i] - '0'));
    return neg ? sub(0, r) : r;
}

// ------------------------------------------------------------ weight system
struct Diagram { int n; std::vector<int> s; };

static u64 word_trace(const std::vector<int>& w, int d) {
    u64 tot = 0;
    for (int s0 = 0; s0 < d; s0++) {
        int s = s0; u64 c = 1; bool alive = true;
        for (int i = int(w.size()) - 1; i >= 0 && alive; i--) {
            switch (w[i]) {
                case 0: if (s < 1) alive = false; else { c = mul(c, fromll((long long)s * (d - s))); s--; } break;
                case 1: if (s + 1 >= d) alive = false; else s++; break;
                default: c = mul(c, fromll(d - 1 - 2 * s));
            }
        }
        if (alive && s == s0) tot = add(tot, c);
    }
    return tot;
}

static u64 W(const Diagram& D, int d) {
    int n = D.n; std::vector<int> firsts;
    for (int i = 0; i < 2 * n; i++) if (i < D.s[i]) firsts.push_back(i);
    const int la[3] = {0, 1, 2}, lb[3] = {1, 0, 2};
    const u64 tw[3] = {inv(4), inv(4), inv(8)};
    int total = 1; for (int i = 0; i < n; i++) total *= 3;
    std::vector<int> w(2 * n);
    u64 tot = 0;
    for (int code = 0; code < total; code++) {
        int x = code; u64 wt = 1;
        for (int j = 0; j < n; j++) { int ch = x % 3; x /= 3; w[firsts[j]] = la[ch]; w[D.s[firsts[j]]] = lb[ch]; wt = mul(wt, tw[ch]); }
        tot = add(tot, mul(wt, word_trace(w, d)));
    }
    return mul(tot, inv(u64(d)));
}

static u64 w_at(const Diagram& D, u64 c) {
    int m = D.n + 1;
    std::vector<u64> xs(m), ys(m);
    for (int i = 0; i < m; i++) { int d = i + 1; xs[i] = mul(fromll((long long)d * d - 1), inv(8)); ys[i] = W(D, d); }
    u64 tot = 0;
    for (int i = 0; i < m; i++) {
        u64 t = ys[i];
        for (int j = 0; j < m; j++) if (j != i) t = mul(t, mul(sub(c, xs[j]), inv(sub(xs[i], xs[j]))));
        tot = add(tot, t);
    }
    return tot;
}

static std::vector<int> graph_of(const Diagram& D) {
    int n = D.n; std::vector<int> firsts;
    for (int i = 0; i < 2 * n; i++) if (i < D.s[i]) firsts.push_back(i);
    std::vector<int> adj(n, 0);
    for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) {
        int a = firsts[u], b = firsts[v], sa = D.s[a], sb = D.s[b];
        if ((a < b && b < sa && sa < sb) || (b < a && a < sb && sb < sa)) { adj[u] |= 1 << v; adj[v] |= 1 << u; }
    }
    return adj;
}

static Diagram random_diagram(int n, std::mt19937_64& rng) {
    std::vector<int> pts(2 * n);
    for (int i = 0; i < 2 * n; i++) pts[i] = i;
    std::shuffle(pts.begin(), pts.end(), rng);
    Diagram D{n, std::vector<int>(2 * n)};
    for (int i = 0; i < n; i++) { D.s[pts[2 * i]] = pts[2 * i + 1]; D.s[pts[2 * i + 1]] = pts[2 * i]; }
    return D;
}

int main() {
    // (1) the published table
    std::ifstream in("../data/fkpu_table_sample.txt");
    std::string line; int rows = 0, bad = 0;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        std::istringstream ss(line); std::string g, val; ss >> g >> val;
        auto slash = val.find('/');
        u64 num = dec_mod(val.substr(0, slash)), den = dec_mod(val.substr(slash + 1));
        std::vector<int> adj; int n = decode_g6(g, adj);
        if (xi(n, adj) != mul(num, inv(den))) { bad++; std::printf("mismatch on %s\n", g.c_str()); }
        rows++;
    }
    std::printf("published table: %d graphs with 9 or 10 vertices, %d mismatches\n", rows, bad);
    if (rows == 0 || bad) return 1;
    // (2) the extension property on random diagrams
    std::mt19937_64 rng(20261012);
    u64 c0 = mul(fromll(-3), inv(32));
    int fails = 0, cnt = 0;
    for (int t = 0; t < 400; t++) {
        Diagram D = random_diagram(7 + (t & 1), rng);
        auto adj = graph_of(D);
        if (w_at(D, c0) != xi(D.n, adj)) fails++;
        cnt++;
    }
    std::printf("extension: %d random chord diagrams with 7 or 8 chords, %d failures\n", cnt, fails);
    if (fails) return 1;
    // (3) negative controls
    for (long long cnum : {0LL, 1LL}) {
        int differ = 0;
        for (int t = 0; t < 20; t++) {
            Diagram D = random_diagram(5, rng);
            auto adj = graph_of(D);
            if (w_at(D, fromll(cnum)) != xi(D.n, adj)) differ++;
        }
        std::printf("control at c = %lld: %d of 20 diagrams differ from xi\n", cnum, differ);
        if (differ == 0) return 1;
    }
    // (4) relabelling invariance
    for (int t = 0; t < 10; t++) {
        int n = 9; std::vector<int> adj(n, 0), perm(n), adj2(n, 0);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (rng() & 1) { adj[u] |= 1 << v; adj[v] |= 1 << u; }
        for (int i = 0; i < n; i++) perm[i] = i;
        std::shuffle(perm.begin(), perm.end(), rng);
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if ((adj[u] >> v) & 1) adj2[perm[u]] |= 1 << perm[v];
        if (xi(n, adj) != xi(n, adj2)) { std::printf("relabelling failure\n"); return 1; }
    }
    std::printf("relabelling invariance: 10 random graphs with 9 vertices\n");
    std::printf("C++: all checks passed\n");
    return 0;
}
