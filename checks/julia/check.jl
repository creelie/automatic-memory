# Independent check in exact rational arithmetic (Rational{BigInt}).
#
# (1) For every chord diagram with at most 4 chords and for random diagrams with 5 chords,
#     the polynomial w_D(c) is obtained by Newton interpolation from tr(C_D)/d in the
#     d-dimensional representations, d = 1, ..., n+1 (dense matrices), and w_D(-3/32) is
#     compared with xi of the intersection graph.
# (2) The four-term relation of xi is checked on all labelled graphs with at most 4 vertices
#     and all ordered pairs of distinct vertices, and on random graphs with 5 vertices.
# (3) xi is also computed from the polynomial S_G(N) = sum_{p : V -> 2-subsets of [N]} sign:
#     S_G(N) is evaluated at N = 0..2n by enumeration-free counting, interpolated, and
#     xi = S_G(-2) / (-32)^n is compared with the T_k formula.

using Random

const Q = Rational{BigInt}

function chord_diagrams(n)
    out = Vector{Vector{Int}}()
    function rec(free, s)
        if isempty(free)
            push!(out, copy(s)); return
        end
        a = free[1]
        for j in 2:length(free)
            b = free[j]
            s[a+1] = b; s[b+1] = a
            rec(vcat(free[2:j-1], free[j+1:end]), s)
        end
    end
    rec(collect(0:2n-1), zeros(Int, 2n))
    out
end

function random_diagram(n, rng)
    pts = shuffle(rng, collect(0:2n-1))
    s = zeros(Int, 2n)
    for i in 1:n
        a, b = pts[2i-1], pts[2i]
        s[a+1] = b; s[b+1] = a
    end
    s
end

function intersection_graph(s)
    n = length(s) ÷ 2
    firsts = [i for i in 0:2n-1 if i < s[i+1]]
    E = Set{Tuple{Int,Int}}()
    for u in 1:n, v in u+1:n
        a, b = firsts[u], firsts[v]
        sa, sb = s[a+1], s[b+1]
        if (a < b < sa < sb) || (b < a < sb < sa)
            push!(E, (u - 1, v - 1))
        end
    end
    n, E
end

# Representation matrices: E e_s = s(d-s) e_{s-1}, F e_s = e_{s+1}, H e_s = (d-1-2s) e_s.
function rep(d)
    Em = zeros(Q, d, d); Fm = zeros(Q, d, d); Hm = zeros(Q, d, d)
    for s in 0:d-1
        s >= 1 && (Em[s, s+1] = s * (d - s))
        s + 1 < d && (Fm[s+2, s+1] = 1)
        Hm[s+1, s+1] = d - 1 - 2s
    end
    (Em, Fm, Hm)
end

const TENSOR = [(1, 2, Q(1, 4)), (2, 1, Q(1, 4)), (3, 3, Q(1, 8))]

function W(s, d)
    n = length(s) ÷ 2
    M = rep(d)
    firsts = [i for i in 0:2n-1 if i < s[i+1]]
    tot = zero(Q)
    for choice in Iterators.product(ntuple(_ -> TENSOR, n)...)
        word = zeros(Int, 2n)
        wt = one(Q)
        for (k, i) in enumerate(firsts)
            a, b, c = choice[k]
            word[i+1] = a; word[s[i+1]+1] = b; wt *= c
        end
        P = Matrix{Q}(I_(d))
        for l in word
            P = P * M[l]
        end
        tot += wt * sum(P[j, j] for j in 1:d)
    end
    tot / d
end

I_(d) = [i == j ? one(Q) : zero(Q) for i in 1:d, j in 1:d]

function newton_eval(xs, ys, x)
    m = length(xs)
    c = copy(ys)
    for j in 2:m, i in m:-1:j
        c[i] = (c[i] - c[i-1]) / (xs[i] - xs[i-j+1])
    end
    v = c[m]
    for i in m-1:-1:1
        v = v * (x - xs[i]) + c[i]
    end
    v
end

w_at(s, c) = begin
    n = length(s) ÷ 2
    xs = [Q(d * d - 1, 8) for d in 1:n+1]
    ys = [W(s, d) for d in 1:n+1]
    newton_eval(xs, ys, c)
end

# T_k(G) via the generating function in Z[x_v]/(x_v^3), arrays indexed in base 3.
function T_all(n, E)
    adj = zeros(Int, n)
    for (u, v) in E
        adj[u+1] |= 1 << v; adj[v+1] |= 1 << u
    end
    terms = Tuple{Int,Int}[]
    for m in 1:(1<<n)-1
        e = 0
        for u in 0:n-1
            ((m >> u) & 1 == 1) && (e += count_ones(adj[u+1] & m))
        end
        push!(terms, (m, iseven(e ÷ 2) ? 1 : -1))
    end
    N3 = 3^n
    P = zeros(BigInt, N3); P[1] = 1
    target = sum(2 * 3^v for v in 0:n-1; init = 0) + 1
    out = BigInt[]
    for k in 0:2n
        push!(out, P[target])
        Qa = zeros(BigInt, N3)
        for idx in 0:N3-1
            P[idx+1] == 0 && continue
            digs = [(idx ÷ 3^v) % 3 for v in 0:n-1]
            for (m, sg) in terms
                ok = true; add = 0
                for v in 0:n-1
                    if (m >> v) & 1 == 1
                        digs[v+1] == 2 && (ok = false; break)
                        add += 3^v
                    end
                end
                ok && (Qa[idx+add+1] += sg * P[idx+1])
            end
        end
        P = Qa
    end
    out
end

xi(n, E) = begin
    T = T_all(n, E)
    Q(sum((-1)^k * (k + 1) * T[k+1] for k in 0:2n; init = BigInt(0))) // Q(BigInt(-32)^n)
end

# S_G(N) = sum_k binom(N, k) T_k(G), evaluated at N = 0..2n and interpolated at N = -2.
function xi_via_S(n, E)
    T = T_all(n, E)
    xs = [Q(N) for N in 0:2n]
    ys = [Q(sum(binomial(BigInt(N), k) * T[k+1] for k in 0:2n; init = BigInt(0))) for N in 0:2n]
    newton_eval(xs, ys, Q(-2)) / Q(BigInt(-32)^n)
end

toggle(E, a, b) = symdiff(E, Set([(min(a, b), max(a, b))]))
function tilde(n, E, a, b)
    nb = [y for y in 0:n-1 if y != a && y != b && (min(b, y), max(b, y)) in E]
    symdiff(E, Set([(min(a, y), max(a, y)) for y in nb]))
end

function main()
    rng = MersenneTwister(20261012)
    c0 = Q(-3, 32)
    cnt = 0
    for n in 0:4
        for s in chord_diagrams(n)
            m, E = intersection_graph(s)
            @assert w_at(s, c0) == xi(m, E)
            cnt += 1
        end
    end
    for _ in 1:20
        s = random_diagram(5, rng)
        m, E = intersection_graph(s)
        @assert w_at(s, c0) == xi(m, E)
        cnt += 1
    end
    println("extension: w_D(-3/32) = xi(Gamma(D)) for $cnt chord diagrams")
    cnt = 0
    for n in 2:4
        allp = [(u, v) for u in 0:n-1 for v in u+1:n-1]
        for mask in 0:(1<<length(allp))-1
            E = Set([allp[i] for i in 1:length(allp) if (mask >> (i - 1)) & 1 == 1])
            @assert xi(n, E) == xi_via_S(n, E)
            for a in 0:n-1, b in 0:n-1
                a == b && continue
                G1 = toggle(E, a, b); G2 = tilde(n, E, a, b); G3 = toggle(G2, a, b)
                @assert xi(n, E) - xi(n, G1) == xi(n, G2) - xi(n, G3)
                cnt += 1
            end
        end
    end
    allp = [(u, v) for u in 0:4 for v in u+1:4]
    for _ in 1:30
        E = Set([e for e in allp if rand(rng) < 0.5])
        a, b = randperm(rng, 5)[1:2] .- 1
        G1 = toggle(E, a, b); G2 = tilde(5, E, a, b); G3 = toggle(G2, a, b)
        @assert xi(5, E) - xi(5, G1) == xi(5, G2) - xi(5, G3)
        cnt += 1
    end
    println("four-term relation: $cnt instances; S_G(-2)/(-32)^n agrees with the T_k formula")
    println("JULIA: all checks passed")
end

main()
