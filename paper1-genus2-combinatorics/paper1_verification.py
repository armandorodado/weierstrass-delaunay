#!/usr/bin/env python3
"""
Independent verification of the computational claims of

  A. Rodado Amaris, "Delaunay Combinatorics of the Moduli and Teichmueller Space
  of Closed Genus-Two Riemann Surfaces"  (Remark 8.12 and Sections 7.3-7.4, 7.6).

Everything is computed on the DUAL TRIANGULATION side: a map T on the sphere with
six vertices (the cone points), encoded by a rotation system on darts.  Under
duality with the graph G of the paper,
  * contracting a non-loop edge of G  = deleting a non-bridge edge of T,
  * expanding a vertex of G            = inserting a diagonal in a face of T of degree >= 4,
  * "G has no monogon"                 = "T has no vertex of degree one",
  * G is trivalent                     = every face of T is a triangle.

Checks performed (expected values from the paper in brackets):
  1. leaf-free six-vertex sphere maps by number of edges   [20,55,97,71,31,5,1 for E=12..6; 280]
  2. trivalent types and abstract graphs                   [20 types, 17 abstract graphs]
  3. contraction hierarchy from the two generic types      [2,6,22,32,22,5,1 = 90]
  4. closure from Theta_6 by expansion only                [128 types; 66 of the 90 reached, 24 missed]
     and by expansion + contraction                        [280 = all leaf-free maps]
  5. realizability (strictly positive solution of A x = 1) [10 of 20; 116 of 280; 2,5,13,12,6,2,1 in the hierarchy]
  6. the explicit stacked-type configuration of Prop. 7.3: cone angles, triangle inequalities,
     signed wedge angles x_e (Section 7.4), the hyperbolic Delaunay criterion, the perfect
     matching of Lemma 7.5, and the edge orbits of Aut(T_2).

Requires: Python 3, numpy, scipy (HiGHS LP), networkx.   Run time: about one minute.
Usage:    python3 paper1_verification.py
"""

import math
import sys
from collections import Counter
from itertools import permutations

import networkx as nx
import numpy as np
from scipy.optimize import linprog

N = 6  # number of cone points

# ---------------------------------------------------------------------------
# Combinatorial maps: darts 0..2E-1, dart d and d^1 form edge d//2,
# sig[d] = next dart counter-clockwise around the tail vertex of d.
# ---------------------------------------------------------------------------


def orbits(perm):
    seen, out = [False] * len(perm), []
    for d in range(len(perm)):
        if not seen[d]:
            cyc, x = [], d
            while not seen[x]:
                seen[x] = True
                cyc.append(x)
                x = perm[x]
            out.append(cyc)
    return out


def vertices(sig):
    return orbits(sig)


def faces(sig):
    return orbits([sig[d ^ 1] for d in range(len(sig))])


def code_from(sig, root):
    lab, order, i = {root: 0}, [root], 0
    while i < len(order):
        d = order[i]
        i += 1
        for e in (sig[d], d ^ 1):
            if e not in lab:
                lab[e] = len(order)
                order.append(e)
    return tuple((lab[sig[d]], lab[d ^ 1]) for d in order)


def canon(sig):
    """(canonical code, |Aut+|); the code is shorter than sig iff the map is disconnected."""
    codes = [code_from(sig, r) for r in range(len(sig))]
    c = min(codes)
    return c, codes.count(c)


def from_code(c):
    pm, nxt = {}, 0
    for d in range(len(c)):
        if d not in pm:
            pm[d], pm[c[d][1]] = nxt, nxt + 1
            nxt += 2
    sig = [0] * len(c)
    for d in range(len(c)):
        sig[pm[d]] = pm[c[d][0]]
    return sig


def delete_edge(sig, k):
    s = list(sig)
    for d in (2 * k, 2 * k + 1):
        p = s.index(d)
        s[p] = s[d] if s[d] != d else p
        s[d] = None
    keep = [d for d in range(len(s)) if s[d] is not None]
    new = {d: i for i, d in enumerate(keep)}
    return [new[s[d]] for d in keep]


def add_edge(sig, x, y):
    """Insert an edge in the corners just before darts x and y."""
    m = len(sig)
    s = sig + [0, 0]
    a, b = m, m + 1
    px = sig.index(x)
    s[px], s[a] = a, x
    py = [d for d in range(m + 2) if s[d] == y and d != a][0]
    s[py], s[b] = b, y
    return s


def add_leaf(sig, x):
    m = len(sig)
    s = sig + [0, 0]
    p = sig.index(x)
    s[p], s[m], s[m + 1] = m, x, m + 1
    return s


def leaf_free(sig):
    return min(len(v) for v in vertices(sig)) >= 2


# ---------------------------------------------------------------------------
# 1. All six-vertex sphere maps with every face of degree >= 3:
#    plane trees on six vertices, then every way of adding edges.
# ---------------------------------------------------------------------------


def all_maps():
    level = {canon([0, 1])[0]}
    for _ in range(N - 2):
        level = {canon(add_leaf(from_code(c), x))[0] for c in level for x in range(len(c))}
    level = {c for c in level if all(len(f) >= 3 for f in faces(from_code(c)))}
    out = set(level)
    while level:
        nxt = set()
        for c in level:
            sig = from_code(c)
            F = faces(sig)
            for f in F:
                d = len(f)
                for i in range(d):
                    for k in range(2, d - 1):
                        s = add_edge(sig, f[i], f[(i + k) % d])
                        fs = faces(s)
                        if len(fs) == len(F) + 1 and all(len(x) >= 3 for x in fs):
                            nxt.add(canon(s)[0])
        out |= nxt
        level = nxt
    return out


def contractions(c):
    sig, out = from_code(c), set()
    for k in range(len(sig) // 2):
        s2 = delete_edge(sig, k)
        c2 = canon(s2)[0]
        if len(vertices(s2)) == N and len(c2) == len(s2) and leaf_free(s2):
            out.add(c2)
    return out


def expansions(c):
    sig, out = from_code(c), set()
    F = faces(sig)
    for f in F:
        d = len(f)
        for i in range(d):
            for k in range(2, d - 1):
                s = add_edge(sig, f[i], f[(i + k) % d])
                fs = faces(s)
                if len(fs) == len(F) + 1 and all(len(x) >= 3 for x in fs):
                    out.add(canon(s)[0])
    return out


def realizable(c):
    """Strictly positive solution of A x = 1 (A = vertex-edge incidence matrix of T)."""
    sig = from_code(c)
    V = vertices(sig)
    vid = {d: i for i, v in enumerate(V) for d in v}
    E = len(sig) // 2
    A = np.zeros((N, E))
    for k in range(E):
        A[vid[2 * k], k] += 1
        A[vid[2 * k + 1], k] += 1
    cost = np.zeros(E + 1)
    cost[-1] = -1                                  # maximise t subject to x_e >= t
    Aub = np.zeros((E, E + 1))
    for k in range(E):
        Aub[k, k], Aub[k, -1] = -1, 1
    r = linprog(cost, A_ub=Aub, b_ub=np.zeros(E), A_eq=np.hstack([A, np.zeros((N, 1))]),
                b_eq=np.ones(N), bounds=[(None, 1)] * (E + 1), method="highs")
    return r.status == 0 and -r.fun > 1e-9


def dual_multigraph(c):
    sig = from_code(c)
    fid = {d: i for i, f in enumerate(faces(sig)) for d in f}
    g = nx.MultiGraph()
    g.add_nodes_from(range(len(faces(sig))))
    for k in range(len(sig) // 2):
        g.add_edge(fid[2 * k], fid[2 * k + 1])
    return g


# ---------------------------------------------------------------------------
# 6. The explicit stacked configuration (Prop. 7.3, Section 7.4, Lemma 7.5)
# ---------------------------------------------------------------------------


def check_stacked_configuration(report):
    GE = [(1, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 4), (3, 7), (4, 8), (5, 6), (5, 8), (6, 7), (7, 8)]
    G = nx.Graph(GE)
    ok, emb = nx.check_planarity(G)
    assert ok
    fcs, seen = [], set()
    for u, v in emb.edges():
        if (u, v) not in seen:
            fcs.append(emb.traverse_face(u, v, mark_half_edges=seen))

    def face_left(u, v):
        for i, f in enumerate(fcs):
            for k in range(len(f)):
                if f[k] == u and f[(k + 1) % len(f)] == v:
                    return i

    TE = [(face_left(u, v), face_left(v, u)) for u, v in GE]          # T-edge e_k
    tri = {x: [k for k, e in enumerate(GE) if x in e] for x in G.nodes}
    L = {1: 1.8269, 2: 1.4751, 3: 1.4751, 4: 1.4751, 5: 1.4751, 6: 1.3347, 9: 1.3347,
         7: 1.6979, 8: 1.6979, 10: 1.6979, 11: 1.6979, 12: 1.4942}
    ell = [L[k + 1] for k in range(12)]

    def ang(a, b, c):
        return math.acos((math.cosh(b) * math.cosh(c) - math.cosh(a)) / (math.sinh(b) * math.sinh(c)))

    cone, corner, tri_ok = [0.0] * 6, {}, True
    for x, ks in tri.items():
        a = [ell[k] for k in ks]
        tri_ok &= all(a[i] < a[(i + 1) % 3] + a[(i + 2) % 3] for i in range(3))
        for i in range(3):
            o = [ks[(i + 1) % 3], ks[(i + 2) % 3]]
            F = (set(TE[o[0]]) & set(TE[o[1]])).pop()
            corner[(x, F)] = ang(ell[ks[i]], ell[o[0]], ell[o[1]])
            cone[F] += corner[(x, F)]
    xe, outside = [0.0] * 12, 0
    for x, ks in tri.items():
        for k in ks:
            A, B = TE[k]
            C = [F for F in {f for j in ks for f in TE[j]} if F not in (A, B)][0]
            d = (corner[(x, A)] + corner[(x, B)] - corner[(x, C)]) / 2
            outside += d < 0
            xe[k] += d / math.pi
    match = [TE[3], TE[5], TE[10]]
    auts = [p for p in permutations(range(6))
            if {frozenset(p[a] for a in e) for e in TE} == {frozenset(e) for e in TE}]
    orbits_ = sorted({tuple(sorted({1 + [frozenset(e) for e in TE].index(frozenset(p[a] for a in TE[k]))
                                    for p in auts})) for k in range(12)})
    report("cone angles / pi (all 1)", [round(c / math.pi, 4) for c in cone],
           all(abs(c / math.pi - 1) < 1e-3 for c in cone))
    report("triangle inequalities hold", tri_ok, tri_ok)
    report("signed x_e values", sorted(set(round(v, 4) for v in xe)),
           sorted(set(round(v, 4) for v in xe)) == [0.0699, 0.1511, 0.3139, 0.3255, 0.3722])
    report("circumcentres outside their triangle", outside, outside == 0)
    report("hyperbolic Delaunay criterion (all x_e > 0)", min(xe) > 0, min(xe) > 0)
    report("Lemma 7.5 matching e4,e6,e11 is perfect", match,
           len({v for e in match for v in e}) == 6)
    report("|Aut(T_2)| and edge orbits", (len(auts), orbits_),
           len(auts) == 4 and orbits_ == [(1,), (2, 3, 4, 5), (6, 9), (7, 8, 10, 11), (12,)])


# ---------------------------------------------------------------------------


def main():
    failures = []

    def report(name, value, ok):
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: {value}")
        if not ok:
            failures.append(name)

    print("1. Six-vertex sphere maps")
    maps = all_maps()
    lf = {c for c in maps if leaf_free(from_code(c))}
    by_e = [sum(1 for c in lf if len(c) == 2 * E) for E in range(12, 5, -1)]
    report("leaf-free maps with 12..6 edges", by_e, by_e == [20, 55, 97, 71, 31, 5, 1])
    report("total leaf-free maps", len(lf), len(lf) == 280)

    print("2. Trivalent types")
    top = [c for c in lf if len(c) == 24]
    classes = []
    for c in top:
        g = dual_multigraph(c)
        for cl in classes:
            if nx.is_isomorphic(g, cl):
                break
        else:
            classes.append(g)
    report("trivalent types / abstract graphs", (len(top), len(classes)),
           (len(top), len(classes)) == (20, 17))
    sig_ = Counter(tuple(sorted(len(v) for v in vertices(from_code(c)))) for c in top)
    report("signature shared by two types", [s for s, m in sig_.items() if m > 1],
           [s for s, m in sig_.items() if m > 1] == [(2, 2, 3, 3, 7, 7)])
    auts = {tuple(sorted(len(v) for v in vertices(from_code(c)))): canon(from_code(c))[1] for c in top}
    report("|Aut+| of octahedral and stacked types", (auts[(4,) * 6], auts[(3, 3, 4, 4, 5, 5)]),
           (auts[(4,) * 6], auts[(3, 3, 4, 4, 5, 5)]) == (24, 2))

    print("3. Contraction hierarchy from the two generic types")
    octa = next(c for c in top if sorted(len(v) for v in vertices(from_code(c))) == [4] * 6)
    stk = next(c for c in top if sorted(len(v) for v in vertices(from_code(c))) == [3, 3, 4, 4, 5, 5])
    levels = [{octa, stk}]
    while True:
        nxt = set().union(*(contractions(c) for c in levels[-1]))
        if not nxt:
            break
        levels.append(nxt)
    H = set().union(*levels)
    report("types per level", [len(l) for l in levels], [len(l) for l in levels] == [2, 6, 22, 32, 22, 5, 1])

    print("4. Regeneration from Theta_6")
    theta = next(c for c in lf if len(c) == 12)
    R, fr = {theta}, {theta}
    while fr:
        fr = set().union(*(expansions(c) for c in fr)) - R
        R |= fr
    report("expansion-only closure; reached/missed of the 90", (len(R), len(H & R), len(H - R)),
           (len(R), len(H & R), len(H - R)) == (128, 66, 24))
    report("missed types by level", [len(l - R) for l in levels],
           [len(l - R) for l in levels] == [0, 0, 2, 9, 10, 3, 0])
    M, fr = {theta}, {theta}
    while fr:
        fr = set().union(*(expansions(c) | contractions(c) for c in fr)) - M
        M |= fr
    report("expansion+contraction closure equals all leaf-free maps", len(M), M == lf)

    print("5. Realizability (strictly positive solution of A x = 1)")
    real = {c for c in lf if realizable(c)}
    report("realizable trivalent types", sum(1 for c in real if len(c) == 24),
           sum(1 for c in real if len(c) == 24) == 10)
    report("realizable types in total; with 11 and 7 edges",
           (len(real), sum(1 for c in real if len(c) == 22), sum(1 for c in real if len(c) == 14)),
           (len(real), sum(1 for c in real if len(c) == 22), sum(1 for c in real if len(c) == 14)) == (116, 26, 2))
    per = [len(l & real) for l in levels]
    report("realizable types per hierarchy level", per, per == [2, 5, 13, 12, 6, 2, 1])

    print("6. Explicit stacked configuration (Prop. 7.3, Section 7.4, Lemma 7.5)")
    check_stacked_configuration(report)

    print("\nALL CHECKS PASSED" if not failures else f"\nFAILED: {failures}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
