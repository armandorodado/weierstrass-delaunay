#!/usr/bin/env python3
"""
Computational verification of the Weierstrass--Delaunay cell decomposition
of the hyperelliptic locus  H_g = M_{0,2g+2}/S_{2g+2}  (genus g >= 2).

Companion code for:  A. Rodado Amaris, "Face-Constraint Independence, a Hall
Criterion, and the Combinatorial Immersion C_{g-1} -> C_g for Hyperelliptic
Surfaces of Arbitrary Genus", Section "Computational verification".

What it does
------------
Let n = 2g+2.  A cell of the decomposition of T(0,n) is a Delaunay
cellulation T of the sphere whose vertices are the n cone points (equivalently,
the dual H = T* of a Delaunay graph of the hyperelliptic surface).  We encode T
as a combinatorial map (rotation system on darts) and:

 1. enumerate all triangulations of S^2 with n vertices (loops and multiple
    edges allowed) by flips from a bipyramid -- the flip graph is connected;
 2. keep those T for which the vertex system  A x = 1  has a solution with x > 0
    (Paper 5, Theorem "realization" + Hall criterion; tested here by an LP);
 3. descend through all polytope facets: a facet of the closed polytope
    {x >= 0, A x = 1} is  {x_e = 0} for some e;  the set Z of edges forced to
    vanish there is found by an LP, and the facet is the open cell of T \\ Z
    provided T \\ Z is connected with n vertices and has dimension one less.
    (Disconnected T \\ Z is not a cellulation by convex Delaunay cells, so that
    facet lies at infinity of T(0,n).)
 4. dim P(T) = |E| - rank A  (rank A = n, or n-1 when T is bipartite).
 5. Euler characteristic:  chi^orb(M_{0,n}/S_n) = sum_T (-1)^dim / |Aut+(T)|,
    and chi^orb(H_g) = chi^orb(M_{0,n}/S_n) / 2   (generic stabiliser <J>).
    Target:  chi(M_{0,n}) = (-1)^(n-3) (n-3)!,  so  chi^orb = that / n!.
 6. (optional, --homology) rational Borel--Moore homology of the orbit complex:
    cells whose stabiliser reverses the orientation of the cell are dropped
    (they contribute 0 rationally); incidence signs are computed from explicit
    bases of ker A carried through the dart isomorphisms.  Ranks are computed
    modulo a large prime p; since b_i(Q) <= b_i(F_p) for all i and both have
    the same Euler characteristic, a mod-p answer concentrated in one degree is
    exact over Q.  Target:  H^BM_* = Q in the top degree 2(n-3), 0 otherwise.

Usage
-----
    python3 weierstrass_delaunay_check.py 6              # genus 2, seconds
    python3 weierstrass_delaunay_check.py 6 --homology
    python3 weierstrass_delaunay_check.py 8 --homology   # genus 3, ~45 min

Requires numpy and scipy (HiGHS LP solver).  Exact rational arithmetic is used
for all Euler-characteristic sums and integer arithmetic for d^2 = 0.
"""

import argparse
import math
import sys
import time
from collections import defaultdict
from fractions import Fraction

import numpy as np
from scipy.linalg import null_space
from scipy.optimize import linprog

# ---------------------------------------------------------------------------
# Combinatorial maps.  Darts 0..2E-1; dart d and d^1 form edge d//2.
# sig[d] = next dart counter-clockwise around the vertex at the tail of d.
# Faces are orbits of d -> sig[d^1].
# ---------------------------------------------------------------------------


def orbits(perm):
    seen = [False] * len(perm)
    out = []
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


def bfs_labels(sig, root):
    lab, order, i = {root: 0}, [root], 0
    while i < len(order):
        d = order[i]
        i += 1
        for e in (sig[d], d ^ 1):
            if e not in lab:
                lab[e] = len(order)
                order.append(e)
    return lab, order


def code_from(sig, root):
    """Canonical code of the map rooted at `root` (covers the root's component)."""
    lab, order = bfs_labels(sig, root)
    return tuple((lab[sig[d]], lab[d ^ 1]) for d in order)


def canon(sig):
    """(canonical code, |Aut+|).  Code length < len(sig) iff the map is disconnected."""
    codes = [code_from(sig, r) for r in range(len(sig))]
    c = min(codes)
    return c, codes.count(c)


def code_dart_map(c):
    """Bijection code-position -> dart index of from_code(c)."""
    pm, nxt = {}, 0
    for d in range(len(c)):
        if d not in pm:
            pm[d] = nxt
            pm[c[d][1]] = nxt + 1
            nxt += 2
    return pm


def from_code(c):
    pm = code_dart_map(c)
    sig = [0] * len(c)
    for d in range(len(c)):
        sig[pm[d]] = pm[c[d][0]]
    return sig


def delete_edge(sig, k):
    """Delete edge k; returns (new sig, map old dart -> new dart)."""
    s = list(sig)
    for d in (2 * k, 2 * k + 1):
        p = s.index(d)
        s[p] = s[d] if s[d] != d else p
        s[d] = None
    keep = [d for d in range(len(s)) if s[d] is not None]
    new = {d: i for i, d in enumerate(keep)}
    return [new[s[d]] for d in keep], new


def delete_edges(sig, Z):
    m = {d: d for d in range(len(sig))}
    s = sig
    for k in sorted(Z, reverse=True):
        kk = m[2 * k] // 2
        s, new = delete_edge(s, kk)
        m = {d: new[v] for d, v in m.items() if v // 2 != kk}
    return s, m


def add_edge(sig, x, y):
    """Insert an edge in the corner before dart x and the corner before dart y."""
    m = len(sig)
    s = sig + [0, 0]
    a, b = m, m + 1
    px = sig.index(x)
    s[px], s[a] = a, x
    py = [d for d in range(m + 2) if s[d] == y and d != a][0]
    s[py], s[b] = b, y
    return s


def incidence(sig):
    V = vertices(sig)
    vid = {d: i for i, v in enumerate(V) for d in v}
    E = len(sig) // 2
    A = np.zeros((len(V), E))
    for k in range(E):
        A[vid[2 * k], k] += 1
        A[vid[2 * k + 1], k] += 1
    return A


def bipyramid(n):
    """A triangulation of S^2 with n >= 4 vertices (two hubs over an (n-2)-gon)."""
    m = n - 2
    pos = {0: np.array([0, 0, 1.0]), 1: np.array([0, 0, -1.0])}
    for i in range(m):
        pos[2 + i] = np.array([math.cos(2 * math.pi * i / m), math.sin(2 * math.pi * i / m), 0])
    edges = [(2 + i, 2 + (i + 1) % m) for i in range(m)]
    edges += [(0, 2 + i) for i in range(m)] + [(1, 2 + i) for i in range(m)]
    darts = []
    for u, v in edges:
        darts += [(u, v), (v, u)]
    sig = [0] * len(darts)
    for v in range(n):
        ds = [i for i, (a, _) in enumerate(darts) if a == v]
        nrm = pos[v] / np.linalg.norm(pos[v])
        r1 = np.cross(nrm, [0.3, 0.7, 0.2])
        r1 /= np.linalg.norm(r1)
        r2 = np.cross(nrm, r1)

        def ang(i):
            w = pos[darts[i][1]] - pos[v]
            return math.atan2(np.dot(w, r2), np.dot(w, r1))

        ds.sort(key=ang)
        for j, i in enumerate(ds):
            sig[i] = ds[(j + 1) % len(ds)]
    return sig


# ---------------------------------------------------------------------------
# Polytope computations
# ---------------------------------------------------------------------------


def relint_point(A, fixed_zero=()):
    """A point in the relative interior of {x >= 0, Ax = 1, x_f = 0 (f in fixed_zero)},
    and the set of coordinates vanishing on that whole face.  (None, None) if empty."""
    E = A.shape[1]
    dl = 1.0 / (4 * E)
    c = np.concatenate([np.zeros(E), -np.ones(E)])          # maximise sum of slacks y
    Aub = np.zeros((E, 2 * E))
    for f in range(E):
        Aub[f, f], Aub[f, E + f] = -1, 1                     # y_f <= x_f
    bnds = [(0, 0) if f in fixed_zero else (0, 1) for f in range(E)] + [(0, dl)] * E
    r = linprog(c, A_ub=Aub, b_ub=np.zeros(E), A_eq=np.hstack([A, np.zeros_like(A)]),
                b_eq=np.ones(A.shape[0]), bounds=bnds, method="highs")
    if r.status != 0:
        return None, None
    y = r.x[E:]
    return r.x[:E], {f for f in range(E) if y[f] < dl / 2}


# ---------------------------------------------------------------------------
# Enumeration
# ---------------------------------------------------------------------------


def triangulations(n, log):
    start = canon(bipyramid(n))[0]
    seen, frontier = {start}, [start]
    while frontier:
        nxt = []
        for c in frontier:
            sig = from_code(c)
            for k in range(len(sig) // 2):                   # flip edge k
                s2, _ = delete_edge(sig, k)
                if len(vertices(s2)) != n:
                    continue
                for f in faces(s2):
                    if len(f) != 4:
                        continue
                    for x, y in ((f[0], f[2]), (f[1], f[3])):
                        s3 = add_edge(s2, x, y)
                        if any(len(ff) != 3 for ff in faces(s3)):
                            continue
                        c3 = canon(s3)[0]
                        if len(c3) == len(s3) and c3 not in seen:
                            seen.add(c3)
                            nxt.append(c3)
        frontier = nxt
    log(f"triangulations of S^2 with {n} vertices: {len(seen)}")
    return seen


def enumerate_cells(n, log):
    tri = triangulations(n, log)
    leaf_free = sum(1 for c in tri if min(len(v) for v in vertices(from_code(c))) >= 2)
    log(f"  of which without degree-1 vertices (dual graph has no monogon): {leaf_free}")
    cells = {}

    def register(c):
        sig = from_code(c)
        A = incidence(sig)
        x, Z = relint_point(A)
        if x is None or Z:                                   # not strictly positive
            return False
        E = len(sig) // 2
        cells[c] = dict(E=E, dim=int(E - np.linalg.matrix_rank(A)), aut=canon(sig)[1],
                        x=x, B=null_space(A), facets=[])
        return True

    queue = [c for c in tri if register(c)]
    log(f"  realizable (top-dimensional cells): {len(queue)}")
    tried = set(tri)
    qi = 0
    while qi < len(queue):
        c = queue[qi]
        qi += 1
        cell = cells[c]
        sig = from_code(c)
        A = incidence(sig)
        seenZ = set()
        for e in range(cell["E"]):
            p, Z = relint_point(A, {e})
            if p is None:
                continue
            Z = frozenset(Z)
            if Z in seenZ:
                continue
            seenZ.add(Z)
            s2, _ = delete_edges(sig, Z)
            c2 = canon(s2)[0]
            if len(c2) != len(s2) or len(vertices(s2)) != n:
                continue                                     # facet at infinity
            if len(s2) // 2 - np.linalg.matrix_rank(incidence(s2)) != cell["dim"] - 1:
                continue                                     # not a facet
            if c2 not in cells:
                if c2 in tried:
                    continue
                tried.add(c2)
                if not register(c2):
                    continue
                queue.append(c2)
            cell["facets"].append((c2, tuple(sorted(Z)), p))
    return cells


# ---------------------------------------------------------------------------
# Euler characteristic
# ---------------------------------------------------------------------------


def euler(cells, n, log):
    tab = defaultdict(lambda: [0, Fraction(0)])
    chi = Fraction(0)
    for cell in cells.values():
        w = Fraction((-1) ** cell["dim"], cell["aut"])
        chi += w
        tab[(cell["E"], cell["dim"])][0] += 1
        tab[(cell["E"], cell["dim"])][1] += w
    log("\n  edges  dim   cells   sum (-1)^dim/|Aut+|")
    for (E, d) in sorted(tab):
        log(f"  {E:5d} {d:4d} {tab[(E, d)][0]:7d}   {tab[(E, d)][1]}")
    target = Fraction((-1) ** (n - 3) * math.factorial(n - 3), math.factorial(n))
    log(f"\n  total cells: {len(cells)}")
    log(f"  chi^orb(M_0,{n}/S_{n}) from cells = {chi}    expected {target}    "
        f"{'OK' if chi == target else 'MISMATCH'}")
    if n % 2 == 0:
        log(f"  chi^orb(H_{(n - 2) // 2}) = {chi / 2}")
    return chi == target


# ---------------------------------------------------------------------------
# Homology
# ---------------------------------------------------------------------------


def orientation_preserved(c, cell):
    sig = from_code(c)
    pm = code_dart_map(c)
    B, E = cell["B"], cell["E"]
    for r in range(len(sig)):
        if code_from(sig, r) != c:
            continue
        lab, _ = bfs_labels(sig, r)
        P = np.zeros((E, E))
        for k in range(E):
            P[pm[lab[2 * k]] // 2, k] = 1
        M = np.linalg.lstsq(B, P @ B, rcond=None)[0]
        if np.linalg.det(M) < 0:
            return False
    return True


def incidences(c, cells):
    cell = cells[c]
    sig = from_code(c)
    B, E = cell["B"], cell["E"]
    out = {}
    for c2, Z, p in cell["facets"]:
        face = cells[c2]
        if not face["ok"]:
            continue
        s2, m = delete_edges(sig, set(Z))
        r2 = next(r for r in range(len(s2)) if code_from(s2, r) == c2)
        lab, _ = bfs_labels(s2, r2)
        pm = code_dart_map(c2)
        inv = {v: d for d, v in m.items()}
        emb = np.zeros((E, face["E"]))
        for xd in range(len(s2)):
            emb[inv[xd] // 2, pm[lab[xd]] // 2] = 1
        outward = p - cell["x"]
        M = np.linalg.lstsq(B, np.column_stack([outward, emb @ face["B"]]), rcond=None)[0]
        det = np.linalg.det(M)
        if abs(det) < 1e-9:
            raise RuntimeError("degenerate incidence determinant")
        out[c2] = out.get(c2, 0) + int(np.sign(det))
    return out


PRIME = 2147483629


def rank_mod_p(rows):
    piv, r = {}, 0
    for row in rows:
        row = {k: v % PRIME for k, v in row.items() if v % PRIME}
        while row:
            k = min(row)
            if k in piv:
                f = row[k]
                for kk, vv in piv[k].items():
                    nv = (row.get(kk, 0) - f * vv) % PRIME
                    if nv:
                        row[kk] = nv
                    else:
                        row.pop(kk, None)
            else:
                inv = pow(row[k], PRIME - 2, PRIME)
                piv[k] = {kk: vv * inv % PRIME for kk, vv in row.items()}
                r += 1
                break
    return r


def homology(cells, n, log):
    for c, cell in cells.items():
        cell["ok"] = orientation_preserved(c, cell)
    top = max(cell["dim"] for cell in cells.values())
    idx = {d: [c for c, x in cells.items() if x["dim"] == d and x["ok"]] for d in range(top + 1)}
    pos = {d: {c: j for j, c in enumerate(idx[d])} for d in idx}
    rows = {}
    for d in range(1, top + 1):
        rows[d] = []
        for c in idx[d]:
            inc = incidences(c, cells)
            rows[d].append({pos[d - 1][c2]: v for c2, v in inc.items() if c2 in pos[d - 1]})
    ok = True
    for d in range(2, top + 1):                             # d^2 = 0 over Z
        bad = 0
        for row in rows[d]:
            acc = defaultdict(int)
            for j, v in row.items():
                for k, w in rows[d - 1][j].items():
                    acc[k] += v * w
            bad += sum(abs(a) for a in acc.values())
        ok &= bad == 0
        log(f"  d^2 = 0 in degree {d}: {'yes' if bad == 0 else 'NO (' + str(bad) + ')'}")
    rk = {d: rank_mod_p(rows[d]) for d in range(1, top + 1)}
    log("\n  dim   orientable cells   H^BM (rational)")
    betti = []
    for d in range(top + 1):
        b = len(idx[d]) - rk.get(d, 0) - rk.get(d + 1, 0)
        betti.append(b)
        log(f"  {d:3d}   {len(idx[d]):15d}   {b}")
    expected = [0] * top + [1]
    ok &= betti == expected and top == 2 * (n - 3)
    log(f"\n  expected Q in degree {2 * (n - 3)} only: {'OK' if ok else 'MISMATCH'}")
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("n", type=int, help="number of cone points (n = 2g+2 for genus g)")
    ap.add_argument("--homology", action="store_true", help="also compute rational BM homology")
    a = ap.parse_args()
    t0 = time.time()

    def log(s):
        print(s, flush=True)

    log(f"Weierstrass--Delaunay cells for n = {a.n} cone points"
        + (f" (hyperelliptic genus {(a.n - 2) // 2})" if a.n % 2 == 0 else ""))
    cells = enumerate_cells(a.n, log)
    ok = euler(cells, a.n, log)
    if a.homology:
        log("\nRational Borel--Moore homology of the orbit complex")
        ok &= homology(cells, a.n, log)
    log(f"\nfinished in {time.time() - t0:.0f} s")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
