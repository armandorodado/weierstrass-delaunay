#!/usr/bin/env python3
"""Independent verification of every finite statement of

  A. Rodado Amaris, "Circle-pattern linear systems for the twenty trivalent Delaunay
  types of a genus-two surface: rank, feasibility and polytope dimension".

Requires Python 3 with numpy, scipy (>= 1.6) and networkx.  Runs in under a minute and
ends with "ALL CHECKS PASSED"; exits with status 1 if any check fails.

The twenty types are recomputed from scratch as dart systems (rotation systems) of the
triangulations T of the sphere with six vertices, twelve edges and no vertex of degree
one.  The reference labeling of the paper's Table 1 (REF below) is used only to name
edges, after checking that it is an isomorphic copy of the computed type.
"""
import sys, itertools
from fractions import Fraction as Fr
import numpy as np
import networkx as nx
from scipy.optimize import linprog

FAILED = []
def check(name, cond):
    print(("ok    " if cond else "FAIL  ") + name)
    if not cond: FAILED.append(name)

# ---------------------------------------------------------------- maps (dart systems)
# A map is a list sig of length 2E: sig[d] is the next dart around the vertex of d,
# and d^1 is the opposite dart of the same edge.  Faces: d -> sig[d^1].
from fractions import Fraction
def faces(sig):
    m=len(sig); seen=[False]*m; cyc=[]
    for d in range(m):
        if not seen[d]:
            c=[];x=d
            while not seen[x]:
                seen[x]=True;c.append(x);x=sig[x^1]
            cyc.append(c)
    return cyc
def vertices(sig):
    m=len(sig); seen=[False]*m; cyc=[]
    for d in range(m):
        if not seen[d]:
            c=[];x=d
            while not seen[x]:
                seen[x]=True;c.append(x);x=sig[x]
            cyc.append(c)
    return cyc
def code_from(sig,r):
    lab={r:0};order=[r];i=0
    while i<len(order):
        d=order[i];i+=1
        for e in (sig[d],d^1):
            if e not in lab: lab[e]=len(order);order.append(e)
    return tuple((lab[sig[d]],lab[d^1]) for d in order)
def canon(sig):
    codes=[code_from(sig,r) for r in range(len(sig))]
    c=min(codes); return c, codes.count(c)
def from_code(c):
    m=len(c); pairmap={};nxt=0
    for d in range(m):
        if d not in pairmap:
            pairmap[d]=nxt; pairmap[c[d][1]]=nxt+1; nxt+=2
    sig=[0]*m
    for d in range(m): sig[pairmap[d]]=pairmap[c[d][0]]
    return sig
def add_vertex(sig,x):
    m=len(sig); s=sig+[0,0]; a,b=m,m+1
    p=sig.index(x); s[p]=a; s[a]=x; s[b]=b
    return s
def add_edge(sig,x,y):
    m=len(sig); s=sig+[0,0]; a,b=m,m+1
    px=sig.index(x); s[px]=a; s[a]=x
    pyn=[d for d in range(m+2) if s[d]==y and d!=a][0]
    s[pyn]=b; s[b]=y
    return s
def run(n):
    cur={canon([0,1])[0]}
    for k in range(n-2):
        nxt=set()
        for c in cur:
            sig=from_code(c)
            for x in range(len(sig)): nxt.add(canon(add_vertex(sig,x))[0])
        cur=nxt
    allL={}; E=n-1
    cur={c for c in cur if all(len(f)>=3 for f in faces(from_code(c)))}
    allL[E]=cur
    while True:
        nxt=set()
        for c in cur:
            sig=from_code(c)
            for f in faces(sig):
                d=len(f)
                for i in range(d):
                    for k in range(2,d-1):
                        s=add_edge(sig,f[i],f[(i+k)%d]); fs=faces(s)
                        if all(len(ff)>=3 for ff in fs) and len(fs)==len(faces(sig))+1:
                            nxt.add(canon(s)[0])
        if not nxt: break
        E+=1; cur=nxt; allL[E]=cur
    return allL


def tri_types():
    out = []
    for c in run(6)[12]:
        sig = from_code(c); V = vertices(sig)
        vid = {d: i for i, cyc in enumerate(V) for d in cyc}
        deg = [len(cyc) for cyc in V]
        if min(deg) >= 2: out.append((c, sig, vid, deg))
    return out

# ---------------------------------------------------------------- reference labeling
REF = {0: {'sig': (4, 4, 4, 4, 4, 4), 'G': [(1, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 7), (5, 8), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 5), (3, 5), (2, 6), (3, 6), (4, 5), (4, 6), (5, 6)]}, 1: {'sig': (3, 3, 4, 4, 5, 5), 'G': [(1, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 4), (3, 7), (4, 8), (5, 6), (5, 8), (6, 7), (7, 8)], 'T': [(1, 2), (2, 3), (1, 3), (1, 4), (2, 4), (3, 5), (2, 5), (1, 5), (4, 6), (1, 6), (2, 6), (5, 6)]}, 2: {'sig': (2, 3, 4, 4, 5, 6), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 7), (4, 8), (5, 6), (5, 8), (6, 7), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (2, 4), (1, 4), (1, 2), (2, 5), (4, 5), (1, 6), (4, 6), (2, 6), (5, 6)]}, 3: {'sig': (2, 3, 3, 4, 6, 6), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 5), (4, 7), (5, 8), (6, 7), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 2), (4, 5), (1, 5), (2, 5), (1, 6), (2, 6), (5, 6)]}, 4: {'sig': (3, 3, 3, 3, 6, 6), 'G': [(1, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 4), (3, 7), (4, 7), (5, 6), (5, 8), (6, 8), (7, 8)], 'T': [(1, 2), (2, 3), (1, 3), (2, 4), (1, 4), (3, 5), (2, 5), (1, 5), (4, 6), (2, 6), (1, 6), (1, 2)]}, 5: {'sig': (2, 2, 3, 5, 5, 7), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 7), (4, 7), (5, 6), (5, 8), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (2, 4), (1, 4), (1, 2), (2, 5), (4, 5), (1, 6), (4, 6), (2, 6), (2, 4)]}, 6: {'sig': (2, 3, 3, 4, 5, 7), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 5), (4, 6), (4, 7), (5, 8), (6, 7), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (2, 4), (1, 4), (1, 2), (2, 5), (4, 5), (2, 4), (5, 6), (2, 6), (4, 6)]}, 7: {'sig': (2, 2, 5, 5, 5, 5), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 6), (4, 7), (5, 6), (5, 8), (7, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 2), (1, 5), (4, 5), (2, 5), (4, 5), (5, 6), (4, 6)]}, 8: {'sig': (2, 2, 3, 3, 7, 7), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 4), (3, 5), (4, 6), (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 2), (1, 2), (2, 5), (1, 5), (2, 6), (1, 6), (5, 6)]}, 9: {'sig': (2, 2, 2, 4, 6, 8), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 7), (4, 7), (5, 7), (5, 8), (6, 8), (6, 8)], 'T': [(1, 2), (2, 3), (1, 3), (1, 4), (2, 4), (1, 2), (4, 5), (1, 5), (1, 4), (1, 2), (1, 6), (2, 6)]}, 10: {'sig': (2, 2, 2, 6, 6, 6), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 7), (4, 7), (5, 8), (5, 8), (6, 7), (6, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 2), (1, 5), (4, 5), (2, 6), (4, 6), (1, 4), (2, 4)]}, 11: {'sig': (2, 2, 4, 4, 4, 8), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 5), (4, 6), (4, 7), (5, 7), (6, 8), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (2, 4), (1, 4), (1, 2), (2, 5), (4, 5), (2, 4), (2, 6), (5, 6), (2, 5)]}, 12: {'sig': (2, 2, 4, 4, 6, 6), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 5), (4, 6), (4, 7), (5, 6), (6, 8), (7, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (2, 4), (1, 4), (1, 2), (2, 5), (4, 5), (2, 4), (4, 5), (4, 6), (5, 6)]}, 13: {'sig': (2, 3, 3, 3, 4, 9), 'G': [(1, 2), (1, 3), (1, 3), (2, 3), (2, 4), (4, 5), (4, 6), (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 2), (1, 1), (1, 4), (1, 4), (1, 5), (4, 5), (1, 6), (4, 6), (5, 6)]}, 14: {'sig': (2, 2, 2, 2, 8, 8), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 4), (3, 5), (4, 6), (5, 7), (5, 7), (6, 8), (6, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 2), (1, 2), (2, 5), (1, 5), (1, 6), (2, 6), (1, 2)]}, 15: {'sig': (2, 2, 2, 3, 5, 10), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 6), (4, 6), (4, 6), (5, 7), (5, 8), (7, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 2), (1, 1), (1, 2), (1, 4), (2, 4), (1, 5), (1, 5), (5, 6), (1, 6)]}, 16: {'sig': (2, 2, 3, 3, 4, 10), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 5), (4, 5), (4, 6), (6, 7), (6, 8), (7, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (1, 2), (1, 4), (1, 1), (1, 5), (1, 5), (5, 6), (1, 6)]}, 17: {'sig': (2, 2, 3, 4, 5, 8), 'G': [(1, 2), (1, 3), (1, 3), (2, 4), (2, 5), (3, 4), (4, 5), (5, 6), (6, 7), (6, 8), (7, 8), (7, 8)], 'T': [(1, 2), (2, 3), (1, 3), (2, 4), (1, 4), (1, 2), (1, 4), (4, 4), (4, 5), (4, 5), (4, 6), (5, 6)]}, 18: {'sig': (2, 2, 2, 3, 3, 12), 'G': [(1, 2), (1, 3), (1, 3), (2, 3), (2, 4), (4, 5), (4, 5), (5, 6), (6, 7), (6, 8), (7, 8), (7, 8)], 'T': [(1, 2), (2, 3), (1, 3), (1, 2), (1, 1), (1, 4), (1, 4), (1, 1), (1, 5), (1, 5), (5, 6), (1, 6)]}, 19: {'sig': (2, 2, 3, 3, 7, 7), 'G': [(1, 2), (1, 3), (1, 3), (2, 3), (2, 4), (4, 5), (4, 5), (5, 6), (6, 7), (6, 8), (7, 8), (7, 8)], 'T': [(1, 2), (1, 3), (2, 3), (1, 2), (1, 1), (1, 4), (1, 4), (4, 4), (4, 5), (4, 5), (4, 6), (5, 6)]}}

FULL = [0, 1, 2, 4, 6, 7, 12, 13, 17, 19]
SIGS = {k: REF[k]['sig'] for k in REF}

# ---------------------------------------------------------------- exact linear algebra
def rank(M):
    M = [[Fr(x) for x in r] for r in M]; r = 0
    for c in range(len(M[0]) if M else 0):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

def solve(M, b):
    n = len(M); M = [[Fr(x) for x in r] + [Fr(y)] for r, y in zip(M, b)]
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c] / M[c][c]; M[i] = [a - f * y for a, y in zip(M[i], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]

def incidence(T):
    A = [[0] * len(T) for _ in range(6)]
    for j, (a, b) in enumerate(T): A[a - 1][j] += 1; A[b - 1][j] += 1
    return A

def lp_bounds(A, zero=()):
    n = len(A[0]); Aeq = np.array(A, float); beq = np.ones(len(A))
    if zero:
        Aeq = np.vstack([Aeq] + [np.eye(n)[j] for j in zero]); beq = np.concatenate([beq, np.zeros(len(zero))])
    mx, mn = [], []
    for j in range(n):
        c = np.zeros(n); c[j] = -1
        r = linprog(c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n, method='highs')
        if r.status == 2: return None
        mx.append(-r.fun); c[j] = 1
        mn.append(linprog(c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n, method='highs').fun)
    return mx, mn

def dim_and_forced(A, zero=()):
    b = lp_bounds(A, zero)
    if b is None: return None, None, None
    mx, mn = b
    Z = [j for j in range(12) if mx[j] < 1e-9]; O = [j for j in range(12) if mn[j] > 1 - 1e-9]
    rows = [list(r) for r in A] + [[int(i == j) for i in range(12)] for j in set(Z) | set(zero)]
    return 12 - rank(rows), Z, O

def poly_vertices(A):
    out = set()
    for B in itertools.combinations(range(12), 6):
        xb = solve([[A[i][j] for j in B] for i in range(6)], [1] * 6)
        if xb is not None and all(v >= 0 for v in xb):
            x = [Fr(0)] * 12
            for i, j in zip(B, xb): x[i] = j
            out.add(tuple(x))
    return out

def holds(A, coef, const):
    M = [list(r) + [1] for r in A]
    return rank(M + [list(coef) + [const]]) == rank(M)

# ---------------------------------------------------------------- the twenty types
print("Enumerating the trivalent types ...")
TT = tri_types()
check("twenty trivalent types", len(TT) == 20)
types = {}
for c, sig, vid, deg in TT:
    s = tuple(sorted(deg)); loops = [e for e in range(12) if vid[2 * e] == vid[2 * e + 1]]
    cand = [k for k in SIGS if SIGS[k] == s]
    k = (19 if loops else 8) if len(cand) > 1 else cand[0]
    types[k] = dict(code=c, sig=sig, vid=vid, deg=deg)
check("signatures as in Table 1 (two types share (2,2,3,3,7,7))", sorted(types) == list(range(20)))

def gfaces(k):
    F = faces(types[k]['sig']); return {d: i for i, f in enumerate(F) for d in f}

# match the reference labeling: a bijection of G-vertices and of parallel edges sending the
# computed map to Table 1, under which the cone points (faces of G) match too.
COL = {}
for k in range(20):
    fid = gfaces(k); vid = types[k]['vid']
    mine = [(fid[2 * e], fid[2 * e + 1]) for e in range(12)]
    paper = [(a - 1, b - 1) for a, b in REF[k]['G']]
    pm = sorted(tuple(sorted(e)) for e in paper)
    Aref = incidence(REF[k]['T']); found = None
    for perm in itertools.permutations(range(8)):
        if sorted(tuple(sorted((perm[a], perm[b]))) for a, b in mine) != pm: continue
        groups = {}
        for i, (a, b) in enumerate(mine): groups.setdefault(tuple(sorted((perm[a], perm[b]))), []).append(i)
        plab = {}
        for j, (a, b) in enumerate(paper): plab.setdefault(tuple(sorted((a, b))), []).append(j)
        keys = list(groups)
        for ch in itertools.product(*[itertools.permutations(groups[g]) for g in keys]):
            col = {j: i for g, c in zip(keys, ch) for j, i in zip(plab[g], c)}
            # same incidence matrix up to renaming the cone points (rows)
            Ap = [[0] * 12 for _ in range(6)]
            for j in range(12):
                e = col[j]; Ap[vid[2 * e]][j] += 1; Ap[vid[2 * e + 1]][j] += 1
            ok = sorted(map(tuple, Ap)) == sorted(map(tuple, Aref))
            if ok: found = col; break
        if found: break
    COL[k] = found
check("Table 1 is an isomorphic copy of each computed type (G edges and cone points)", all(COL[k] for k in range(20)))
check("types 18 and 19 have the same edge list of G", REF[18]['G'] == REF[19]['G'])
G = {k: nx.MultiGraph(REF[k]['G']) for k in range(20)}
iso_pairs = [(a, b) for a in range(20) for b in range(a + 1, 20) if nx.is_isomorphic(G[a], G[b])]
check("abstract-isomorphic pairs of G are exactly {11,12},{16,17},{18,19}", iso_pairs == [(11, 12), (16, 17), (18, 19)])

A = {k: incidence(REF[k]['T']) for k in range(20)}
check("signature = vertex degrees of T", all(tuple(sorted(sum(r) for r in A[k])) == SIGS[k] for k in range(20)))
LOOPS = {k: [j for j, (a, b) in enumerate(REF[k]['T']) if a == b] for k in range(20)}
check("loops: 13:e5, 15:e5, 16:e8, 17:e8, 18:e5,e8, 19:e5,e8",
      {k: [j + 1 for j in v] for k, v in LOOPS.items() if v} == {13: [5], 15: [5], 16: [8], 17: [8], 18: [5, 8], 19: [5, 8]})
check("every loop is at a cone point of degree >= 7",
      all(sum(A[k][REF[k]['T'][j][0] - 1]) >= 7 for k in range(20) for j in LOOPS[k]))

# ---------------------------------------------------------------- rank and dimensions (Thm 3.2, Table 2)
check("rank A_i = 6 for all twenty types (Theorem 3.2)", all(rank(A[k]) == 6 for k in range(20)))
FORCED = {3: ([1, 6, 8, 9], []), 5: ([1, 4, 5, 6, 12], []), 8: ([1, 6, 7, 8, 9, 10, 11], [12]),
          9: ([1, 4, 5, 6, 8, 9, 10], [7]), 10: ([1, 4, 5, 6, 11, 12], []), 11: ([1, 6, 7, 12], []),
          15: ([1, 4, 5, 6, 9, 10, 12], [11]), 16: ([1, 6, 8, 9, 10, 12], [11]),
          18: ([1, 3, 4, 5, 8, 9, 10, 12], [2, 11])}
DIM = {0: 6, 1: 6, 2: 6, 3: 3, 4: 6, 5: 2, 6: 6, 7: 6, 8: 1, 9: 1, 10: 1, 11: 3, 12: 6, 13: 6, 14: None,
       15: 1, 16: 2, 17: 6, 18: 1, 19: 6}
info = {k: dim_and_forced(A[k]) for k in range(20)}
check("dimensions of Table 2 / Theorem 4.3", all(info[k][0] == DIM[k] for k in range(20)))
check("forced coordinates and values of Table 2",
      all(([j + 1 for j in info[k][1] if j not in info[k][2]], [j + 1 for j in info[k][2]]) == FORCED.get(k, ([], []))
          for k in range(20) if k != 14))
check("type 14 is infeasible", info[14][0] is None)

def vec(d):
    v = [0] * 12
    for j, c in d.items(): v[j - 1] += c
    return v
def comb(k, y):
    return [sum(y[i] * A[k][i][j] for i in range(6)) for j in range(12)], sum(y)
check("type 3: (R1+R2+R5)-(R3+R4+R6) = 2(x1+x6+x8+x9) = 0",
      comb(3, [1, 1, -1, -1, 1, -1]) == (vec({1: 2, 6: 2, 8: 2, 9: 2}), 0))
pt = {1: 0, 6: 0, 8: 0, 9: 0, 2: Fr(1, 2), 3: Fr(1, 2), 7: Fr(1, 2), 12: Fr(1, 2), 4: Fr(1, 4), 5: Fr(1, 4), 10: Fr(1, 4), 11: Fr(1, 4)}
check("type 3: the stated relative-interior point satisfies A x = 1",
      all(sum(A[3][i][j] * pt[j + 1] for j in range(12)) == 1 for i in range(6)))
check("type 14: (R1+R2)-(R3+R4+R5+R6) = 2(x1+x6+x7+x12) = -2",
      comb(14, [1, 1, -1, -1, -1, -1]) == (vec({1: 2, 6: 2, 7: 2, 12: 2}), -2))
check("type 1: (R1+R2+R5+R6)-(R3+R4) = 2(x1+x7+x8+x10+x11+x12) = 2",
      comb(1, [1, 1, -1, -1, 1, 1]) == (vec({1: 2, 7: 2, 8: 2, 10: 2, 11: 2, 12: 2}), 2))
check("type 1: row of cone point 5 is x6+x7+x8+x12", A[1][4] == vec({6: 1, 7: 1, 8: 1, 12: 1}))

# Proposition 6.1
ok_c = ok_b = True
for k in FORCED:
    Z = [j - 1 for j in FORCED[k][0]]; keep = [j for j in range(12) if j not in Z]
    H = nx.MultiGraph(); H.add_nodes_from(range(1, 7))
    for j in keep: H.add_edge(*REF[k]['T'][j])
    degs = [sum(A[k][v][j] for j in keep) for v in range(6)]
    if FORCED[k][1]: ok_b &= (not nx.is_connected(H)) and min(degs) == 1
    else: ok_c &= nx.is_connected(H) and min(degs) >= 2
check("Prop 6.1(b): types with a coordinate forced to 1 have T - Z disconnected with a degree-1 vertex", ok_b)
check("Prop 6.1(c): types 3,5,10,11 have T - Z connected with all degrees >= 2", ok_c)
check("Prop 6.1(c): type 10 gives the six-cycle",
      sorted(tuple(sorted(REF[10]['T'][j])) for j in range(12) if j + 1 not in FORCED[10][0]) and
      all(sum(A[10][v][j] for j in range(12) if j + 1 not in FORCED[10][0]) == 2 for v in range(6)))

# ---------------------------------------------------------------- vertices (Section 7)
print("Enumerating vertices ...")
V = {k: poly_vertices(A[k]) for k in range(20)}
check("every vertex is half-integral (Theorem 7.1)", all(a in (0, Fr(1, 2), 1) for k in V for v in V[k] for a in v))
MH = {0: {(3, 0): 8, (0, 6): 4}, 1: {(3, 0): 7, (0, 6): 2}, 2: {(3, 0): 5, (0, 6): 2}, 3: {(3, 0): 4},
      4: {(3, 0): 6, (0, 6): 2}, 5: {(3, 0): 3}, 6: {(3, 0): 5, (0, 6): 2}, 7: {(3, 0): 4, (0, 6): 4},
      8: {(3, 0): 2}, 9: {(3, 0): 2}, 10: {(3, 0): 2}, 11: {(3, 0): 4}, 12: {(3, 0): 4, (0, 6): 4},
      13: {(3, 0): 4, (1, 4): 1, (0, 6): 2}, 14: {}, 15: {(3, 0): 2}, 16: {(3, 0): 3},
      17: {(3, 0): 3, (1, 4): 2, (0, 6): 4}, 18: {(3, 0): 2}, 19: {(3, 0): 2, (1, 4): 4, (2, 2): 1, (0, 6): 4}}
def mh(k):
    d = {}
    for v in V[k]:
        key = (sum(a == 1 for a in v), sum(a == Fr(1, 2) for a in v)); d[key] = d.get(key, 0) + 1
    return d
check("vertex counts and (m,h)-distributions of Table 3", all(mh(k) == MH[k] for k in range(20)))
def subgraph_count(k):
    ends = REF[k]['T']; cnt = 0
    for S in range(1 << 12):
        H = nx.MultiGraph(); H.add_nodes_from(range(1, 7))
        for e in range(12):
            if S >> e & 1: H.add_edge(*ends[e])
        ok = True
        for C in nx.connected_components(H):
            sub = H.subgraph(C); n, m = len(C), sub.number_of_edges()
            if n == 1: ok = m == 1
            elif n == 2: ok = m == 1
            else: ok = n % 2 == 1 and m == n and all(d == 2 for _, d in sub.degree()) and nx.number_of_selfloops(sub) == 0
            if not ok: break
        cnt += ok
    return cnt
check("Corollary 7.2: subgraph count = number of vertices, all twenty types",
      all(subgraph_count(k) == len(V[k]) for k in range(20)))
def parse(rows):
    return {tuple(Fr(1, 2) if a == 'h' else Fr(int(a)) for a in r.split()) for r in rows}
V0 = parse(["h h h 0 0 0 0 0 0 h h h", "h 0 0 h h 0 h 0 h 0 0 h", "1 0 0 0 0 0 1 0 0 0 1 0", "1 0 0 0 0 0 0 0 1 1 0 0",
            "0 h 0 0 h h h h 0 0 h 0", "0 1 0 0 1 0 0 0 0 0 0 1", "0 1 0 0 0 0 0 1 0 1 0 0", "0 0 h h 0 h 0 h h h 0 0",
            "0 0 1 1 0 0 0 0 0 0 0 1", "0 0 1 0 0 1 0 0 0 0 1 0", "0 0 0 1 0 0 1 1 0 0 0 0", "0 0 0 0 1 1 0 0 1 0 0 0"])
V1 = parse(["1 0 0 0 0 1 0 0 1 0 0 0", "0 h 0 h 0 h h 0 h h 0 0", "0 1 0 1 0 0 0 0 0 0 0 1", "0 1 0 0 0 0 0 1 1 0 0 0",
            "0 0 h 0 h h 0 h h 0 h 0", "0 0 1 0 1 0 0 0 0 0 0 1", "0 0 1 0 0 0 1 0 1 0 0 0", "0 0 0 1 0 1 0 0 0 0 1 0",
            "0 0 0 0 1 1 0 0 0 1 0 0"])
check("Example 7.3: the twelve listed vertices of P_0", V0 == V[0])
check("Example 7.3: their average is 1/4", all(sum(v[j] for v in V0) / 12 == Fr(1, 4) for j in range(12)))
check("Example 7.4: the nine listed vertices of P_1", V1 == V[1])
check("Example 7.4: eight vertices of each on x_e1 = 0",
      sum(v[0] == 0 for v in V[0]) == 8 and sum(v[0] == 0 for v in V[1]) == 8)

# ---------------------------------------------------------------- flips (Section 8)
def pred(s, d): return next(x for x in range(len(s)) if s[x] == d)
def flip(sig, e):
    a, b = 2 * e, 2 * e + 1
    a1 = sig[b]; a2 = sig[a1 ^ 1]; b1 = sig[a]; b2 = sig[b1 ^ 1]
    assert sig[a2 ^ 1] == a and sig[b2 ^ 1] == b
    if e in (a1 // 2, a2 // 2, b1 // 2, b2 // 2): return None
    s = list(sig)
    pa = pred(s, a); s[pa] = s[a]
    pb = pred(s, b); s[pb] = s[b]
    n = s[a1 ^ 1]; s[a1 ^ 1] = a; s[a] = n
    n = s[b1 ^ 1]; s[b1 ^ 1] = b; s[b] = n
    F = faces(s); assert len(F) == 8 and all(len(f) == 3 for f in F) and len(vertices(s)) == 6
    return s
def canon_maps(sig):
    best = min(code_from(sig, r) for r in range(len(sig)))
    out = []
    for r in range(len(sig)):
        if code_from(sig, r) != best: continue
        lab = {r: 0}; order = [r]; i = 0
        while i < len(order):
            d = order[i]; i += 1
            for x in (sig[d], d ^ 1):
                if x not in lab: lab[x] = len(order); order.append(x)
        pm = {}; nxt = 0
        for d in range(len(sig)):
            if d not in pm: pm[d] = nxt; pm[best[d][1]] = nxt + 1; nxt += 2
        out.append({d: pm[lab[d]] for d in range(len(sig))})
    return best, out
code2type = {types[k]['code']: k for k in types}
check("stored maps are canonical", all(from_code(types[k]['code']) == types[k]['sig'] for k in types))
INV = {k: {v: j for j, v in COL[k].items()} for k in range(20)}   # internal edge -> reference label

FL = {}   # FL[k][j] = (admissible, (target type, [arrival reference labels]), facet dim)
for k in range(20):
    sig = types[k]['sig']; d6 = DIM[k] == 6; rows = []
    for j in range(12):
        e = COL[k][j]; s2 = flip(sig, e)
        adm = s2 is not None and min(len(c) for c in vertices(s2)) >= 2
        tgt = None
        if adm:
            c, mp = canon_maps(s2); t = code2type[c]
            tgt = (t, sorted({INV[t][m[2 * e] // 2] for m in mp}))
            assert canon(flip(s2, e))[0] == types[k]['code']
        fd = dim_and_forced(A[k], (j,))[0] if d6 else None
        rows.append((adm, tgt, fd))
    FL[k] = rows
crit = all(FL[k][j][0] == ((sum(A[k][a - 1]) >= 4) if a == b else (sum(A[k][a - 1]) >= 3 and sum(A[k][b - 1]) >= 3))
           for k in range(20) for j, (a, b) in enumerate(REF[k]['T']))
check("admissible <=> endpoints of degree >= 3 (loop: >= 4), all 240 edges", crit)
FT = {0: (12, 12, 12), 1: (10, 12, 10), 2: (7, 10, 7), 4: (10, 12, 10), 6: (7, 10, 7), 7: (8, 8, 8),
      12: (8, 8, 8), 13: (7, 10, 7), 17: (8, 8, 8), 19: (8, 8, 8)}
def frow(k):
    r = FL[k]
    return (sum(x[2] == 5 for x in r), sum(x[0] for x in r), sum(x[0] and x[2] == 5 for x in r))
check("Table 4: facets, admissible edges, overlap", all(frow(k) == FT[k] for k in FULL))
check("Theorem 8.3: every facet is at an admissible edge", all(x[0] for k in FULL for x in FL[k] if x[2] == 5))
check("Theorem 8.3: 13 of 98 admissible edges are not facets, with face dimensions 1..3",
      sum(x[0] for k in FULL for x in FL[k]) == 98 and
      sorted({x[2] for k in FULL for x in FL[k] if x[0] and x[2] != 5}) == [1, 2, 3] and
      sum(x[0] and x[2] != 5 for k in FULL for x in FL[k]) == 13)
check("Example 8.1: F_e6 of P_1 has dimension 3 and e6 is admissible", FL[1][5][0] and FL[1][5][2] == 3)
ARCS = [(k, j) for k in FULL for j in range(12) if FL[k][j][0] and FL[k][j][2] == 5]
check("85 facets", len(ARCS) == 85)
check("Prop 8.6: every facet leads to a full-dimensional type", all(FL[k][j][1][0] in FULL for k, j in ARCS))
check("Theorem 8.4: the arrival face is a facet and flips back to the source",
      all(FL[t][a][2] == 5 and FL[t][a][1][0] == k for k, j in ARCS for t in [FL[k][j][1][0]] for a in FL[k][j][1][1]))
check("Theorem 8.4: deleting e and e' leaves the same incidence system (up to relabeling)",
      all(nx.is_isomorphic(nx.MultiGraph([REF[k]['T'][x] for x in range(12) if x != j]),
                           nx.MultiGraph([REF[t]['T'][x] for x in range(12) if x != FL[k][j][1][1][0]]))
          for k, j in ARCS for t in [FL[k][j][1][0]]))
check("Example 8.5: the flip of the cube at e1 is type 1, arriving at e1", FL[0][0][1] == (1, [0]))
H = nx.MultiGraph([(1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (2, 6), (3, 5), (3, 6), (4, 7), (5, 7), (6, 7)])
def contract(k):
    g = nx.MultiGraph(REF[k]['G']); a, b = REF[k]['G'][0]; g.remove_edge(a, b)
    return nx.contracted_nodes(g, a, b, self_loops=False)
check("Example 8.5: G_0/e1 and G_1/e1 are both H", nx.is_isomorphic(contract(0), H) and nx.is_isomorphic(contract(1), H))
cnt = {}
for k, j in ARCS:
    key = tuple(sorted((k, FL[k][j][1][0]))); cnt[key] = cnt.get(key, 0) + 1
check("Figure 1 edge labels", cnt == {(0, 1): 13, (1, 1): 4, (1, 2): 6, (1, 4): 3, (2, 2): 2, (2, 6): 4, (2, 7): 5,
                                       (4, 6): 10, (6, 12): 6, (6, 13): 2, (7, 12): 6, (12, 17): 3, (13, 13): 4,
                                       (13, 17): 4, (17, 17): 4, (17, 19): 3, (19, 19): 6})

# vertex generation (Theorem 8.9)
def generate(allowed):
    gen = {k: set() for k in range(20)}; gen[0] = set(V[0])
    while True:
        new = {k: set(gen[k]) for k in range(20)}
        for t in allowed:
            for j in range(12):
                adm, tgt, _ = FL[t][j]
                if not adm or tgt[0] not in allowed: continue
                e = COL[t][j]; s2 = flip(types[t]['sig'], e); c, mp = canon_maps(s2); u = code2type[c]
                for x in gen[t]:
                    if x[j] != 0: continue
                    for m in mp:
                        y = [None] * 12
                        for jj in range(12): y[INV[u][m[2 * COL[t][jj]] // 2]] = x[jj]
                        assert tuple(y) in V[u]; new[u].add(tuple(y))
        if new == gen: return gen
        gen = new
for allowed, name in ((FULL, "full-dimensional types"), ([k for k in range(20) if k != 14], "all feasible types")):
    gen = generate(allowed)
    miss = {k: V[k] - gen[k] for k in FULL}
    check(f"Theorem 8.9 ({name}): missing 0 except 13:1, 17:2, 19:5",
          {k: len(m) for k, m in miss.items() if m} == {13: 1, 17: 2, 19: 5})
    check(f"Theorem 8.9 ({name}): missing = vertices with a loop at 1/2",
          all(miss[k] == {v for v in V[k] if any(v[l] == Fr(1, 2) for l in LOOPS[k])} for k in FULL))

# ---------------------------------------------------------------- automorphisms and unfolding (Section 9)
AUT = {k: canon_maps(types[k]['sig'])[1] for k in FULL}
check("|Aut+(T)| = 24,2,1,4,1,4,2,1,1,2", [len(AUT[k]) for k in FULL] == [24, 2, 1, 4, 1, 4, 2, 1, 1, 2])
orb = {}
for k in FULL:
    seen = {}; n = 0
    for j in range(12):
        if j in seen: continue
        for m in AUT[k]: seen[INV[k][m[2 * COL[k][j]] // 2]] = n
        n += 1
    orb[k] = seen
pair = {}; welldef = True
for k in FULL:
    for o in set(orb[k].values()):
        img = set()
        for j in range(12):
            if orb[k][j] != o: continue
            adm, tgt, fd = FL[k][j]
            img.add((tgt[0], orb[tgt[0]][tgt[1][0]]) if adm and fd == 5 else None)
        welldef &= len(img) == 1; pair[(k, o)] = img.pop()
facet_orbits = {k: sum(pair[(k, o)] is not None for o in set(orb[k].values())) for k in FULL}
check("Prop 9.1: orbit map well defined", welldef)
check("Prop 9.1: fixed-point-free involution on facet orbits",
      all(pair[pair[a]] == a and pair[a] != a for a in pair if pair[a] is not None))
check("Prop 9.1: facet orbits 1,6,7,3,7,3,5,7,8,5 (52 in all)",
      [facet_orbits[k] for k in FULL] == [1, 6, 7, 3, 7, 3, 5, 7, 8, 5])

idx = {a: i for i, a in enumerate(ARCS)}
def children(t, arr):
    return [(FL[t][j][1][0], FL[t][j][1][1][0]) for j in range(12) if j != arr and FL[t][j][0] and FL[t][j][2] == 5]
M = np.zeros((85, 85))
for a in ARCS:
    for c in children(*a): M[idx[a], idx[c]] += 1
ev = sorted(np.abs(np.linalg.eigvals(M)), reverse=True)
cur = {}
for c in children(0, None): cur[c] = cur.get(c, 0) + 1
seq = [1]
for d in range(40):
    seq.append(sum(cur.values())); nxt = {}
    for (t, e), m in cur.items():
        for c in children(t, e): nxt[c] = nxt.get(c, 0) + m
    cur = nxt
check("Table 5: 1, 12, 108, 828, 6012, 44292, 322116, 2327988", seq[:8] == [1, 12, 108, 828, 6012, 44292, 322116, 2327988])
check("Table 5: counts divisible by 12", all(x % 12 == 0 for x in seq[1:]))
check("Prop 9.2: spectral radius 7.0928, next 6.0438", abs(ev[0] - 7.0928) < 1e-4 and abs(ev[1] - 6.0438) < 1e-4)
check("Prop 9.2: ratio at depth 40 is 7.0934", abs(seq[40] / seq[39] - 7.0934) < 1e-4)

print()
if FAILED:
    print(f"{len(FAILED)} CHECK(S) FAILED"); sys.exit(1)
print("ALL CHECKS PASSED")
