set_option linter.unusedVariables false

/-!
# Formal verification of the finite linear algebra of Paper 2

A. Rodado Amaris, *Circle-pattern linear systems for the twenty trivalent Delaunay
types of a genus-two surface: rank, feasibility and polytope dimension*.

Checked with Lean 4 (v4.15.0), core library only (no Mathlib):
    lean Paper2CirclePatterns.lean      (about 15 seconds; no output means every theorem checked)

Data.  `ends k` lists, for type `k` (0 ≤ k ≤ 19, numbered as in the paper), the two
cone points (1…6) joined by the edges e₁,…,e₁₂ of the dual triangulation T, in the
reference labeling of the paper's Table 1 (Definition 2.2).  The incidence matrix `A k` (6 × 12, a
loop counting 2) is computed from it, and P_k = {x ∈ ℝ¹² : A_k x = 1, x ≥ 0}.

What is formalized
* `rank_six`             — rank A_k = 6 for all twenty types               (Theorem 3.2)
* `type14_infeasible`    — A₁₄ x = N·1, x ≥ 0 over ℤ forces N = 0, so P₁₄ = ∅;
                           likewise over ℚ after clearing denominators     (Section 5.3)
* `forced_k`             — the forced coordinates of Table 2, for the nine
                           lower-dimensional types, as genuine theorems
                           (any x ≥ 0 with A_k x = N·1 has x_e = 0, resp. N,
                           on the listed edges)                             (Table 2)
* `dim_upper`            — rank of [A_k ; e_F] = 12 − dim, so the forced
                           equalities cut P_k down to dimension ≤ dim       (Proposition 4.2)
* `vertices_in_P`, `dim_lower`
                         — the computed vertices lie in P_k and affinely span
                           dimension dim, so dim P_k = dim exactly          (Theorem 4.3)
* `half_integral_and_vertices`
                         — every basic feasible solution of every type has all
                           coordinates in {0, ½, 1}, and the vertices are
                           exactly `vertexData`                              (Theorem 7.1)
* `vertex_counts`, `mh_distribution`
                         — the vertex counts and (m,h) distributions        (Table 3)
* `facet_table`, `facets_admissible`
                         — numbers of facets, admissible edges and their
                           overlap for the ten full-dimensional types, and
                           facet ⇒ Whitehead-admissible                     (Table 4, Theorem 8.3)

Conventions.  Vertices are stored as 2x ∈ {0,1,2}¹².  A vertex is a basic feasible
solution: six columns with nonzero determinant, solved by Cramer's rule, with all
coordinates in [0,1].  That the basic feasible solutions are exactly the vertices,
and that P_k is their convex hull, are standard facts of polyhedral theory that are
used, not formalized; with them, the dimension of a face is the affine rank of the
vertices on it.  A Whitehead move at e is admissible when it creates no monogon,
i.e. both endpoints of e have degree ≥ 3 in T (a loop: degree ≥ 4); the script
`paper2_verification.py` checks this criterion against the flip itself, for all
240 edges.

Trust: the finite checks use `native_decide`, which trusts the Lean compiler in
addition to the kernel.  The theorems proved by `omega` are checked by the kernel.
-/

/-! ## Data -/

def ends : List (List (Nat × Nat)) := [
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,5), (3,5), (2,6), (3,6), (4,5), (4,6), (5,6)],  -- type 0
  [(1,2), (2,3), (1,3), (1,4), (2,4), (3,5), (2,5), (1,5), (4,6), (1,6), (2,6), (5,6)],  -- type 1
  [(1,2), (1,3), (2,3), (2,4), (1,4), (1,2), (2,5), (4,5), (1,6), (4,6), (2,6), (5,6)],  -- type 2
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,2), (4,5), (1,5), (2,5), (1,6), (2,6), (5,6)],  -- type 3
  [(1,2), (2,3), (1,3), (2,4), (1,4), (3,5), (2,5), (1,5), (4,6), (2,6), (1,6), (1,2)],  -- type 4
  [(1,2), (1,3), (2,3), (2,4), (1,4), (1,2), (2,5), (4,5), (1,6), (4,6), (2,6), (2,4)],  -- type 5
  [(1,2), (1,3), (2,3), (2,4), (1,4), (1,2), (2,5), (4,5), (2,4), (5,6), (2,6), (4,6)],  -- type 6
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,2), (1,5), (4,5), (2,5), (4,5), (5,6), (4,6)],  -- type 7
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,2), (1,2), (2,5), (1,5), (2,6), (1,6), (5,6)],  -- type 8
  [(1,2), (2,3), (1,3), (1,4), (2,4), (1,2), (4,5), (1,5), (1,4), (1,2), (1,6), (2,6)],  -- type 9
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,2), (1,5), (4,5), (2,6), (4,6), (1,4), (2,4)],  -- type 10
  [(1,2), (1,3), (2,3), (2,4), (1,4), (1,2), (2,5), (4,5), (2,4), (2,6), (5,6), (2,5)],  -- type 11
  [(1,2), (1,3), (2,3), (2,4), (1,4), (1,2), (2,5), (4,5), (2,4), (4,5), (4,6), (5,6)],  -- type 12
  [(1,2), (1,3), (2,3), (1,2), (1,1), (1,4), (1,4), (1,5), (4,5), (1,6), (4,6), (5,6)],  -- type 13
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,2), (1,2), (2,5), (1,5), (1,6), (2,6), (1,2)],  -- type 14
  [(1,2), (1,3), (2,3), (1,2), (1,1), (1,2), (1,4), (2,4), (1,5), (1,5), (5,6), (1,6)],  -- type 15
  [(1,2), (1,3), (2,3), (1,4), (2,4), (1,2), (1,4), (1,1), (1,5), (1,5), (5,6), (1,6)],  -- type 16
  [(1,2), (2,3), (1,3), (2,4), (1,4), (1,2), (1,4), (4,4), (4,5), (4,5), (4,6), (5,6)],  -- type 17
  [(1,2), (2,3), (1,3), (1,2), (1,1), (1,4), (1,4), (1,1), (1,5), (1,5), (5,6), (1,6)],  -- type 18
  [(1,2), (1,3), (2,3), (1,2), (1,1), (1,4), (1,4), (4,4), (4,5), (4,5), (4,6), (5,6)]  -- type 19
]

def incidence (es : List (Nat × Nat)) : List (List Int) :=
  (List.range 6).map fun v =>
    es.map fun p => ((if p.1 = v + 1 then 1 else 0) + (if p.2 = v + 1 then 1 else 0) : Int)

def A (k : Nat) : List (List Int) := incidence (ends.getD k [])

/-! ## Exact integer linear algebra -/

/-- One step of fraction-free Gaussian elimination on column `c`. -/
def elimStep (rows : List (List Int)) (c : Nat) : Option (List (List Int)) :=
  match rows.find? (fun r => r.getD c 0 != 0) with
  | none => none
  | some p =>
    let pc := p.getD c 0
    some ((rows.erase p).map fun r =>
      let rc := r.getD c 0
      List.zipWith (fun a b => pc * a - rc * b) r p)

def rankAux : Nat → Nat → List (List Int) → Nat
  | 0, _, _ => 0
  | fuel + 1, c, rows =>
    match elimStep rows c with
    | none => rankAux fuel (c + 1) rows
    | some rest => 1 + rankAux fuel (c + 1) rest

/-- Rank over ℚ of an integer matrix given as a list of rows. -/
def rank (rows : List (List Int)) : Nat := rankAux ((rows.headD []).length) 0 rows

/-- Determinant by fraction-free (Bareiss) elimination. -/
def bareiss : Nat → Int → List (List Int) → Int
  | 0, _, _ => 1
  | fuel + 1, prev, rows =>
    match rows with
    | [] => prev
    | _ =>
      -- find a row with nonzero first entry
      match rows.findIdx? (fun r => r.headD 0 != 0) with
      | none => 0
      | some i =>
        let p := rows.getD i []
        let sgn : Int := if i % 2 = 0 then 1 else -1
        let others := rows.eraseIdx i
        let a := p.headD 0
        let rest := others.map fun r =>
          let c := r.headD 0
          List.zipWith (fun x y => (a * x - c * y) / prev) (r.drop 1) (p.drop 1)
        match rest with
        | [] => sgn * a
        | _ => sgn * bareiss fuel a rest

def det (m : List (List Int)) : Int := bareiss (m.length + 1) 1 m

def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

def bases : List (List Nat) := choose 6 (List.range 12)

def setCol (m : List (List Int)) (i : Nat) (v : List Int) : List (List Int) :=
  (m.zip v).map fun (r, a) => r.set i a

/-- For a basis `B`: (det, Cramer numerators). -/
def cramer (M : List (List Int)) (B : List Nat) : Int × List Int :=
  let MB := M.map fun r => B.map (r.getD · 0)
  let d := det MB
  (d, (List.range 6).map fun i => det (setCol MB i (List.replicate 6 1)))

/-- Is the basic solution of `B` feasible (all coordinates in [0,1])? -/
def feasible (d : Int) (nums : List Int) : Bool :=
  d != 0 && nums.all fun n => if d > 0 then 0 ≤ n && n ≤ d else d ≤ n && n ≤ 0

/-- Are all coordinates of the basic solution in ½ℤ? -/
def halfInt (d : Int) (nums : List Int) : Bool := nums.all fun n => (2 * n) % d == 0

/-- The basic solution, doubled (2x), as a vector of length 12. -/
def doubled (B : List Nat) (d : Int) (nums : List Int) : List Int :=
  (List.range 12).map fun j =>
    match (B.zip nums).find? (·.1 == j) with
    | some (_, n) => (2 * n) / d
    | none => 0

def dedup (l : List (List Int)) : List (List Int) :=
  l.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

def basicFeasible (k : Nat) : List (List Nat × Int × List Int) :=
  (bases.map fun B => let c := cramer (A k) B; (B, c.1, c.2)).filter fun t => feasible t.2.1 t.2.2

/-- The vertices of P_k, doubled. -/
def verts (k : Nat) : List (List Int) :=
  dedup ((basicFeasible k).map fun t => doubled t.1 t.2.1 t.2.2)

/-- The vertices of P_k, doubled (2x), as computed by the independent Python script;
    `half_integral_and_vertices` proves that they are exactly the vertices. -/
def vertexData : List (List (List Int)) := [
  [[1,1,1,0,0,0,0,0,0,1,1,1],[1,0,0,1,1,0,1,0,1,0,0,1],[2,0,0,0,0,0,2,0,0,0,2,0],[2,0,0,0,0,0,0,0,2,2,0,0],[0,1,0,0,1,1,1,1,0,0,1,0],[0,2,0,0,2,0,0,0,0,0,0,2],[0,2,0,0,0,0,0,2,0,2,0,0],[0,0,1,1,0,1,0,1,1,1,0,0],[0,0,2,2,0,0,0,0,0,0,0,2],[0,0,2,0,0,2,0,0,0,0,2,0],[0,0,0,2,0,0,2,2,0,0,0,0],[0,0,0,0,2,2,0,0,2,0,0,0]],  -- type 0
  [[2,0,0,0,0,2,0,0,2,0,0,0],[0,1,0,1,0,1,1,0,1,1,0,0],[0,2,0,2,0,0,0,0,0,0,0,2],[0,2,0,0,0,0,0,2,2,0,0,0],[0,0,1,0,1,1,0,1,1,0,1,0],[0,0,2,0,2,0,0,0,0,0,0,2],[0,0,2,0,0,0,2,0,2,0,0,0],[0,0,0,2,0,2,0,0,0,0,2,0],[0,0,0,0,2,2,0,0,0,2,0,0]],  -- type 1
  [[1,1,1,0,0,0,0,1,0,1,0,1],[0,1,1,0,0,1,0,1,0,1,0,1],[0,2,0,2,0,0,0,0,0,0,0,2],[0,2,0,0,0,0,2,0,0,2,0,0],[0,2,0,0,0,0,0,2,0,0,2,0],[0,0,2,0,2,0,0,0,0,0,0,2],[0,0,2,0,0,0,0,2,2,0,0,0]],  -- type 2
  [[0,2,0,0,2,0,0,0,0,0,0,2],[0,2,0,0,0,0,2,0,0,0,2,0],[0,0,2,2,0,0,0,0,0,0,0,2],[0,0,2,0,0,0,2,0,0,2,0,0]],  -- type 3
  [[2,0,0,0,0,2,0,0,2,0,0,0],[0,1,0,0,1,1,1,0,1,0,1,0],[0,2,0,0,0,0,0,2,2,0,0,0],[0,0,1,1,0,1,0,1,1,1,0,0],[0,0,2,0,0,0,2,0,2,0,0,0],[0,0,0,2,0,2,0,0,0,0,2,0],[0,0,0,0,2,2,0,0,0,2,0,0],[0,0,0,0,0,2,0,0,2,0,0,2]],  -- type 4
  [[0,2,0,0,0,0,2,0,0,2,0,0],[0,2,0,0,0,0,0,2,0,0,2,0],[0,0,2,0,0,0,0,2,2,0,0,0]],  -- type 5
  [[1,1,1,0,0,0,0,1,0,1,0,1],[0,1,1,0,0,1,0,1,0,1,0,1],[0,2,0,2,0,0,0,0,0,2,0,0],[0,2,0,0,0,0,2,0,0,0,0,2],[0,2,0,0,0,0,0,2,0,0,2,0],[0,2,0,0,0,0,0,0,2,2,0,0],[0,0,2,0,2,0,0,0,0,2,0,0]],  -- type 6
  [[1,1,1,0,0,0,0,1,0,0,1,1],[1,1,1,0,0,0,0,0,0,1,1,1],[0,1,1,0,0,1,0,1,0,0,1,1],[0,1,1,0,0,1,0,0,0,1,1,1],[0,2,0,0,2,0,0,0,0,0,2,0],[0,2,0,0,0,0,0,0,2,0,0,2],[0,0,2,2,0,0,0,0,0,0,2,0],[0,0,2,0,0,0,2,0,0,0,0,2]],  -- type 7
  [[0,2,0,0,2,0,0,0,0,0,0,2],[0,0,2,2,0,0,0,0,0,0,0,2]],  -- type 8
  [[0,2,0,0,0,0,2,0,0,0,2,0],[0,0,2,0,0,0,2,0,0,0,0,2]],  -- type 9
  [[0,2,0,0,0,0,0,2,2,0,0,0],[0,0,2,0,0,0,2,0,0,2,0,0]],  -- type 10
  [[0,2,0,2,0,0,0,0,0,0,2,0],[0,2,0,0,0,0,0,2,0,2,0,0],[0,2,0,0,0,0,0,0,2,0,2,0],[0,0,2,0,2,0,0,0,0,0,2,0]],  -- type 11
  [[1,1,1,0,0,0,0,1,0,0,1,1],[1,1,1,0,0,0,0,0,0,1,1,1],[0,1,1,0,0,1,0,1,0,0,1,1],[0,1,1,0,0,1,0,0,0,1,1,1],[0,2,0,2,0,0,0,0,0,0,0,2],[0,2,0,0,0,0,2,0,0,0,2,0],[0,2,0,0,0,0,0,0,2,0,0,2],[0,0,2,0,2,0,0,0,0,0,0,2]],  -- type 12
  [[1,1,1,0,0,0,0,0,1,0,1,1],[0,1,1,1,0,0,0,0,1,0,1,1],[0,0,2,0,1,0,0,0,1,0,1,1],[0,0,2,0,0,2,0,0,0,0,0,2],[0,0,2,0,0,0,2,0,0,0,0,2],[0,0,2,0,0,0,0,2,0,0,2,0],[0,0,2,0,0,0,0,0,2,2,0,0]],  -- type 13
  [],  -- type 14
  [[0,2,0,0,0,0,0,2,0,0,2,0],[0,0,2,0,0,0,2,0,0,0,2,0]],  -- type 15
  [[0,2,0,0,2,0,0,0,0,0,2,0],[0,0,2,2,0,0,0,0,0,0,2,0],[0,0,2,0,0,0,2,0,0,0,2,0]],  -- type 16
  [[1,1,1,0,0,0,0,1,0,0,0,2],[1,1,1,0,0,0,0,0,1,0,1,1],[1,1,1,0,0,0,0,0,0,1,1,1],[0,1,1,0,0,1,0,1,0,0,0,2],[0,1,1,0,0,1,0,0,1,0,1,1],[0,1,1,0,0,1,0,0,0,1,1,1],[0,2,0,0,2,0,0,0,0,0,0,2],[0,2,0,0,0,0,2,0,0,0,0,2],[0,0,2,2,0,0,0,0,0,0,0,2]],  -- type 17
  [[0,2,0,0,0,2,0,0,0,0,2,0],[0,2,0,0,0,0,2,0,0,0,2,0]],  -- type 18
  [[1,1,1,0,0,0,0,1,0,0,0,2],[1,1,1,0,0,0,0,0,1,0,1,1],[1,1,1,0,0,0,0,0,0,1,1,1],[0,1,1,1,0,0,0,1,0,0,0,2],[0,1,1,1,0,0,0,0,1,0,1,1],[0,1,1,1,0,0,0,0,0,1,1,1],[0,0,2,0,1,0,0,1,0,0,0,2],[0,0,2,0,1,0,0,0,1,0,1,1],[0,0,2,0,1,0,0,0,0,1,1,1],[0,0,2,0,0,2,0,0,0,0,0,2],[0,0,2,0,0,0,2,0,0,0,0,2]]  -- type 19
]

def vd (k : Nat) : List (List Int) := vertexData.getD k []

def sameSet (a b : List (List Int)) : Bool :=
  a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)

def affRank (vs : List (List Int)) : Nat :=
  match vs with
  | [] => 0
  | v0 :: rest => rank (rest.map fun v => List.zipWith (· - ·) v v0)

def unitRow (j : Nat) : List Int := (List.range 12).map fun i => if i = j then 1 else 0

def degree (k v : Nat) : Int := ((A k).getD (v - 1) []).foldl (· + ·) 0

def admissible (k e : Nat) : Bool :=
  match (ends.getD k []).getD e (0, 0) with
  | (a, b) => if a = b then decide (degree k a ≥ 4) else decide (degree k a ≥ 3) && decide (degree k b ≥ 3)

def isFacet (k e : Nat) : Bool :=
  let S := (vd k).filter fun v => v.getD e 0 == 0
  affRank S == 5

/-! ## Rank -/

theorem rank_six : (List.range 20).all (fun k => rank (A k) == 6) = true := by native_decide

/-! ## Infeasibility of type 14 and the forced coordinates

Each row equation is written out from `ends`; `rows_match` checks that the
coefficients are exactly the rows of `A k`.  Integer solutions of A x = N·1 are
the rational solutions of A x = 1 scaled by a common denominator N > 0. -/

theorem type14_infeasible (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x4 + x6 + x7 + x9 + x10 + x12 = N)
    (h2 : x1 + x3 + x5 + x6 + x7 + x8 + x11 + x12 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 = N)
    (h5 : x8 + x9 = N)
    (h6 : x10 + x11 = N) :
    N = 0 := by omega

theorem forced_3 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x4 + x6 + x8 + x10 = N)
    (h2 : x1 + x3 + x5 + x6 + x9 + x11 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 + x7 = N)
    (h5 : x7 + x8 + x9 + x12 = N)
    (h6 : x10 + x11 + x12 = N) :
    x1 = 0 ∧ x6 = 0 ∧ x8 = 0 ∧ x9 = 0 := by omega

theorem forced_5 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x5 + x6 + x9 = N)
    (h2 : x1 + x3 + x4 + x6 + x7 + x11 + x12 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 + x8 + x10 + x12 = N)
    (h5 : x7 + x8 = N)
    (h6 : x9 + x10 + x11 = N) :
    x1 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x12 = 0 := by omega

theorem forced_8 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x4 + x6 + x7 + x9 + x11 = N)
    (h2 : x1 + x3 + x5 + x6 + x7 + x8 + x10 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 = N)
    (h5 : x8 + x9 + x12 = N)
    (h6 : x10 + x11 + x12 = N) :
    x1 = 0 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = N := by omega

theorem forced_9 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x3 + x4 + x6 + x8 + x9 + x10 + x11 = N)
    (h2 : x1 + x2 + x5 + x6 + x10 + x12 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 + x7 + x9 = N)
    (h5 : x7 + x8 = N)
    (h6 : x11 + x12 = N) :
    x1 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x7 = N := by omega

theorem forced_10 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x4 + x6 + x7 + x11 = N)
    (h2 : x1 + x3 + x5 + x6 + x9 + x12 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 + x8 + x10 + x11 + x12 = N)
    (h5 : x7 + x8 = N)
    (h6 : x9 + x10 = N) :
    x1 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x11 = 0 ∧ x12 = 0 := by omega

theorem forced_11 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x5 + x6 = N)
    (h2 : x1 + x3 + x4 + x6 + x7 + x9 + x10 + x12 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 + x8 + x9 = N)
    (h5 : x7 + x8 + x11 + x12 = N)
    (h6 : x10 + x11 = N) :
    x1 = 0 ∧ x6 = 0 ∧ x7 = 0 ∧ x12 = 0 := by omega

theorem forced_15 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x4 + 2 * x5 + x6 + x7 + x9 + x10 + x12 = N)
    (h2 : x1 + x3 + x4 + x6 + x8 = N)
    (h3 : x2 + x3 = N)
    (h4 : x7 + x8 = N)
    (h5 : x9 + x10 + x11 = N)
    (h6 : x11 + x12 = N) :
    x1 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x12 = 0 ∧ x11 = N := by omega

theorem forced_16 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x2 + x4 + x6 + x7 + 2 * x8 + x9 + x10 + x12 = N)
    (h2 : x1 + x3 + x5 + x6 = N)
    (h3 : x2 + x3 = N)
    (h4 : x4 + x5 + x7 = N)
    (h5 : x9 + x10 + x11 = N)
    (h6 : x11 + x12 = N) :
    x1 = 0 ∧ x6 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x12 = 0 ∧ x11 = N := by omega

theorem forced_18 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 N : Int)
    (p1 : 0 ≤ x1) (p2 : 0 ≤ x2) (p3 : 0 ≤ x3) (p4 : 0 ≤ x4) (p5 : 0 ≤ x5) (p6 : 0 ≤ x6)
    (p7 : 0 ≤ x7) (p8 : 0 ≤ x8) (p9 : 0 ≤ x9) (p10 : 0 ≤ x10) (p11 : 0 ≤ x11) (p12 : 0 ≤ x12)
    (h1 : x1 + x3 + x4 + 2 * x5 + x6 + x7 + 2 * x8 + x9 + x10 + x12 = N)
    (h2 : x1 + x2 + x4 = N)
    (h3 : x2 + x3 = N)
    (h4 : x6 + x7 = N)
    (h5 : x9 + x10 + x11 = N)
    (h6 : x11 + x12 = N) :
    x1 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x12 = 0 ∧ x2 = N ∧ x11 = N := by omega

theorem rows_match :
    A 14 = [[1,1,0,1,0,1,1,0,1,1,0,1],[1,0,1,0,1,1,1,1,0,0,1,1],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,1,0,0,0],[0,0,0,0,0,0,0,0,0,1,1,0]] ∧
    A 3 = [[1,1,0,1,0,1,0,1,0,1,0,0],[1,0,1,0,1,1,0,0,1,0,1,0],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,1,0,0,0,0,0],[0,0,0,0,0,0,1,1,1,0,0,1],[0,0,0,0,0,0,0,0,0,1,1,1]] ∧
    A 5 = [[1,1,0,0,1,1,0,0,1,0,0,0],[1,0,1,1,0,1,1,0,0,0,1,1],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,0,1,0,1,0,1],[0,0,0,0,0,0,1,1,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,1,0]] ∧
    A 8 = [[1,1,0,1,0,1,1,0,1,0,1,0],[1,0,1,0,1,1,1,1,0,1,0,0],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,1,0,0,1],[0,0,0,0,0,0,0,0,0,1,1,1]] ∧
    A 9 = [[1,0,1,1,0,1,0,1,1,1,1,0],[1,1,0,0,1,1,0,0,0,1,0,1],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,1,0,1,0,0,0],[0,0,0,0,0,0,1,1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,1]] ∧
    A 10 = [[1,1,0,1,0,1,1,0,0,0,1,0],[1,0,1,0,1,1,0,0,1,0,0,1],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,0,1,0,1,1,1],[0,0,0,0,0,0,1,1,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,0,0]] ∧
    A 11 = [[1,1,0,0,1,1,0,0,0,0,0,0],[1,0,1,1,0,1,1,0,1,1,0,1],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,0,1,1,0,0,0],[0,0,0,0,0,0,1,1,0,0,1,1],[0,0,0,0,0,0,0,0,0,1,1,0]] ∧
    A 15 = [[1,1,0,1,2,1,1,0,1,1,0,1],[1,0,1,1,0,1,0,1,0,0,0,0],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,1,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,1,0],[0,0,0,0,0,0,0,0,0,0,1,1]] ∧
    A 16 = [[1,1,0,1,0,1,1,2,1,1,0,1],[1,0,1,0,1,1,0,0,0,0,0,0],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,1,1,0,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,1,0],[0,0,0,0,0,0,0,0,0,0,1,1]] ∧
    A 18 = [[1,0,1,1,2,1,1,2,1,1,0,1],[1,1,0,1,0,0,0,0,0,0,0,0],[0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,1,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,1,0],[0,0,0,0,0,0,0,0,0,0,1,1]] := by native_decide

/-! ## Dimension -/

def forcedSet (k : Nat) : List Nat := match k with
  | 3 => [0, 5, 7, 8]
  | 5 => [0, 3, 4, 5, 11]
  | 8 => [0, 5, 6, 7, 8, 9, 10, 11]
  | 9 => [0, 3, 4, 5, 6, 7, 8, 9]
  | 10 => [0, 3, 4, 5, 10, 11]
  | 11 => [0, 5, 6, 11]
  | 15 => [0, 3, 4, 5, 8, 9, 10, 11]
  | 16 => [0, 5, 7, 8, 9, 10, 11]
  | 18 => [0, 1, 2, 3, 4, 7, 8, 9, 10, 11]
  | _ => []

/-- Upper bound: the forced equalities and A_k x = 1 cut out an affine space of dimension `dim`. -/
theorem dim_upper : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19].map (fun k => 12 - rank (A k ++ (forcedSet k).map unitRow)) = [6, 6, 6, 3, 6, 2, 6, 6, 1, 1, 1, 3, 6, 6, 1, 2, 6, 1, 6] := by native_decide

/-- Every computed vertex lies in P_k: A_k v = 2·1 and 0 ≤ v ≤ 2 (v = 2x). -/
theorem vertices_in_P : (List.range 20).all (fun k => (vd k).all fun v =>
    ((A k).all fun r => (List.zipWith (· * ·) r v).foldl (· + ·) 0 == 2) &&
    v.all fun a => 0 ≤ a && a ≤ 2) = true := by native_decide

/-- Lower bound: the vertices span an affine space of dimension `dim`. -/
theorem dim_lower : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19].map (fun k => affRank (vd k)) = [6, 6, 6, 3, 6, 2, 6, 6, 1, 1, 1, 3, 6, 6, 1, 2, 6, 1, 6] := by native_decide

/-! ## Vertices -/

/-- The main enumeration: every basic feasible solution is half-integral, and the vertices
    are exactly `vertexData`. -/
theorem half_integral_and_vertices : (List.range 20).all (fun k =>
    let bf := basicFeasible k
    bf.all (fun t => halfInt t.2.1 t.2.2) &&
    sameSet (dedup (bf.map fun t => doubled t.1 t.2.1 t.2.2)) (vd k)) = true := by native_decide

theorem vertex_counts : (List.range 20).map (fun k => (vd k).length) = [12, 9, 7, 4, 8, 3, 7, 8, 2, 2, 2, 4, 8, 7, 0, 2, 3, 9, 2, 11] := by native_decide

def mh (k : Nat) : List ((Nat × Nat) × Nat) :=
  let ps := (vd k).map fun v => (v.countP (· == 2), v.countP (· == 1))
  let keys := ps.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []
  let sorted := keys.mergeSort fun p q => p.1 > q.1 || (p.1 == q.1 && p.2 ≥ q.2)
  sorted.map fun p => (p, ps.count p)

theorem mh_distribution : (List.range 20).map mh =
    [[((3, 0), 8), ((0, 6), 4)], [((3, 0), 7), ((0, 6), 2)], [((3, 0), 5), ((0, 6), 2)], [((3, 0), 4)], [((3, 0), 6), ((0, 6), 2)], [((3, 0), 3)], [((3, 0), 5), ((0, 6), 2)], [((3, 0), 4), ((0, 6), 4)], [((3, 0), 2)], [((3, 0), 2)], [((3, 0), 2)], [((3, 0), 4)], [((3, 0), 4), ((0, 6), 4)], [((3, 0), 4), ((1, 4), 1), ((0, 6), 2)], [], [((3, 0), 2)], [((3, 0), 3)], [((3, 0), 3), ((1, 4), 2), ((0, 6), 4)], [((3, 0), 2)], [((3, 0), 2), ((2, 2), 1), ((1, 4), 4), ((0, 6), 4)]] := by native_decide

/-! ## Facets and Whitehead-admissibility -/

def facetRow (k : Nat) : Nat × Nat × Nat :=
  let es := List.range 12
  (es.countP (isFacet k), es.countP (admissible k), es.countP fun e => isFacet k e && admissible k e)

theorem facet_table : [0, 1, 2, 4, 6, 7, 12, 13, 17, 19].map facetRow =
    [(12, 12, 12), (10, 12, 10), (7, 10, 7), (10, 12, 10), (7, 10, 7), (8, 8, 8), (8, 8, 8), (7, 10, 7), (8, 8, 8), (8, 8, 8)] := by native_decide

theorem facets_admissible : [0, 1, 2, 4, 6, 7, 12, 13, 17, 19].all (fun k => (List.range 12).all fun e => !isFacet k e || admissible k e) = true := by native_decide

/-- The admissibility counts for the ten lower-dimensional or infeasible types (Table 5 caption). -/
theorem admissible_counts : (List.range 20).map (fun k => (List.range 12).countP (admissible k)) =
    [12, 12, 10, 10, 12, 8, 10, 8, 8, 6, 6, 8, 8, 10, 4, 6, 8, 8, 6, 8] := by native_decide
