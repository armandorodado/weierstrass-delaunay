/-!
# Formal verification of the finite combinatorics of Paper 1

A. Rodado Amaris, *Delaunay Combinatorics of the Moduli and Teichmüller Space of
Closed Genus-Two Riemann Surfaces*, Sections 2–4 and Remark 4.6.

Checked with Lean 4 (v4.15.0), core library only (no Mathlib):
    lean Paper1Combinatorics.lean      (about 25 seconds)

What is formalized
* `ce_graph_counts`      — Euler count for CE-graphs: v = 8, e = 12          (§2.2)
* `riemann_hurwitz_g2`   — six branch points                               (§2.1)
* `degree_balance`       — Lemma "Degree bound and balance": x₅ = x₃         (Lemma 3.2)
* `level_invariant`      — face count is constant along the hierarchy      (Lemma 8.5)
* `pentagon_lemma`       — non-crossing diagonals of a pentagon share a vertex (Lemma 3.3)
* `classification`       — every simplicial triangulation of S² on six vertices is
                           isomorphic to the octahedron or the stacked one, and these
                           two are distinct                                (Props 3.4–3.5, Thm 3.6)
* `aut_octa`, `aut_stacked`, `autPlus_octa`, `autPlus_stacked`
                         — |Aut| = 48, 4 and |Aut⁺| = 24, 2                 (Prop 3.7)
* `octa_flips`, `stacked_flips`, `stacked_selfflip_orbit`
                         — the generic Whitehead-move orbit                (Props 4.3–4.4, Thm 4.5)

Encoding of "simplicial triangulation of S² with six vertices".  A set `T` of
3-element subsets of {0,…,5} (triangles) such that
  (i)   |T| = 8,
  (ii)  every 2-element subset lies in 0 or 2 triangles of `T`,
  (iii) the link of every vertex is non-empty and connected,
  (iv)  `T` is connected.
(ii)–(iv) make `T` a closed connected combinatorial surface (every link is a single
cycle, since by (ii) each link vertex has degree 2).  It has 6 vertices,
3·8/2 = 12 edges and 8 faces, so χ = 2 and the surface is S².  Conversely every
simplicial triangulation of S² on six vertices has 8 faces (Euler) and satisfies
(ii)–(iv).  Triangles are sets, so the triangulation is automatically simple, which
is the genericity condition of the paper.

Trust: the finite checks use `native_decide`, which trusts the Lean compiler in
addition to the kernel.
-/

/-! ## Arithmetic lemmas -/

/-- A CE-graph: trivalent (3v = 2e), six faces, Euler characteristic 2. -/
theorem ce_graph_counts (v e : Nat) (h1 : 3 * v = 2 * e) (h2 : v + 6 = e + 2) :
    v = 8 ∧ e = 12 := by omega

/-- Riemann–Hurwitz for a degree-2 map from genus 2 to genus 0. -/
theorem riemann_hurwitz_g2 (b : Int) (h : 2 * 2 - 2 = 2 * (2 * 0 - 2) + b) : b = 6 := by
  omega

/-- Lemma (degree bound and balance): six vertices of degree 3, 4 or 5 and degree sum 24. -/
theorem degree_balance (x3 x4 x5 : Nat) (h1 : x3 + x4 + x5 = 6)
    (h2 : 3 * x3 + 4 * x4 + 5 * x5 = 24) : x5 = x3 := by omega

/-- Lemma (level invariant): after k contractions, V = 8 - k, E = 12 - k force F = 6. -/
theorem level_invariant (k : Nat) (_hk : k ≤ 6) (F : Int)
    (h : ((8 : Int) - k) - (12 - k) + F = 2) : F = 6 := by omega

/-! ## The pentagon lemma -/

/-- `a`, `b` are consecutive vertices of the pentagon 0-1-2-3-4. -/
def adj5 (a b : Fin 5) : Bool := (a.val + 1) % 5 == b.val || (b.val + 1) % 5 == a.val

/-- `ab` is a diagonal. -/
def isDiag (a b : Fin 5) : Bool := a != b && !adj5 a b

/-- `x` lies strictly inside the boundary arc from `a` to `b` (counter-clockwise). -/
def strictlyBetween (a b x : Fin 5) : Bool :=
  let d := (b.val + 5 - a.val) % 5
  let dx := (x.val + 5 - a.val) % 5
  0 < dx && dx < d

/-- Two chords of a convex pentagon with four distinct endpoints cross iff the
endpoints interleave. -/
def crosses (a b c d : Fin 5) : Bool :=
  a != c && a != d && b != c && b != d && (strictlyBetween a b c != strictlyBetween a b d)

/-- Lemma (pentagon lemma, key step): two non-crossing diagonals of a pentagon share an
endpoint.  A triangulation of a pentagon uses two non-crossing diagonals, so it is a
fan from their common endpoint. -/
theorem pentagon_lemma : ∀ a b c d : Fin 5, isDiag a b = true → isDiag c d = true →
    crosses a b c d = false → (a = c ∨ a = d ∨ b = c ∨ b = d) := by decide

/-! ## Finite machinery: subsets of {0,…,5} as bitmasks -/

/-- Number of set bits among the first `w` bits. -/
def pc (w m : Nat) : Nat := ((List.range w).filter (fun i => m.testBit i)).length

/-- The 20 triangles (3-subsets of {0,…,5}). -/
def tris : List Nat := (List.range 64).filter (fun m => pc 6 m == 3)

/-- The 15 edges (2-subsets of {0,…,5}). -/
def edges : List Nat := (List.range 64).filter (fun m => pc 6 m == 2)

/-- The triangle set encoded by a 20-bit mask. -/
def triList (m : Nat) : List Nat :=
  (List.range 20).filterMap (fun i => if m.testBit i then tris[i]? else none)

/-- Number of triangles of `T` containing the edge `e`. -/
def cnt (T : List Nat) (e : Nat) : Nat := (T.filter (fun t => t &&& e == e)).length

def edgeOK (T : List Nat) : Bool := edges.all (fun e => cnt T e == 0 || cnt T e == 2)

def iter : Nat → (Nat → Nat) → Nat → Nat
  | 0, _, x => x
  | k + 1, f, x => iter k f (f x)

/-- One closure step: add every set of `L` meeting the current vertex set. -/
def closeStep (L : List Nat) (r : Nat) : Nat :=
  L.foldl (fun acc e => if acc &&& e != 0 then acc ||| e else acc) r

/-- The family `L` of vertex sets is non-empty and connected. -/
def connectedFamily (L : List Nat) : Bool :=
  match L with
  | [] => false
  | e :: _ => iter 8 (closeStep L) e == L.foldl (· ||| ·) 0

/-- Link of vertex `v`: the edges opposite `v` in the triangles through `v`. -/
def link (T : List Nat) (v : Nat) : List Nat :=
  (T.filter (fun t => t &&& (1 <<< v) != 0)).map (fun t => t ^^^ (1 <<< v))

/-- `T` is a simplicial triangulation of S² on the six vertices {0,…,5}. -/
def isSphere (T : List Nat) : Bool :=
  T.length == 8 && edgeOK T && (List.range 6).all (fun v => connectedFamily (link T v)) &&
    connectedFamily T

/-- All permutations of a list (fuel = length). -/
def permsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, l =>
      if l.isEmpty then [[]]
      else (l.map (fun x => (permsAux n (l.erase x)).map (x :: ·))).foldr (· ++ ·) []

def perms6 : List (List Nat) := permsAux 6 (List.range 6)

/-- Image of a vertex set under the permutation `p` (as a list `i ↦ p[i]`). -/
def mapMask (p : List Nat) (t : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => if t.testBit i then acc ||| (1 <<< p.getD i 0) else acc) 0

def setEq (A B : List Nat) : Bool := A.length == B.length && A.all (fun a => B.contains a)

/-- `T` and `T'` are isomorphic simplicial complexes. -/
def isoTo (T T' : List Nat) : Bool := perms6.any (fun p => setEq (T.map (mapMask p)) T')

def toMask (l : List Nat) : Nat := l.foldl (fun acc i => acc ||| (1 <<< i)) 0

/-- Oriented triangles of the octahedron (antipodal pairs {0,1}, {2,3}, {4,5}). -/
def octaO : List (List Nat) :=
  [[0,2,4],[0,5,2],[0,4,3],[0,3,5],[1,4,2],[1,2,5],[1,3,4],[1,5,3]]

/-- Oriented triangles of the stacked triangulation: the octahedron flipped at {0,2}. -/
def stackedO : List (List Nat) :=
  [[0,4,3],[0,3,5],[1,4,2],[1,2,5],[1,3,4],[1,5,3],[0,5,4],[2,4,5]]

def octa : List Nat := octaO.map toMask
def stacked : List Nat := stackedO.map toMask

/-! ## Classification (Propositions 3.4–3.5, Theorem 3.6) -/

theorem octa_isSphere : isSphere octa = true := by native_decide
theorem stacked_isSphere : isSphere stacked = true := by native_decide
theorem octa_ne_stacked : isoTo octa stacked = false := by native_decide

def classificationCheck : Bool :=
  (List.range (2 ^ 20)).all (fun m =>
    !(pc 20 m == 8) || !isSphere (triList m) || isoTo (triList m) octa ||
      isoTo (triList m) stacked)

theorem classificationCheck_ok : classificationCheck = true := by native_decide

/-- Every encoded set of triangles is a sub-list of the 20 triangles; `triList` ranges over
all of them as `m` ranges over 20-bit masks.  Main theorem: every simplicial triangulation
of S² on six vertices is isomorphic to the octahedron or to the stacked triangulation. -/
theorem classification (m : Nat) (hm : m < 2 ^ 20) (h8 : pc 20 m = 8)
    (hs : isSphere (triList m) = true) :
    isoTo (triList m) octa = true ∨ isoTo (triList m) stacked = true := by
  have h := classificationCheck_ok
  unfold classificationCheck at h
  rw [List.all_eq_true] at h
  have hm' := h m (List.mem_range.mpr hm)
  simp [h8, hs] at hm'
  exact hm'

/-! ## Automorphism groups (Proposition 3.7) -/

def autCount (T : List Nat) : Nat := (perms6.filter (fun p => setEq (T.map (mapMask p)) T)).length

/-- The three cyclic rotations of an oriented triangle. -/
def rotations (t : List Nat) : List (List Nat) :=
  match t with
  | [a, b, c] => [[a, b, c], [b, c, a], [c, a, b]]
  | _ => []

/-- Coherent orientation: every directed edge occurs exactly once, with its reverse. -/
def coherent (O : List (List Nat)) : Bool :=
  let de := O.foldr (fun t acc => match t with
    | [a, b, c] => [(a, b), (b, c), (c, a)] ++ acc
    | _ => acc) []
  de.length == 24 && de.all (fun (a, b) => (de.filter (· == (a, b))).length == 1 &&
    de.contains (b, a))

def autPlusCount (O : List (List Nat)) : Nat :=
  let rots := O.foldr (fun t acc => rotations t ++ acc) []
  (perms6.filter (fun p => O.all (fun t => rots.contains (t.map (fun i => p.getD i 0))))).length

theorem octa_coherent : coherent octaO = true := by native_decide
theorem stacked_coherent : coherent stackedO = true := by native_decide
theorem aut_octa : autCount octa = 48 := by native_decide
theorem aut_stacked : autCount stacked = 4 := by native_decide
theorem autPlus_octa : autPlusCount octaO = 24 := by native_decide
theorem autPlus_stacked : autPlusCount stackedO = 2 := by native_decide

/-! ## Diagonal flips and the generic orbit (Propositions 4.3–4.4, Theorem 4.5) -/

/-- Result of flipping edge `e`: `none` if inadmissible (the new diagonal is already an
edge, Lemma 4.2), otherwise `some 0` (octahedron), `some 1` (stacked), `some 2` (other). -/
def flipClass (T : List Nat) (e : Nat) : Option Nat :=
  match T.filter (fun t => t &&& e == e) with
  | [t1, t2] =>
      let cd := (t1 ^^^ e) ||| (t2 ^^^ e)
      if cnt T cd != 0 then none
      else
        let u := e &&& (e - 1)
        let w := e ^^^ u
        let T' := (T.filter (fun t => t != t1 && t != t2)) ++ [cd ||| u, cd ||| w]
        if isoTo T' octa then some 0 else if isoTo T' stacked then some 1 else some 2
  | _ => none

def edgesOf (T : List Nat) : List Nat := edges.filter (fun e => cnt T e == 2)

def countRes (T : List Nat) (r : Option Nat) : Nat :=
  ((edgesOf T).filter (fun e => flipClass T e == r)).length

/-- Proposition 4.3: all twelve edges of the octahedron flip, each to the stacked type. -/
theorem octa_flips :
    (edgesOf octa).length = 12 ∧ countRes octa (some 1) = 12 := by native_decide

/-- Proposition 4.4: of the stacked triangulation's twelve edges, exactly one flips to the
octahedron, four to the stacked type, and seven are inadmissible. -/
theorem stacked_flips :
    (edgesOf stacked).length = 12 ∧ countRes stacked (some 0) = 1 ∧
      countRes stacked (some 1) = 4 ∧ countRes stacked none = 7 ∧
      countRes stacked (some 2) = 0 := by native_decide

/-- The four self-transition edges form a single orbit under Aut(stacked). -/
theorem stacked_selfflip_orbit :
    let S := (edgesOf stacked).filter (fun e => flipClass stacked e == some 1)
    let A := perms6.filter (fun p => setEq (stacked.map (mapMask p)) stacked)
    S.all (fun e => S.all (fun e' => A.any (fun p => mapMask p e == e'))) = true := by
  native_decide

/-! ## Non-vacuity: the encoding finds exactly the expected labelled triangulations -/

/-- There are exactly 195 labelled simplicial triangulations of S² on {0,…,5}:
6!/48 = 15 octahedra and 6!/4 = 180 stacked ones. -/
theorem labelled_sphere_count :
    ((List.range (2 ^ 20)).filter (fun m => pc 20 m == 8 && isSphere (triList m))).length = 195 := by
  native_decide
