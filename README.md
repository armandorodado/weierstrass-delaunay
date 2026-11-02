# weierstrass-delaunay

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23870957.svg)](https://doi.org/10.5281/zenodo.23870957)

Code and formal proofs for the **Weierstrass–Delaunay cell decomposition** of the
moduli space of genus-two Riemann surfaces and of the hyperelliptic locus in every
genus.

A hyperelliptic Riemann surface *X* of genus *g* is a double cover of the sphere,
branched at its 2*g*+2 Weierstrass points. The quotient is a hyperbolic sphere with
2*g*+2 cone points of angle π, and the Delaunay decomposition of those cone points
is canonical: it involves no choices and no extra marked points. Grouping surfaces
by the combinatorial type of this decomposition gives a mapping-class-group
invariant cell decomposition of the moduli space. This repository contains the
code that classifies the types, decides which of them occur, formally verifies
the finite combinatorics, and checks the resulting cell complex against known
invariants of the moduli space.

The code accompanies a series of papers by A. Rodado Amaris, building on the
author's PhD thesis (University of Melbourne, 2007).

## Contents

| Folder | Paper | What it checks |
|---|---|---|
| [`paper1-genus2-combinatorics/`](paper1-genus2-combinatorics/) | *Delaunay Combinatorics of the Moduli and Teichmüller Space of Closed Genus-Two Riemann Surfaces* | Lean 4 formalization of the classification, automorphism groups and flip orbit; all enumerations of the paper |
| [`paper5-hyperelliptic-genus-g/`](paper5-hyperelliptic-genus-g/) | *Face-Constraint Independence, a Hall Criterion, and the Combinatorial Immersion C<sub>g−1</sub> → C<sub>g</sub> for Hyperelliptic Surfaces of Arbitrary Genus* | Euler characteristic and rational homology of the cell decomposition of the hyperelliptic locus, genus 2 and 3 |

## Requirements

- Python 3.9 or later, with `numpy`, `scipy` (1.6 or later, for the HiGHS LP solver) and `networkx`:

  ```bash
  pip install -r requirements.txt
  ```

- For the formal proofs: [Lean 4](https://lean-lang.org), version 4.15.0 (core library only, no Mathlib).
  With [elan](https://github.com/leanprover/elan) installed, the `lean-toolchain` file selects the right version automatically.

## Paper 1: genus two

```bash
cd paper1-genus2-combinatorics
lean Paper1Combinatorics.lean        # about 25 s; no output means every theorem checked
python3 paper1_verification.py       # about 15 s; ends with "ALL CHECKS PASSED"
```

**`Paper1Combinatorics.lean`** (Remark 4.6 of the paper) proves:

- every simplicial triangulation of the sphere on six vertices is isomorphic to the
  octahedron or to the stacked triangulation, and there are exactly
  195 = 6!/48 + 6!/4 labelled ones (Theorem 3.6);
- the automorphism groups have orders 48 and 4, and 24 and 2 when restricted to
  orientation-preserving automorphisms (Proposition 3.7);
- the Whitehead-move (flip) orbit: all 12 flips of the octahedron give the stacked
  type; of the stacked type's 12 edges, 1 flips back, 4 flip to itself (one orbit)
  and 7 are inadmissible (Propositions 4.3–4.4, Theorem 4.5);
- the pentagon lemma and the Euler-count arithmetic (Lemmas 3.2, 3.3, 8.5).

The finite checks use `native_decide`, so they trust the Lean compiler as well as
the kernel.

**`paper1_verification.py`** (Remark 8.12) recomputes, on the dual-triangulation
side and independently of the paper's own programs:

| Check | Value |
|---|---|
| six-vertex sphere maps without degree-one vertices, by number of edges 12…6 | 20, 55, 97, 71, 31, 5, 1 (280 in total) |
| trivalent types; distinct abstract graphs | 20; 17 |
| contraction hierarchy from the two generic types | 2, 6, 22, 32, 22, 5, 1 (90 in total) |
| closure from Θ₆ by expansion only | 128 types; 66 of the 90 reached |
| closure by expansion and contraction | all 280 |
| realizable types: trivalent; all; per hierarchy level | 10; 116; 2, 5, 13, 12, 6, 2, 1 |
| explicit stacked configuration (Prop. 7.3, §7.4, Lemma 7.5) | cone angles, Delaunay criterion, perfect matching, symmetry |

## Paper 5: the hyperelliptic locus in genus *g*

```bash
cd paper5-hyperelliptic-genus-g
python3 weierstrass_delaunay_check.py 6 --homology    # genus 2: a few seconds
python3 weierstrass_delaunay_check.py 8 --homology    # genus 3: about 50 minutes
```

The argument is the number of cone points, *n* = 2*g* + 2. The script enumerates
all realizable Delaunay cells of the moduli space of the sphere with *n* cone points
modulo permutations, with their dimensions, automorphism groups and faces, and
checks two invariants:

- the **orbifold Euler characteristic**, against χ(M<sub>0,n</sub>)/n!, and its half
  for the hyperelliptic locus;
- the **rational Borel–Moore homology** of the cell complex, which must be ℚ in the
  top degree only, because the hyperelliptic locus is rationally acyclic.

| | genus 2 (*n* = 6) | genus 3 (*n* = 8) |
|---|---|---|
| realizable cells | 116 | 45,871 |
| orbifold Euler characteristic of the hyperelliptic locus | −1/240 = ζ(−3)/(−2) | −1/672 |
| rational cohomology | ℚ in degree 0 | ℚ in degree 0 |

The complete genus-3 output is in [`output_genus3.txt`](paper5-hyperelliptic-genus-g/output_genus3.txt).
The script exits with a non-zero status if any check fails.

## Citing

If you use this code, please cite the corresponding paper:

```bibtex
@article{RodadoAmaris-genus2,
  author  = {Rodado Amaris, Armando},
  title   = {Delaunay Combinatorics of the Moduli and {T}eichm{\"u}ller Space
             of Closed Genus-Two {R}iemann Surfaces},
  journal = {arXiv preprint arXiv:XXXX.XXXXX},
  year    = {2026}
}
```

the software itself (this DOI always resolves to the latest version):

```bibtex
@software{RodadoAmaris-weierstrass-delaunay,
  author    = {Rodado Amaris, Armando},
  title     = {weierstrass-delaunay: code and formal proofs for the
               {W}eierstrass--{D}elaunay cell decomposition of genus-two and
               hyperelliptic moduli spaces},
  publisher = {Zenodo},
  year      = {2026},
  doi       = {10.5281/zenodo.23870957},
  url       = {https://github.com/armandorodado/weierstrass-delaunay}
}
```

and, for the original framework,

```bibtex
@phdthesis{RodadoAmaris2007,
  author = {Rodado Amaris, Armando J.},
  title  = {Weierstrass Points and Canonical Cell Decompositions of the Moduli
            and {T}eichm{\"u}ller Spaces of {R}iemann Surfaces of Genus Two},
  school = {University of Melbourne},
  year   = {2007},
  url    = {https://minerva-access.unimelb.edu.au/items/db3ae682-386e-51d5-87cb-d755f4d0cb96}
}
```

## Licence

The code is released under the MIT licence; see [`LICENSE`](LICENSE).

## Contact

Armando Rodado Amaris — armando@rodadolab.com
