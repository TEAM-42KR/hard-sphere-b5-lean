# The fifth virial coefficient of hard spheres: Lean 4 formalization of geometric lemmas

This repository contains machine-checked proofs, in Lean 4 with Mathlib, of 96 geometric lemmas used in the
paper *The fifth virial coefficient of hard spheres* by Sungsoo Na and its companion
*The fifth virial coefficient of hard spheres: complete proofs and computations*.
It is a partial formalization: the lemmas below are proved, the main theorem of the paper is not (see
"What is not proved").

## What is proved

`Challenge.lean` states the 96 theorems, each with `sorry`. It imports exactly these modules:

- `Mathlib`
- `HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure`
- `HardSphereB5Lean.Definitions.Def_SolidGeom_ClassicalInputs_SurfaceCalculusInputs`
- `HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5`
- `HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer`
- `HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff`

The five library modules contain the definitions that the statements use and nothing else: they import only
Mathlib and each other, and they contain no `theorem`, `lemma`, `example` or `instance` declaration and no tactic proof (`by`).
So the statements in `Challenge.lean` and `Solution.lean` refer to the same definitions, and no proof is imported
into `Challenge.lean`. `Solution.lean` states the same 96 declarations and proves each of them by the
corresponding theorem of the library `HardSphereB5Lean`.

| Group | Lean namespace | Theorems | In plain words |
|---|---|---:|---|
| Lens and three-ball volumes | `HardSphereB5.Lean.Geometry` | 3 | Two-ball lens volumes for centre separations between 0 and 2; three-ball intersection volumes and positivity of the face quantity `Q` under the stated four-centre configuration hypotheses. |
| Spherical Crofton decomposition | `HardSphereB5.SphericalCrofton` | 27 | Chord and great-circle integrals over regular regions of the unit sphere: the kernel identities, the chord-length integral, the Crofton-type decomposition with its remainder term, and the two statements showing that the literal form of that decomposition fails. |
| Path core | `HardSphereB5.Lean.Geometry.PathCore` | 66 | Four unit balls whose centres form a path configuration: realizability and classification of the configurations, circumcentres and faces, sliver tetrahedra, the near and bulk patches with their areas, moments and volumes, null sets of walls, and the normal form of the volume of the common intersection. |

The full list of the 96 names is `theorem_names` in `config.json` (the names in `Challenge.lean` and
`Solution.lean`); the corresponding library theorems are listed in `Audit.lean` and `Check.lean`.

## What is not proved

- The main theorem of the paper (the value of the fifth virial coefficient of hard spheres in three dimensions)
  is not formalized here.
- The representation of the coefficient by iterated integrals, and the reduction of the coefficient to the
  lemmas above, are not formalized here.
- No numerical value is computed or checked here.

The repository checks the 96 statements above and nothing else.

## What is checked

If `lake build` succeeds, then:

1. every module of `HardSphereB5Lean`, `Challenge.lean`, `Solution.lean` and `Audit.lean` was checked by the
   Lean kernel;
2. `Audit.lean` (part of the default build) prints, for each of the 96 theorems (in `Solution.lean` and in the
   library), the axioms it depends on, and fails
   unless they are among `propext`, `Classical.choice` and `Quot.sound`; it also fails if any constant of the
   `HardSphereB5Lean` modules uses `sorry` directly;
3. the only `sorry` in the repository are the 96 in `Challenge.lean`, one per statement; the build reports
   them as warnings. There is no `native_decide`.

`config.json` is a configuration for Comparator (`leanprover/comparator`), which checks that each
theorem of `Solution.lean` has the same statement as in `Challenge.lean`, with identical definitions behind it, and
that it uses only the permitted axioms. A Comparator run (tag v4.33.0, built with Lean v4.33.1) on the clean
machine described below, on a source archive with the same Lean files as this repository, passed for all 96
theorems: after comparing the statements and checking the axioms it replayed the solution in the Lean kernel and
printed `Lean default kernel accepts the solution` and `Your solution is okay!` (4 min 26 s wall clock; output in
`receipts/comparator.log`).

## Rebuilding

Requirements: elan (the Lean toolchain manager), git, and an internet connection for the Mathlib cache.

From the repository root (the folder of a clone of this repository, or the unpacked release archive):

```
lake exe cache get
lake build
lake env lean Check.lean
```

Expected output: `lake build` ends with `Build completed successfully` (9804 jobs).
Its output includes 96 warnings about `sorry`, all from `Challenge.lean`, and 192 axiom-audit
messages from `Audit.lean` (some span several lines): one for each solution theorem and one for each corresponding
library theorem. Each reports only `propext`, `Classical.choice` and `Quot.sound`, with `sorryAx allowed: false`.
The audit ends with `AUDIT placeholders (0): []`. `Check.lean` prints the types and axiom dependencies of all 96
library theorems.

Measured on a clean machine (AWS r8g.4xlarge, AWS Graviton4; 16 cores, 124 GiB memory, aarch64), using a source archive with the same Lean files and dependency pins as this repository:

- `lake exe cache get`: 42 s wall clock;
- `lake build`: 8 min 22 s wall clock, maximum resident memory of a single process 8.3 GiB;
- disk used by `.lake` after the build: 13.7 GiB.

The logs of that build are in `receipts/` (`build.log`, `build.time`, `check.out`, `build_summary.txt`,
`machine.txt`), with the Comparator output (`comparator.log`, `comparator.time`).

## Versions

- Lean: `leanprover/lean4:v4.33.1` (`lean-toolchain`).
- Mathlib: tag `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`).

## License

MIT (see `LICENSE`).

## Citation

If you use this repository, please cite the paper: Sungsoo Na, *The fifth virial coefficient of hard spheres*,
DOI: to be added on publication.

Assisted by AI.
