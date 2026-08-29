# A recursive Buchstab switching improvement for the greatest prime factor of `n^2+1`

This repository contains the manuscript and Lean/checker code for the
`1.323` greatest-prime-factor weak form of Landau's fourth problem.

Public GitHub mirror: <https://github.com/CGandGameEngineLearner/landau-fourth-problem-1.323>

Copyright (C) 2026 JinWen Li.

Verification code is licensed under the GNU General Public License
Version 2 (`LICENSE`; SPDX `GPL-2.0-only`). The manuscript and project
prose are CC BY 4.0 (`LICENSE-PAPER.md`).

The main claim studied by the paper is

```text
P+(n^2 + 1) > n^1.323
```

for infinitely many positive integers `n`, subject to the analytic transfer
review described in the paper. Equivalently, infinitely often

```text
n^2 + 1 = p*m,   p > n^1.323,   m < n^(0.677 + o(1)).
```

This is an important quantitative step toward Landau's fourth problem, not a
claim that `n^2+1` is prime infinitely often. The parity barrier remains
explicitly acknowledged.

## Repository layout

- `paper/landau_lpf_1_323.tex`: arXiv-ready manuscript source.
- `output/landau_lpf_1_323.pdf`: rendered manuscript.
- `lean/`: focused Lean 4 project containing the 24-module dependency closure
  of the recursive `1.323` certificate; unrelated Gaussian/Atkin--Lehner
  research modules are intentionally excluded.
- `scripts/`: exact C++, arbitrary-precision Python, and branch-coverage
  audits, plus arXiv and Zenodo packaging scripts.
- `notes/`: analytic-transfer audit, source-version hashes, and publication
  readiness ledger.
- `CITATION.cff`, `.zenodo.json`: citation and Zenodo deposit metadata.

## Reproduce the Lean formalization

Requirements: Lean/Lake with the toolchain in `lean/lean-toolchain` and
network access the first time dependencies are fetched.

```text
cd lean
lake update
lake build
```

The project contains no `sorry`, `admit`, or user-supplied axioms in the
Lean source. The formalization checks the finite Buchstab identities, signs,
recursive node inequalities, rational sieve envelope, primitive integer
rounding specifications, the convex ten-panel midpoint certificate for the
elementary `F6` width integral, the endpoint ledger, and the real-power
implication

```text
x > 2^13230,  0 <= n <= 2*x  ==>  n^1.323 < x^1.3231.
```

The canonical `1200 x 300 x 160` block equalities are evaluated with
`native_decide`; after the block projections, the exact saving sum, division,
rational normalization, and endpoint inequalities are checked without
re-expanding the native computations.  The native compiler is therefore a
trust boundary for the four block values; the C++ and Python implementations
remain independent cross-checks.  Kernel-checked lemmas record the cell sign
as `max(0, 4alpha+A1+A3+T-A0-A2)`, the `1/(12n)` cell width, conservative
clipping, and proof-adverse endpoint directions.  They do not prove that the
integer algorithm equals the analytic `H(alpha)` integral. The cited
Type-I/II and standard linear-sieve theorems, together with the quoted
Buchstab-function lower bound, remain external inputs.  The paper proves the
finite Mellin--Perron localization analytically; Lean does not formalize it.

For audit bookkeeping, the focused project also checks affine `nu`-margin
identities, an explicit rational `nu=10^-20` on the retained range, one-sided
common/containing cell geometry, program branch gates, the algebraic
normalization of `alpha/gamma`, the lower-sieve `t+1` threshold, `Phi(p/q)`,
and `U_LS`, the `s<1` cutoff identity, the exact half-margin split, the
comparison `10^11*nu < half-margin`, and
finite Perron budget arithmetic under stated hypotheses.  Its gate-2/3
additions still do not construct the Perron localization or the
prefix-dependent Rosser coefficients.  None of these lemmas proves
Grimmelt--Merikoski Corollaries 7.1/7.2 or the standard dimension-one sieve
functions.  Their applicability and the collected-prefix calculation are
proved in the manuscript, not in Lean.

## Reproduce the exact certificate

From the repository root:

```text
g++ -O3 -std=c++20 scripts/certify_harman_recursive_tail.cpp \
  -o /tmp/certify_harman_recursive_tail
/tmp/certify_harman_recursive_tail 1200 300 160

python3 scripts/audit_harman_recursive_tail.py \
  1200 300 160 --workers 16

python3 scripts/audit_harman_recursive_branch_coverage.py
```

The two numerical audits must agree on

```text
saving_lower=0.032303187971
CERTIFIED=YES
```

The branch audit must additionally print

```text
BRANCH_LEDGER_CERTIFIED=YES
```

The canonical grid visits `34,215,168` ordered three-prime boxes and
`19,635,200` recursive tail child boxes.

## Build the paper

From the repository root:

```text
tectonic paper/landau_lpf_1_323.tex --outdir build/pdf
```

Alternatively run `pdflatex` twice with `build/pdf` as the output directory.
The source uses an internal bibliography and needs no BibTeX pass.

To package the current clean source snapshot for an external referee, run
`scripts/build_1_323_review_bundle.sh`; the generated archive and checksum
are deliberately ignored by Git because the repository itself is the
versioned source of record.

To create the minimal arXiv source upload, run
`scripts/package_arxiv_source.sh`. It produces
`output/landau_lpf_1_323_arxiv_source.tar.gz`, a tarball containing only the
main `.tex` file; arXiv's source processor will generate the PDF itself.

To create the Zenodo/GitHub-style source zip from a clean commit, run
`scripts/package_zenodo_source.sh`. It writes
`output/landau-fourth-problem-1.323-v1.2.0.zip` from `git archive` and must
not be committed.

## External inputs and review boundary

The exact source versions, theorem locations, and SHA-256 hashes of the
external PDFs are recorded in
`notes/SOURCE_LOCK_1_323_2026-08-25.md`. The publication-readiness ledger
lists the six analytic checks that should receive independent review.

The author metadata in the current release is JinWen Li, SouthWest Petroleum
University, `lifesize1@163.com`.

## Cite this archive

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22140874.svg)](https://doi.org/10.5281/zenodo.22140874)

```text
Li, J. (2026). A recursive Buchstab switching improvement for the
greatest prime factor of n^2+1 (Version 1.2.0).
https://doi.org/10.5281/zenodo.22140874
```

The concept DOI `10.5281/zenodo.22140874` always resolves to the latest
version. The version-specific DOI for `v1.2.0` will be recorded after Zenodo
archives the GitHub Release. GitHub also reads `CITATION.cff`. Verification
code is GPL-2.0-only; the manuscript and notes are CC BY 4.0.

## Deposit on Zenodo

The Git-tracked tree is the public archive. Local Cursor tooling, Lean build
products, third-party PDFs under `tmp/`, unpublished `notes/zhihu_*.md`
files, and generated zip/tar archives are gitignored and must not be
uploaded.

Preferred path (GitHub integration):

1. Sign in at <https://zenodo.org> with the GitHub account that owns
   `CGandGameEngineLearner/landau-fourth-problem-1.323`.
2. Open **GitHub** in the Zenodo drop-down, enable this repository, and
   save. Zenodo will then archive every new GitHub Release.
3. Tag a new version and create a GitHub Release. Zenodo archives that
   snapshot and mints a new version DOI under the concept DOI
   `10.5281/zenodo.22140874`.
4. Record the new version DOI in `CITATION.cff`, this README, and the
   paper's supplementary-material remark.

Manual upload, if GitHub integration is unavailable: from a clean checkout
of the same tag run `scripts/package_zenodo_source.sh`, or the equivalent

```text
git archive --format=zip --prefix=landau-fourth-problem-1.323-v1.2.0/ \
  -o output/landau-fourth-problem-1.323-v1.2.0.zip HEAD
```

Upload that zip. Do not zip a dirty working copy. Paste the metadata from
`.zenodo.json`; the record license ID must be the Zenodo vocabulary value
`gpl-2.0-only`. The manuscript remains CC BY 4.0 as stated in
`LICENSE-PAPER.md`.

## AI-assisted development disclosure

The author discloses that GPT-5.6 Sol was used as a reasoning and coding
assistant in developing the core recursive Buchstab switching argument, the
proof-direction and branch ledger, the Lean certificate implementation, the
exact-integer audit scripts, and the manuscript exposition. The author
reviewed the final mathematical statements and takes responsibility for the
submitted content. The model is not an author or an independent verifier;
the cited analytic inputs remain external.
