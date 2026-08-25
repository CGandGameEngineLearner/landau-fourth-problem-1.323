# A recursive Buchstab switching improvement for the greatest prime factor of `n^2+1`

This repository contains the manuscript and Lean/checker code for the
`1.323` greatest-prime-factor weak form of Landau's fourth problem.

Public GitHub mirror: <https://github.com/CGandGameEngineLearner/landau-fourth-problem-1.323>

Verification code is MIT-licensed; the manuscript and project prose are
CC BY 4.0. See `LICENSE` and `LICENSE-PAPER.md`.

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
- `lean/`: focused Lean 4 project containing the 22-module dependency closure
  of the recursive `1.323` certificate; unrelated Gaussian/Atkin--Lehner
  research modules are intentionally excluded.
- `scripts/`: exact C++, arbitrary-precision Python, and branch-coverage
  audits.
- `notes/`: analytic-transfer audit, source-version hashes, and publication
  readiness ledger.

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
re-expanding the native computations. The analytic Type-I/II, standard
linear-sieve, Mellin--Perron transfer, and the quoted Buchstab-function lower
bound remain conventional external inputs, as stated in the paper.

The focused project additionally checks finite audit lemmas for the six
analytic-review gates: affine `nu`-interior identities, half-integer strict
threshold separation, an abstract divisor-tuple representation bound,
one-sided common/containing cell geometry and program branch gates, and the
algebraic normalization of `alpha/gamma`, the lower-sieve `t+1` threshold,
`Phi(p/q)`, and `U_LS`. These lemmas make the transfer ledger easier to audit;
they do not prove Grimmelt--Merikoski Corollaries 7.1/7.2, Perron localization
for the actual sifted sums, or the standard dimension-one sieve functions.

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

## External inputs and review boundary

The exact source versions, theorem locations, and SHA-256 hashes of the
external PDFs are recorded in
`notes/SOURCE_LOCK_1_323_2026-08-25.md`. The publication-readiness ledger
lists the six analytic checks that should receive independent review.

The author metadata in the current release is JinWen Li, SouthWest Petroleum
University, `lifesize1@163.com`. Before final public release, add a permanent
archive DOI and update the data/code availability statement.

## AI-assisted development disclosure

The author discloses that GPT-5.6 Sol was used as a reasoning and coding
assistant in developing the core recursive Buchstab switching argument, the
proof-direction and branch ledger, the Lean certificate implementation, the
exact-integer audit scripts, and the manuscript exposition. The author
reviewed the final mathematical statements and takes responsibility for the
submitted content. The model is not an author or an independent verifier;
the cited analytic inputs remain external.
