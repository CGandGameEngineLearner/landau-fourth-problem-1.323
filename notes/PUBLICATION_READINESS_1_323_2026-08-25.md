# Publication-readiness ledger for the `1.323` manuscript

Date: 25 August 2026.

## Claim and scope

The manuscript's claimed theorem is

```text
P+(n^2+1) > n^1.323
```

for infinitely many positive integers `n`.  This is a greatest-prime-factor
weak form of Landau's fourth problem.  It gives a factorization

```text
n^2+1 = p*m,  p > n^1.323,  m < n^(0.677+o(1)),
```

but does not prove infinitely many prime values of `n^2+1`.

## AI-assisted development disclosure

The manuscript and repository explicitly disclose the author's use of
GPT-5.6 Sol as a reasoning and coding assistant for the core recursive
Buchstab switching argument, proof-direction/branch ledger, Lean certificate,
exact-integer audits, and exposition. The author reviewed the final statements
and assumes responsibility for the submission. This does not make the model
an author or independent verifier, and the cited analytic transfers remain
external inputs.

## Authoritative artifacts

- Manuscript: `paper/landau_lpf_1_323.tex`.
- Rendered paper: `output/landau_lpf_1_323.pdf`.
- Analytic transfer audit:
  `notes/HARMAN_RECURSIVE_1_323_ANALYTIC_TRANSFER_AUDIT_2026-08-25.md`.
- Fixed-width certificate: `scripts/certify_harman_recursive_tail.cpp`.
- Arbitrary-precision audit: `scripts/audit_harman_recursive_tail.py`.
- Exhaustive branch audit:
  `scripts/audit_harman_recursive_branch_coverage.py`.
- Lean aggregation:
  `Landau/HarmanRecursiveCertificateCanonical.lean`.
- Review-bundle builder: `scripts/build_1_323_review_bundle.sh`.
- Generated review snapshot:
  `output/landau-1.323-review-bundle.tar.gz` with adjacent SHA-256 file.
- Locked external-source ledger:
  `notes/SOURCE_LOCK_1_323_2026-08-25.md`.
- Submission metadata and cover-letter template:
  `paper/SUBMISSION_PACKAGE_1_323.md`.
- Code license: `LICENSE` (MIT); paper/prose license: `LICENSE-PAPER.md`
  (CC BY 4.0).

## Internally closed gates

1. The recursive Buchstab signs and base-minus-children inequalities are
   checked abstractly in Lean.
2. The `1200 x 300 x 160` outward-rounded certificate gives
   `0.032303187971 > 0.032` in C++, Python, and Lean.
3. The exact endpoint total is
   `8997005488261/9000000000000 < 1`.
4. The endpoint module checks the rational strict comparison
   `1323/1000 < 13231/10000`; the full analytic dyadic-to-pointwise passage
   is not part of the focused Lean project.
5. The manuscript states the Grimmelt--Merikoski Type-I/II ranges with their
   squarefree-support and divisor-bounded coefficient hypotheses.
6. The manuscript now contains a quantitative finite cross-condition
   localization lemma and a prefix-uniform dimension-one linear-sieve
   proposition.
7. An exhaustive integer branch audit visits all `34,215,168` ordered
   three-prime boxes and `19,635,200` tail child boxes, confirms that every
   analytic branch occurs, and verifies the proof-adverse Buchstab-argument
   gates.

## External expert-review gates

An analytic-number-theory referee should check the following items directly,
not merely the final numerical certificate.

1. **Source transfer.** Verify Corollaries 7.1 and 7.2 of
   Grimmelt--Merikoski with `a=h=1`, including uniformity of the implicit
   constants after dyadic subdivision.
2. **Perron localization.** Verify that every ordering and roughness
   condition in the selected Type-II subset is assigned to opposite
   coefficient families as stated, and that the half-integer strict
   threshold removes equality terms without changing divisor bounds.
3. **Variable sieve cutoff.** Verify the prefix-uniform Rosser-weight
   argument when the cutoff is the least selected prime, including the
   dyadic partition and the use of the absolute Type-I remainder sum.
4. **One-sided boundary treatment.** Verify that discarded Type-II priority
   cells are used only for lower bounds, while every upper-bound branch uses
   a containing, proof-adverse cell.
5. **Model integrals.** Match every Buchstab and linear-sieve multiplier to
   the normalization in Merikoski's Lemma 7 and equations (2.4)--(2.5).
6. **Endpoint assembly.** Check that the unchanged published deficiencies,
   the independent `F6` lower bound, and the recursive saving enter with the
   stated signs.

The theorem should remain labelled a complete candidate result until these
six gates receive an independent signed review.

## Reproduction commands

From the project directory:

```text
lake build

g++ -O3 -std=c++20 scripts/certify_harman_recursive_tail.cpp \
  -o /tmp/certify_harman_recursive_tail
/tmp/certify_harman_recursive_tail 1200 300 160

python3 scripts/audit_harman_recursive_tail.py \
  1200 300 160 --workers 16

python3 scripts/audit_harman_recursive_branch_coverage.py

tectonic paper/landau_lpf_1_323.tex --outdir build/pdf

scripts/build_1_323_review_bundle.sh
```

Both external certificates must print

```text
saving_lower=0.032303187971
CERTIFIED=YES
```

and `lake build` must complete the focused `Landau` certificate project and
executable.
The branch audit must print `BRANCH_LEDGER_CERTIFIED=YES`.

## Release metadata still required

Before public circulation or submission:

- verify the author line `JinWen Li`, affiliation, and email;
- add acknowledgements and funding disclosures;
- create a permanent repository release containing the exact source and
  certificate files;
- record its DOI or immutable archive identifier in the paper;
- state the source-code license and the Lean/Mathlib toolchain versions;
- obtain an independent analytic review of the six gates above.
