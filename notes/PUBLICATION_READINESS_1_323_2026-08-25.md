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
- Zenodo source packager: `scripts/package_zenodo_source.sh`.
- Generated review snapshot:
  `output/landau-1.323-review-bundle.tar.gz` with adjacent SHA-256 file.
- Locked external-source ledger:
  `notes/SOURCE_LOCK_1_323_2026-08-25.md`.
- Submission metadata and cover-letter template:
  `paper/SUBMISSION_PACKAGE_1_323.md`.
- Code license: `LICENSE` (GPL-2.0); paper/prose license: `LICENSE-PAPER.md`
  (CC BY 4.0).

## Internally closed finite checks

1. The recursive Buchstab signs and base-minus-children inequalities are
   checked abstractly in Lean.
2. The `1200 x 300 x 160` outward-rounded certificate gives
   `0.032303187971 > 0.032` in C++, Python, and Lean.
3. The exact endpoint total is
   `8997005488261/9000000000000 < 1`.
4. The endpoint and real-power modules check both the rational strict
   comparison `1323/1000 < 13231/10000` and the finite implication
   `x>2^13230, 0<=n<=2x => n^1.323<x^1.3231`. The preceding analytic block
   estimate remains external.
5. Lean checks the one-sided common/containing box geometry and the algebraic
   normalization of `alpha/gamma`, `t+1`, `Phi`, and `U_LS`; the analytic use
   of these facts remains in gates 4--5 below.
6. Lean checks the affine `nu` ledger, an integer half-threshold fact, and an
   abstract divisor-tuple count.  These do not close source transfer, Perron
   localization, or the prefix-uniform linear sieve in gates 1--3 below.
7. An exhaustive integer branch audit visits all `34,215,168` ordered
   three-prime boxes and `19,635,200` tail child boxes, confirms that every
   analytic branch occurs, and verifies the proof-adverse Buchstab-argument
   gates.

## External expert-review gates

An analytic-number-theory referee should check the following items directly,
not merely the final numerical certificate.

1. **Source transfer.** Verify Corollaries 7.1 and 7.2 of
   Grimmelt--Merikoski with `a=h=1`, against the manuscript's page-specific
   zero-free-region, smooth-family, divisor-bound, and squarefree checks.
2. **Perron localization.** Verify that every ordering and roughness
   condition in the selected Type-II subset is assigned to opposite
   coefficient families, and check the written contour-tail estimate and
   the summed `x^(B+C)/T` truncation budget.
3. **Variable sieve cutoff.** Verify the prefix-uniform Rosser-weight
   proof when the cutoff is the least selected prime, including the common
   local density, normalized smooth seminorms, and the absolute Type-I sum.
4. **One-sided boundary treatment.** Verify that discarded Type-II priority
   cells are used only for lower bounds, while every upper-bound branch uses
   a containing, proof-adverse cell.
5. **Model integrals.** Match every Buchstab and linear-sieve multiplier to
   the normalization in Merikoski's Lemma 7 and equations (2.4)--(2.5).
6. **Endpoint assembly.** Check the explicit `nu=10^-20` integral-loss
   majorants and moving-hyperplane count, then check that the unchanged
   deficiencies, `F6`, and recursive saving enter with the stated signs.

The theorem should remain labelled a complete candidate result until these
six gates receive an independent signed review.

## Six-gate Lean/expert boundary

| Gate | Lean now checks | Still requires an analytic-number-theory expert |
| --- | --- | --- |
| 1. Source/interior transfer | The shifted `nu` definitions, strict interior interval, exponent-ledger identities, `gamma>0.04`, and cutoff order. | The cited Grimmelt--Merikoski corollaries remain external; the manuscript now checks `a=h=1`, the zero-free-region paragraph, uniform dyadic seminorms, divisor bounds, and squarefree support explicitly. |
| 2. Perron localization | Integer strict comparison versus `V-1/2`, the logarithmic separation, and the final polynomial truncation budget. | The manuscript now proves the contour truncation and aggregate error analytically; a referee should verify that proof and the listed variable assignments. |
| 3. Variable sieve cutoff | An abstract triangle-inequality coefficient bound and a fixed divisor-tuple representation bound for at most three prefix slots plus one divisor slot. | The dimension-one fundamental lemma and GM Corollary 7.1 remain external; the manuscript now proves their prefix-family hypotheses, `r_u(d)=r_P(ud)`, and the collected absolute-remainder estimate. |
| 4. One-sided cells | Common-domain and containing-domain endpoints/inclusions, Type-II/subset branch equations, recursive `pairChildUpper` gates, and containing tail-child mesh. | That the cited analytic estimates apply uniformly on those cells and that discarded boundaries/margins pass to the limiting integrals in the required direction. |
| 5. Model normalization | `alpha/gamma`, the `s3` `t+1` threshold, `Phi(p/q)`, outward rounding, and the two algebraic branches of `U_LS`. | Matching the actual sifted sums to Merikoski's Lemma 7 normalization and the analytic origin/validity of the standard linear-sieve `F/f` factors. |
| 6. Endpoint assembly | The `F6` convex ten-panel width certificate, exact core/sign assembly, endpoint fraction, `nu=10^-20`, `10^11 nu <` half margin, and dyadic real-power conversion. | The quoted Buchstab lower bound, published analytic components, and the manuscript's explicit integral majorants and moving-boundary estimate. |

This table is an audit map, not a claim that Lean proves the six analytic
gates or the main greatest-prime-factor theorem.

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
- GitHub release `v1.2.0` is prepared under concept DOI
  `10.5281/zenodo.22140874`;
- record the new version DOI after Zenodo archives the release;
- state the source-code license (`GPL-2.0-only`) and the Lean/Mathlib
  toolchain versions (`leanprover/lean4:v4.22.0`, Mathlib `v4.22.0`);
- obtain an independent analytic review of the six gates above.
