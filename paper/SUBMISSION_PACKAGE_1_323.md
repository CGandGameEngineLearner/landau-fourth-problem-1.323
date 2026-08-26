# Submission package for the `1.323` manuscript

This file is a fill-in template for journal submission and public release.
Bracketed fields require author input.

## Manuscript metadata

**Title**

A recursive Buchstab switching improvement for the greatest prime factor of
`n^2+1`

**Short title**

Recursive Buchstab switching

**2020 MSC**

11N32, 11N35, 11N75

**Keywords**

greatest prime factor; quadratic polynomial; Harman sieve; Buchstab identity;
Landau's fourth problem; computer-assisted proof; Lean

**Article type**

Research article

## Author fields

- Author name: `JinWen Li`
- ORCID: `[OPTIONAL ORCID]`
- Affiliation: `SouthWest Petroleum University`
- Email: `lifesize1@163.com`
- Corresponding author: `[YES/NO]`
- Funding: `[FUNDING STATEMENT OR "No external funding"]`
- Competing interests: `[STATEMENT]`
- Acknowledgements: `[ACKNOWLEDGEMENTS]`

## AI-assisted development disclosure

The author discloses that GPT-5.6 Sol was used as a reasoning and coding
assistant in developing the core recursive Buchstab switching argument, the
proof-direction and branch ledger, the Lean certificate implementation, the
exact-integer audit scripts, and the manuscript exposition. The author
reviewed the final mathematical statements and takes responsibility for the
submitted content. The model is not an author or an independent verifier;
the cited analytic Type-I/II, linear-sieve, and Mellin--Perron transfers
remain external inputs.

## Abstract

Let `P+(m)` denote the greatest prime factor of `m`. Grimmelt and Merikoski
recently proved unconditionally the Type I and Type II ranges that had
previously yielded, under Selberg's eigenvalue conjecture, the exponent
`1.312` for `P+(n^2+1)`. Li subsequently announced the exponent `1.317` by
sharpening the numerical Buchstab integrations. We use the same
unconditional arithmetic input but recursively expose the one-prime tail in
the linear-sieve range `7/6<alpha<5/4`. The resulting three-prime children
are bounded using either the available Type II estimate or a lower
dimension-one linear sieve. An outward-rounded integer certificate,
independently recomputed in Lean, fixed-width C++, and arbitrary-precision
Python, proves that this switching saves at least `0.032303187971` on the
normalized sieve scale. Together with the original published upper bounds
and an independent elementary lower bound for the subtracted one-prime term,
this gives `P+(n^2+1)>n^1.323` for infinitely many positive integers `n`.
The internal block exponent is `1.3231` and the exact final normalized bound
is `8997005488261/9000000000000<1`. Lean 4 verifies the finite Buchstab sign
ledger, integer switching certificate, primitive outward-rounding rules, and
exact rational endpoint budget. The analytic dyadic-to-pointwise passage is
not part of the focused Lean project. This is a quantitative
weak form of Landau's fourth problem: it produces a prime divisor exceeding
`n^1.323` and hence a complementary cofactor smaller than
`n^(0.677+o(1))`, but it does not overcome the sieve parity barrier.

## Significance statement

Landau's fourth problem asks whether `n^2+1` is prime infinitely often.
Iwaniec's theorem reaches primes or semiprimes, but the sieve parity barrier
does not distinguish the two. The present work advances a complementary
quantitative frontier: infinitely often one prime divisor exceeds
`n^1.323`, leaving a cofactor below `n^(0.677+o(1))`. The improvement from
`1.317` comes from a new recursive use of Buchstab's identity in a range
previously treated only by the linear sieve. Every numerical inequality is
certified by three exact-integer implementations, one checked by the Lean
kernel.

## Novelty summary for editors and referees

1. The paper introduces a recursive switching of the formerly discarded
   one-prime tail in `7/6<alpha<5/4`.
2. Non-Type-II three-prime children receive a lower dimension-one
   linear-sieve bound instead of being discarded.
3. Two-prime descendants of the negative tail are bounded by the minimum of
   a universal upper linear sieve, a direct Type-II asymptotic, and a
   recursive base-minus-children bound.
4. The exact saving `0.032303187971` is recomputed independently in C++,
   Python integers, and Lean.
5. The paper states explicit finite Mellin--Perron localization and
   prefix-uniform linear-sieve results, together with a complete
   branch-to-input ledger.
6. An exhaustive audit visits `34,215,168` ordered three-prime boxes and
   `19,635,200` tail child boxes and checks every analytic exponent gate.

## Data and code availability

The review archive contains the TeX source, rendered PDF, locked
Lean toolchain and project, fixed-width C++ certificate, arbitrary-precision
Python audit, exhaustive analytic branch audit, source-version ledger, and
reproduction instructions. Before public release, replace the local review
snapshot by an immutable archive and insert:

- Repository URL: `https://github.com/CGandGameEngineLearner/landau-fourth-problem-1.323`
- Release tag/commit: `[TAG OR COMMIT]`
- Archive DOI: `[ZENODO OR OTHER DOI]`
- Code license: `GPL-2.0-only`
- SHA-256: `[FINAL PUBLIC ARCHIVE SHA-256]`

## Cover letter draft

Dear Editor,

Please consider the manuscript “A recursive Buchstab switching improvement
for the greatest prime factor of `n^2+1`” for publication as a research
article.

Landau's fourth problem asks whether `n^2+1` is prime infinitely often. A
standard quantitative approach is to maximize the greatest prime factor of
these values. Building on the unconditional Type-I/II ranges of Grimmelt and
Merikoski, and on Li's announced exponent `1.317`, the manuscript proves the
new exponent `1.323`. Equivalently, infinitely often `n^2+1` has a prime
factor exceeding `n^1.323`, leaving a complementary cofactor below
`n^(0.677+o(1))`.

The new ingredient is a recursive Buchstab switching in the range formerly
handled by a linear-sieve bound. The analytic argument is separated from an
exact outward-rounded certificate. The certificate is independently
recomputed by fixed-width C++, arbitrary-precision Python, and Lean 4; the
Lean kernel also verifies the finite combinatorial signs, rounding rules, and
endpoint budget. A complete source archive
and reproduction instructions accompany the submission.

The manuscript does not claim a solution of Landau's fourth problem and
states explicitly where the parity barrier remains. It also identifies the
external analytic inputs and the non-formalized review boundary. We believe
the result is a substantive quantitative advance in the sieve-theoretic
program around Landau's problem.

This manuscript is original, is not under consideration elsewhere, and all
authors have approved its submission. `[EDIT IF NECESSARY]`

Sincerely,

`[AUTHOR NAME]`

## Final author actions

1. Verify the author, affiliation, and email fields in the TeX source.
2. Complete the remaining declarations above.
3. Select a journal and conform the TeX style only after preserving the
   theorem numbering and source-version ledger.
4. Obtain an independent analytic-number-theory review of the six gates in
   `notes/PUBLICATION_READINESS_1_323_2026-08-25.md`.
5. Create the permanent public source archive and update the paper's data
   availability statement.
6. Rebuild all certificates, Lean, and both TeX engines from the final
   archive before submission.
