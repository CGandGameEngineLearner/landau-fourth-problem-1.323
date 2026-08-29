# Paper build

The research manuscript is `landau_lpf_1_323.tex`.  It presents the recursive Buchstab-tail switching
argument and three independent exact-integer implementations for the
exponent `1.323` under the paper's recorded analytic inputs, proved via
the internal strict block exponent `1.3231`.  Its exact final normalized bound is
`8997005488261/9000000000000 < 1`.

The manuscript is positioned as a theorem under those inputs, an exact
endpoint audit, and a formal-verification note.  It now includes explicit finite
Mellin--Perron localization and prefix-uniform linear-sieve propositions,
rather than leaving the new recursive cross-conditions under a generic
"standard localization" reference.  An exhaustive integer audit now maps
all `34,215,168` ordered three-prime boxes and `19,635,200` tail child boxes
to the analytic branch ledger.  It explicitly acknowledges Li's
announced exponent `1.317` and must receive independent analytic-number-
theory review before any public theorem or priority claim.

Preferred build commands:

```text
tectonic landau_lpf_1_323.tex --outdir ../build/pdf
```

A conventional TeX installation can instead run `pdflatex` twice.  The
manuscript uses an internal `thebibliography`, so BibTeX is not required.

Build the review-source snapshot with

```text
scripts/build_1_323_review_bundle.sh
```

This writes `output/landau-1.323-review-bundle.tar.gz`; the adjacent
`.sha256` file verifies the exact generated archive.

Journal metadata, significance text, declarations, and a cover-letter draft
are collected in `SUBMISSION_PACKAGE_1_323.md`.

The minimal arXiv source archive is generated from the repository root with
`scripts/package_arxiv_source.sh`.

The current author metadata is JinWen Li, SouthWest Petroleum University,
`lifesize1@163.com`. The public GitHub tree is the Zenodo payload. Package it with
`scripts/package_zenodo_source.sh` or a GitHub Release tagged `v1.2.0`. The
Zenodo concept DOI is `10.5281/zenodo.22140874`; record the new version DOI
after the release is archived.
