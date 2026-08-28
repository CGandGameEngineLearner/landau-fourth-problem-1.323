# arXiv submission guide for `landau_lpf_1_323`

This repository contains an arXiv-ready source package. The official arXiv
instructions are [Submission Overview](https://info.arxiv.org/help/submit/index.html)
and [Submit TeX/LaTeX](https://info.arxiv.org/help/submit_tex.html).

## 1. Prepare the source

From the repository root:

```text
scripts/package_arxiv_source.sh
```

The resulting file is:

```text
output/landau_lpf_1_323_arxiv_source.tar.gz
```

It contains exactly one file at its root:

```text
landau_lpf_1_323.tex
```

The paper has an internal `thebibliography`, no figures, no external style
files, and no `.bib`/`.bbl` dependency. Do not upload the PDF, `.aux`, `.log`,
`.out`, `.git`, `.lake`, or the full GitHub repository as the arXiv TeX
source. arXiv explicitly removes/ignores intermediate output files and
recommends submitting only files needed to compile the paper.

For this one-file paper you may upload either the tarball above or the
`paper/landau_lpf_1_323.tex` file directly. The direct `.tex` upload is the
simplest option.

## 2. Start the submission

1. Sign in or create an arXiv account at <https://arxiv.org/>
   and open **Submit** / **Start New Submission**.
2. Select the primary category `math.NT` (Number Theory). Complete any
   first-time endorsement or author-account prompts arXiv displays.
3. Enter the metadata exactly as follows:

   - Title: `A recursive Buchstab switching improvement for the greatest prime factor of n^2+1`
   - Author: `JinWen Li`
   - Affiliation: `SouthWest Petroleum University`
   - Email: `lifesize1@163.com`
   - Comments: `15 pages; Lean 4 formalization and exact-integer verification code available on GitHub.`

4. Paste the abstract from the TeX source. The source already contains the
   same title, author, affiliation, email, keywords, and abstract.
5. Upload the TeX source or the minimal tarball. If arXiv asks for a TeX
   processor, choose the automatically recommended LaTeX/PDFLaTeX processor.
   This source has been checked with PDFLaTeX and Tectonic.

The manuscript includes an explicit author disclosure that GPT-5.6 Sol was
used as a reasoning and coding assistant during development of the core
argument and verification materials. This is a transparency statement, not
an attribution of authorship or independent mathematical verification.

## 3. Process and inspect the PDF

1. Let arXiv run its **Process** step.
2. Open the generated PDF and compare it with
   `output/landau_lpf_1_323.pdf`.
3. Check especially the title, author line, affiliation, email, theorem
   statement, references, and the final GitHub URL.
4. Read the processing log. If arXiv reports a TeX error, do not submit;
   correct the source locally and regenerate the minimal package.
5. Select the appropriate arXiv license and agree to the submission terms.
6. Submit/announce only after the preview PDF and metadata are correct.

arXiv's current TeX system compiles the uploaded source itself, so the local
PDF is a comparison artifact, not a replacement for checking the arXiv-built
PDF. arXiv also advises against including hidden version-control directories
or unrelated files in the source package.

## 4. After announcement

Record the arXiv identifier in the GitHub README and, if desired, add it to
the paper's references or metadata in a new Git commit. Keep the Lean/GitHub
repository synchronized with the announced source version. Deposit the same
commit on Zenodo via a GitHub Release (`v1.0.0`, then `v1.0.1` after the
DOI is inserted), or with `scripts/package_zenodo_source.sh`. The verification
repository is:

<https://github.com/CGandGameEngineLearner/landau-fourth-problem-1.323>
