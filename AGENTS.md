# Repository rules

## Bilingual paper synchronization

- `paper/landau_lpf_1_323.tex` is the authoritative English manuscript and
  `paper/landau_lpf_1_323_zh.tex` is its Chinese companion translation.
- Every operation that changes the paper's mathematical content, claims,
  proof-status language, structure, formulas, constants, references, or
  metadata must update both files in the same working turn.
- The two versions may use natural language-specific phrasing and pagination,
  but their mathematical content and verification boundaries must agree.
- Before finishing any paper edit, compile both PDFs and check that neither
  version has unresolved references or changed locked certificate values.
- Never describe Lean as proving the analytic transfer or the main theorem in
  either language.
