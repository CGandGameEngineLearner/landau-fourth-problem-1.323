# Analytic transfer audit for the recursive `1.323` certificate

Date: 25 August 2026.

## 1. Status and scope

The finite computation is now closed.  Three independent exact-integer
implementations (fixed-width C++, arbitrary-precision Python, and Lean) give
the canonical lower bound

```text
recursive switching saving >= 0.032303187971 > 0.032.
```

The four large Lean computations are checked in separate modules and are
projected to small natural-number theorems before final aggregation.  The
whole project builds.  This note audits the remaining source-to-source
analytic transfer from the finite tree to the sifted sums.  The published
Type-I/II estimates and the standard dimension-one linear sieve remain
external inputs; no Lean file attempts to reprove them.

The resulting theorem should still be described as a complete candidate
proof until it has received an independent analytic-number-theory review.
It is not a proof of prime values of `n^2+1`.

The manuscript now promotes the two previously implicit uniformity steps to
named results.  `Finite cross-condition localization` uses the half-integer
threshold `V-1/2` in truncated Perron inversion, so strict prime-ordering and
`P+(d)<q3` conditions have no equality ambiguity and incur only a fixed
polylogarithmic kernel loss.  `Prefix-uniform linear sieve` collects each
Rosser modulus together with the at-most-three-prime prefix and invokes the
absolute Type-I discrepancy sum at total level `x^(1/2-nu)`.  These additions
close the expository gap identified in the first internal review; an external
expert must still check that their stated uniformity matches every recursive
branch.

An exhaustive canonical-grid audit now checks this matching at the box
level.  It visits `34,215,168` ordered `A3` boxes and `19,635,200` tail
two-prime boxes, observes every analytic branch in the ledger, and proves
the following proof-adverse minimum Buchstab arguments using integer
comparisons only:

```text
A3 Type-II lower branch      5.206977117
R1 base lower branch         9.007506255
pair Type-II upper branch    8.002880298
recursive-base upper branch  7.508771632
```

The first two exceed `2.47`, and the last two exceed `4`.  The script is
`scripts/audit_harman_recursive_branch_coverage.py` and terminates with
`BRANCH_LEDGER_CERTIFIED=YES`.

## 2. Published inputs and strict margins

For a smooth modulus block `P=x^alpha`, put

```text
a     = alpha-1,
sigma = (2-alpha)/3,
gamma = (5-4*alpha)/3,
xi    = 3/2-alpha,
tau   = xi/2.
```

Grimmelt--Merikoski Corollary 7.1 supplies Type I for
`D<=x^(1/2-eta)`.  Its exact statement bounds the sum over `d<=D` of the
absolute value of the modulus-`d` discrepancy.  By the triangle inequality
this permits arbitrary divisor-bounded `lambda_d`, with only an `x^o(1)`
loss.  Corollary 7.2 supplies Type II for divisor-bounded
coefficients, with the `N` coefficient squarefree-supported, when

```text
x^(alpha-1+2*eta) <= N
N <= x^((2-alpha)/3-(4/3)*eta),
M >= N,  M*N=x^alpha.
```

As in the `1.3201` audit, use one fixed `nu>0` and the shifted parameters

```text
a_nu     = a+3*nu,
sigma_nu = sigma-2*nu,
gamma_nu = gamma-4*nu,
xi_nu    = xi-3*nu,
tau_nu   = xi_nu/2.
```

Then `[a_nu,sigma_nu]` lies strictly inside Corollary 7.2 and

```text
(a+2*nu)+xi_nu    = 1/2-nu,
(a+2*nu)+gamma_nu = sigma-2*nu
                         < sigma-(4/3)*nu.
```

These are the two ledgers used in Merikoski's Fundamental Proposition II.
The certificate retains only `alpha<1.22`, where `gamma>=0.04` in the
limiting geometry.  Thus all shifted cutoffs remain uniformly separated
for sufficiently small fixed `nu`.

## 3. Exact finite tree and signs

The first split is

```text
S(A(P),x^a)
 = S(A(P),x^gamma)
   - sum_(gamma<beta1<tau) S(A(P)_{q1},q1)
   - sum_(tau<beta1<a)     S(A(P)_{q1},q1).
```

Expand the first prime range twice more.  If `A0,A1,A2,A3` denote the
usual zero-, one-, two-, and three-prime terms, then

```text
S(A(P),x^a) <= A0-A1+A2-A3-T,
```

where `T` is any lower bound for the last one-prime tail.  The sign rules
and this subtractive-tail inequality are proved abstractly in
`Landau/HarmanSwitchingCombinatorics.lean`.

The old proof lower-bounded `A3` only on Type-II triples and set `T=0`.
The recursive certificate makes two additions:

1. on a non-Type-II three-prime child it may use a lower linear-sieve
   bound;
2. it obtains a positive `T` by subtracting certified upper bounds for the
   two-prime children of each tail node.

No branch is recursively exposed beyond the third selected prime.

## 4. Linear-sieve envelopes used by the tree

After fixing a squarefree prime prefix of total exponent `s0`, Corollary
7.1 supplies the linear-sieve remainder level

```text
delta = 1/2-s0-nu.
```

For sieve cutoff `x^zeta`, write `s=delta/zeta`.  After removing the common
Euler factor, the standard dimension-one envelopes are

```text
upper:  e^(-EulerGamma) F(s),
lower:  e^(-EulerGamma) f(s).
```

For the upper bound, `e^(-EulerGamma)F(s)=2/s` on `1<=s<=3`, and the
function is at most `2/3` for `s>=3`.  Therefore the proof-adverse global
upper bound used for a two-prime child is

```text
U_LS(beta1,beta2)
 = max(2/(1/2-beta1-beta2), 2/(3*beta2)).
```

The maximum is intentionally wasteful near a cell crossing `s=3`; it is
uniformly valid on both sides.

For `2<=s<=4`,

```text
e^(-EulerGamma) f(s) = 2*log(s-1)/s
                    >= 4*(s-2)/s^2.
```

The logarithmic inequality and monotonicity of the rational right-hand side
on `[2,4]` are proved in `Landau/LinearSieveRationalEnvelope.lean`.  At
`s=4` the rational lower envelope equals `1/2`; standard monotonicity of
the lower linear-sieve function licenses the constant continuation `1/2`
for `s>=4`.

The integer certificate samples the rational lower envelope only at the
21 thresholds

```text
2.01, 2.1, 2.2, ..., 3.9, 4.0.
```

For each threshold `t`, the interval where the true sieve parameter is at
least `t` receives weight `4(t-2)/t^2`; overlapping intervals take the
maximum.  Omitting `2<s<2.01` gives zero and is harmless.

To apply the linear sieve uniformly after summing over prefix primes,
combine the Rosser weights with the at most three prime indicators.  The
number of representations is bounded by one fixed divisor function and
the total modulus is below `x^(1/2-nu)`.  Hence Corollary 7.1 applies to the
combined divisor-bounded coefficient.  Prime ordering and cell boundaries
are removed by the same fixed Mellin/Perron localization used for the
Type-II terms.

## 5. Lower bound for the three-prime term

For an ordered triple `gamma<beta3<beta2<beta1<tau`, let `W3` be the
maximum of the following available lower weights.

* `u_-=0.5607` if one of
  `beta1+beta2`, `beta1+beta3`, `beta2+beta3`, or
  `beta1+beta2+beta3` lies in `[a_nu,sigma_nu]`.
* The rational lower-linear-sieve weight for residual level
  `1/2-beta1-beta2-beta3-nu` and cutoff `beta3`.

Then the retained lower model is

```text
A3_lower(alpha)
 = alpha * integral W3(beta1,beta2,beta3)
     d beta1 d beta2 d beta3
     /(beta1*beta2*beta3^2).
```

The Type-II part is justified exactly as in the old three-prime transfer:
choose the first eligible subset, place its squarefree product on the `N`
side, and separate ordering and priority conditions by a finite smooth
partition.  The lower-sieve part instead uses Corollary 7.1 as described in
Section 4.  Since both are lower bounds for the same nonnegative child, the
maximum is again a valid lower bound.

For every Type-II child in the retained range the Buchstab argument is
larger than `2.47`.  Indeed `beta_j<a` and ordering imply

```text
(alpha-beta1-beta2-beta3)/beta3
  > (3-2*alpha)/(alpha-1)
  >= (3-2*1.22)/(1.22-1)
  > 2.54.
```

Thus the quoted bound `omega>=0.5607` applies.

## 6. Recursive lower bound for the omitted one-prime tail

For `tau<beta1<a`, Buchstab gives

```text
S(A(P)_{q1},q1)
 = S(A(P)_{q1},x^gamma)
   - sum_(gamma<beta2<beta1) S(A(P)_{q1*q2},q2).
```

The base is covered by Fundamental Proposition II because `beta1<a<xi`.
Its lower model is `u_-/gamma`.  The Buchstab argument is at least `9`, so
the lower omega bound is valid.

For each two-prime child define `U2` as the minimum of all available upper
bounds:

```text
U2 = min(
  U_LS,
  u_+/beta2                    when beta1+beta2 is Type II,
  u_+/gamma - integral W3 d beta3/beta3^2
                                when beta1+beta2<=xi
).
```

The last option is another Buchstab identity.  Its base is covered by
Fundamental Proposition II because the two-prime prefix is at most `xi`,
and its three-prime children have the lower bound from Section 5.  It is
used only when the certified child lower sum does not exceed the base
upper bound.

The Type-II upper option is valid on the actual ordered region.  Since
`beta2<beta1`, one has `beta2<=(beta1+beta2)/2`; if the pair sum is at most
`sigma`, then

```text
(alpha-beta1-beta2)/beta2
 >= 2*(alpha-sigma)/sigma >= 6.4.
```

The recursive base has Buchstab argument at least `7.5`.  Hence
`u_+=0.5617`, valid for arguments at least `4`, applies in both places.

Consequently

```text
T(alpha) = alpha * integral_(tau)^(a)
  max(0, u_-/gamma
         - integral_(gamma)^(beta1) U2(beta1,beta2) d beta2/beta2)
  d beta1/beta1
```

is a valid lower bound for the omitted negative tail.

## 7. Proof-adverse box geometry

On each alpha cell the certificate uses only common subdomains for positive
terms and containing superdomains for subtracted upper terms.

* The tail `beta1` interval is the common intersection
  `[tau(alpha_lo),a(alpha_lo)]` after outward rounding.
* Its `beta2` children use a containing interval from the smallest gamma
  to the upper endpoint of the `beta1` box.
* The entire same-cell `beta2` region is subtracted.  It therefore includes,
  rather than loses, configurations of two distinct primes in one exponent
  cell; it also harmlessly overcounts `beta2>=beta1`.
* Three-prime lower terms use common ordered boxes with
  `beta3<beta2<beta1`; same-cell boxes are omitted from lower bounds.
* A Type-II box is retained only when its full subset-sum interval lies in
  the full alpha-cell intersection of `[a,sigma]`.
* Lower log and reciprocal weights are rounded down; child upper weights
  are rounded up.

This is precisely the correction that removes the earlier false `4/3`
signal.

## 8. Exact certificate and independent agreement

The canonical grid is

```text
alpha cells = 1200
A3 beta cells = 300
tail beta cells = 160
scale = 10^12.
```

The exact totals before division by the alpha denominator `14400` are

```text
savingSum = 465165906793678
tailSum   = 263955803476054
a3Sum     = 640218767558782
positive alpha cells = 727.
```

Downward division gives

```text
tail lower integral = 0.018330264130
A3 lower integral   = 0.044459636636
saving lower        = 0.032303187971.
```

The C++ and Python 1200-cell dumps agree byte for byte and have SHA-256

```text
6e1901ca1dc8b2c32ae6bcc3759a42ea9a3dab8932870eeb3f6e2d42f0ac3175.
```

Lean independently recomputes the grid in four 192-cell blocks plus a
zero tail block.  The block saving sums are

```text
154113574025565
151615832402575
117510700363272
 41925800002266
              0.
```

Their projected natural-number theorems aggregate in
`Landau/HarmanRecursiveCertificateCanonical.lean`, which proves both the
exact saving and the strict comparison with `0.032`.

## 9. Limiting geometry and endpoint closure

For fixed `nu>0`, all Type-II and linear-sieve applications are made in
strict interiors.  On `alpha<1.22`, gamma is bounded away from zero, so all
integrands have a common integrable majorant.  The finitely many Type-II,
linear-sieve-threshold, ordering, and cell-boundary hyperplanes have measure
zero.  Dominated convergence therefore lets the fixed-margin envelope
approach the certified limiting envelope as `nu` and the smooth priority
mesh tend to zero.

At internal block exponent `1.3231`, substituting the certified saving gives
the exact normalized total

```text
8997005488261 / 9000000000000 < 1,
```

with margin

```text
2994511739 / 9000000000000 > 0.
```

Choose one fixed positive `nu` and one fixed smooth mesh whose combined
loss is less than half this margin, then take `x` large enough to absorb the
power-saving and `o(1)` errors.  The standard dyadic conversion from block
exponent `1.3231` gives the pointwise exponent `1.323`.

The exact saving, endpoint total, endpoint margin, and block-to-pointwise
strict inequality are all checked in Lean.

## 10. Audit conclusion

Every new finite branch has a matched published or standard analytic
input:

* Fundamental Proposition II for prefixes at most `xi`;
* Corollary 7.2 for uniformly interior Type-II subset products;
* Corollary 7.1 plus the standard dimension-one linear sieve for the
  upper and lower residual-sieve branches;
* fixed-depth Mellin/Perron localization for ordering and cross-conditions.

No sign reversal, endpoint use, unbounded-depth coefficient, or missing
same-cell prime configuration remains in the audited tree.  Subject to
accepting those external analytic theorems, the manuscript can now be
upgraded from the `1.3201` candidate to the stronger statement

```text
P+(n^2+1) > n^1.323
```

for infinitely many `n`.  This improves the currently published/announced
`1.317` frontier, but it remains a greatest-prime-factor approximation and
does not bypass the parity barrier in Landau's fourth problem.
