import Landau.HarmanRecursiveCertificateCanonical
import Landau.HarmanRecursiveEndpoint
import Landau.HarmanSwitchingCombinatorics
import Landau.HarmanF6Midpoint
import Landau.LargestPrimeFactorExponent
import Landau.HarmanProofAdverseGeometry
import Landau.HarmanModelNormalization
import Landau.HarmanTypeIIInterior
import Landau.HarmanFiniteTransferCombinatorics

/-!
# Landau `1.323` verification project

This is the deliberately small root of the public verification repository.
It imports only the recursive Harman certificate, its endpoint arithmetic,
the finite `F₆` midpoint proof, the dyadic real-power conversion, the finite
Buchstab sign ledger, and their local dependencies. The unrelated
Gaussian/Atkin--Lehner research library is not part of this snapshot.

The four canonical block equalities are supplied by `native_decide`.  After
their small natural-number projections are imported, the canonical sum,
division, endpoint arithmetic, `F₆` convexity, and geometric/algebraic
one-sided checks are ordinary kernel-checked proofs.  This trust split does
not assert that the finite algorithm equals the analytic `H(α)` integral.
-/
