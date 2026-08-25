import Mathlib

namespace Landau

/-!
# Gates 2 and 3: finite transfer combinatorics

This module records only the integer half-threshold facts used before Perron
localization and an abstract finite representation/coefficient bound.  It
does **not** formalize Perron inversion, Rosser weights, Corollary 7.1, or the
application of any discrepancy estimate to the paper's actual coefficients.
-/

/-- Gate 2 (half-integer localization): for natural-number variables,
`U<V` is equivalent to `U≤V-1`.  This removes equality ambiguity at the
finite integer level but does not prove a Perron integral formula. -/
theorem nat_strict_iff_le_pred {U V : Nat} (hV : 0 < V) :
    U < V ↔ U ≤ V - 1 := by
  omega

/-- Gate 2 (half-integer localization): an integer strict inequality is
equivalent to lying below the half-integer threshold `V-1/2`.  This is only
ordered-field arithmetic and does not estimate a truncated Perron kernel. -/
theorem nat_strict_iff_cast_lt_half_threshold {U V : Nat} :
    U < V ↔ (U : ℚ) < (V : ℚ) - 1 / 2 := by
  constructor
  · intro h
    have h' : (U : ℚ) + 1 ≤ V := by exact_mod_cast h
    linarith
  · intro h
    by_contra hnot
    have h' : V ≤ U := Nat.le_of_not_gt hnot
    have hcast : (V : ℚ) ≤ U := by exact_mod_cast h'
    linarith

/-- Gate 2 (half-integer localization): if `U<V`, the rational distance
from `U` to `V-1/2` is at least `1/2`.  This supplies the finite separation
claimed in the paper, not the analytic Perron truncation error. -/
theorem half_threshold_distance_ge {U V : Nat} (h : U < V) :
    1 / 2 ≤ |(V : ℚ) - 1 / 2 - (U : ℚ)| := by
  have h' : (U : ℚ) + 1 ≤ V := by exact_mod_cast h
  rw [abs_of_nonneg]
  · linarith
  · linarith

/-- A fixed tuple of divisors used as an abstract encoding target for gate 3.
It is not asserted here that the paper's prime/Rosser representations have
already been encoded into this type. -/
abbrev DivisorTuple (m k : Nat) := Fin k → {d // d ∈ m.divisors}

def divisorTupleBound (m k : Nat) : Nat := m.divisors.card ^ k

/-- Gate 3 (finite representation count): every finite set of `k`-tuples of
divisors of `m` has size at most `(# divisors m)^k`.  This is a fixed
divisor-function bound; it does not prove that Corollary 7.1 applies to the
paper's collected coefficient. -/
theorem card_divisorTuple_le_bound (m k : Nat)
    (reps : Finset (DivisorTuple m k)) :
    reps.card ≤ divisorTupleBound m k := by
  calc
    reps.card ≤ Fintype.card (DivisorTuple m k) := Finset.card_le_univ _
    _ = divisorTupleBound m k := by
      simp [DivisorTuple, divisorTupleBound]

/-- Gate 3 (bounded Rosser-type coefficients): if every representation has
coefficient of absolute value at most one, the collected coefficient is
bounded by the number of representations.  This is a triangle-inequality
lemma only and does not construct or validate Rosser weights. -/
theorem abs_sum_le_representation_count
    {ι : Type*} [DecidableEq ι] (reps : Finset ι) (lambda : ι → ℤ)
    (hlambda : ∀ r ∈ reps, |lambda r| ≤ 1) :
    |∑ r ∈ reps, lambda r| ≤ (reps.card : ℤ) := by
  calc
    |∑ r ∈ reps, lambda r| ≤ ∑ r ∈ reps, |lambda r| := by
      simpa using Finset.abs_sum_le_sum_abs lambda reps
    _ ≤ ∑ _r ∈ reps, (1 : ℤ) := by
      exact Finset.sum_le_sum fun r hr => hlambda r hr
    _ = (reps.card : ℤ) := by simp

/-- Gate 3 (combined finite coefficient bound): for representations already
encoded as `k` divisor tuples and weights bounded by one, the absolute
coefficient is at most the fixed divisor-tuple bound.  The missing analytic
step is still the identification of the real prefix/Rosser coefficient and
the application of Grimmelt--Merikoski Corollary 7.1. -/
theorem divisorTuple_coefficient_bound
    (m k : Nat) (reps : Finset (DivisorTuple m k))
    (lambda : DivisorTuple m k → ℤ)
    (hlambda : ∀ r ∈ reps, |lambda r| ≤ 1) :
    |∑ r ∈ reps, lambda r| ≤ (divisorTupleBound m k : ℤ) := by
  exact (abs_sum_le_representation_count reps lambda hlambda).trans
    (by exact_mod_cast card_divisorTuple_le_bound m k reps)

/-- Gate 3 (at-most-three-prime specialization): a prefix with at most three
prime slots plus one Rosser-divisor slot is bounded by the four-slot divisor
tuple function.  This remains an abstract encoding bound and does not prove
the prefix-uniform linear-sieve proposition. -/
theorem three_prime_prefix_coefficient_bound
    (m : Nat) (reps : Finset (DivisorTuple m 4))
    (lambda : DivisorTuple m 4 → ℤ)
    (hlambda : ∀ r ∈ reps, |lambda r| ≤ 1) :
    |∑ r ∈ reps, lambda r| ≤ (divisorTupleBound m 4 : ℤ) := by
  exact divisorTuple_coefficient_bound m 4 reps lambda hlambda

end Landau
