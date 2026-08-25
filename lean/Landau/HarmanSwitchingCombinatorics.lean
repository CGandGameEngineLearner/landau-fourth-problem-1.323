import Mathlib

namespace Landau

/-!
# Finite combinatorics of the Harman--Buchstab switching

This module proves the exact finite identities underlying the new
three-step switching.  It is deliberately abstract: `bad p x` says that the
index `p` divides, or otherwise excludes, the object `x`.  Thus no analytic
or number-theoretic estimate enters the proofs below.
-/

section AbstractBuchstab

variable {ι Ω R : Type*} [AddCommGroup R]

/-- Abstract finite weighted sifted sum.  The entries in `active` must divide
the object; the entries in `cutoff` must not.  Boolean predicates make the
combinatorial partition independent of any arithmetic model. -/
def finiteSiftedWeight (A : Finset Ω) (w : Ω → R)
    (bad : ι → Ω → Bool) (active cutoff : List ι) : R :=
  ∑ x ∈ A,
    if active.all (fun p => bad p x) &&
        cutoff.all (fun p => !(bad p x)) then w x else 0

/-- One-step Buchstab identity: an object surviving the old cutoff either
survives the new test or has the new index active. -/
theorem finiteSiftedWeight_append_one
    (A : Finset Ω) (w : Ω → R) (bad : ι → Ω → Bool)
    (active cutoff : List ι) (p : ι) :
    finiteSiftedWeight A w bad active cutoff =
      finiteSiftedWeight A w bad active (cutoff ++ [p]) +
        finiteSiftedWeight A w bad (p :: active) cutoff := by
  simp only [finiteSiftedWeight, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ha : active.all (fun q => bad q x) = true
  · by_cases hc : cutoff.all (fun q => !(bad q x)) = true
    · by_cases hp : bad p x = true
      · simp [ha, hc, hp]
      · have hp' : bad p x = false := Bool.eq_false_of_not_eq_true hp
        simp [ha, hc, hp']
    · have hc' : cutoff.all (fun q => !(bad q x)) = false :=
        Bool.eq_false_of_not_eq_true hc
      simp [ha, hc']
  · have ha' : active.all (fun q => bad q x) = false :=
      Bool.eq_false_of_not_eq_true ha
    simp [ha']

/-- Sum of the disjoint first-bad-index pieces removed while a list of tests
is appended to a cutoff. -/
def buchstabRemovedWeight (A : Finset Ω) (w : Ω → R)
    (bad : ι → Ω → Bool) (active base : List ι) : List ι → R
  | [] => 0
  | p :: ps =>
      finiteSiftedWeight A w bad (p :: active) base +
        buchstabRemovedWeight A w bad active (base ++ [p]) ps

/-- Exact finite Buchstab identity for an arbitrary ordered list of new
tests.  No primality or asymptotic hypothesis is used. -/
theorem finite_buchstab_identity
    (A : Finset Ω) (w : Ω → R) (bad : ι → Ω → Bool)
    (active base extra : List ι) :
    finiteSiftedWeight A w bad active (base ++ extra) =
      finiteSiftedWeight A w bad active base -
        buchstabRemovedWeight A w bad active base extra := by
  induction extra generalizing base with
  | nil => simp [buchstabRemovedWeight]
  | cons p ps ih =>
      rw [show base ++ p :: ps = (base ++ [p]) ++ ps by simp]
      rw [ih]
      rw [finiteSiftedWeight_append_one A w bad active base p]
      simp only [buchstabRemovedWeight]
      abel

/-- Applying the same subtractive identity three times produces exactly the
sign pattern `A₀ - A₁ + A₂ - A₃`. -/
theorem three_step_buchstab_signs
    {target A0 retained1 A1 retained2 A2 A3 : R}
    (h0 : target = A0 - retained1)
    (h1 : retained1 = A1 - retained2)
    (h2 : retained2 = A2 - A3) :
    target = A0 - A1 + A2 - A3 := by
  rw [h0, h1, h2]
  abel

/-- Four nested subtractive Buchstab identities have the alternating sign
pattern `A₀ - A₁ + A₂ - A₃ + A₄`.  This is the pattern used when a fourth
prime is exposed inside a previously discarded negative branch. -/
theorem four_step_buchstab_signs
    {target A0 retained1 A1 retained2 A2 retained3 A3 A4 : R}
    (h0 : target = A0 - retained1)
    (h1 : retained1 = A1 - retained2)
    (h2 : retained2 = A2 - retained3)
    (h3 : retained3 = A3 - A4) :
    target = A0 - A1 + A2 - A3 + A4 := by
  rw [h0, h1, h2, h3]
  abel

/-- A lower bound for an omitted subtractive tail may itself be subtracted
from the coarse upper envelope. -/
theorem retain_subtractive_tail_lower_bound
    [PartialOrder R] [IsOrderedAddMonoid R]
    {target coarse tail tailLower : R}
    (htarget : target = coarse - tail) (hlower : tailLower ≤ tail) :
    target ≤ coarse - tailLower := by
  rw [htarget]
  exact sub_le_sub_left hlower coarse

/-- Proof-direction ledger for a negative Buchstab node: a base lower bound
minus a children upper bound is a lower bound for the node. -/
theorem buchstab_node_lower_bound
    [PartialOrder R] [IsOrderedAddMonoid R]
    {node base children baseLower childrenUpper : R}
    (hnode : node = base - children)
    (hbase : baseLower ≤ base) (hchildren : children ≤ childrenUpper) :
    baseLower - childrenUpper ≤ node := by
  rw [hnode]
  exact sub_le_sub hbase hchildren

/-- Proof-direction ledger for a positive Buchstab node: a base upper bound
minus a children lower bound is an upper bound for the node. -/
theorem buchstab_node_upper_bound
    [PartialOrder R] [IsOrderedAddMonoid R]
    {node base children baseUpper childrenLower : R}
    (hnode : node = base - children)
    (hbase : base ≤ baseUpper) (hchildren : childrenLower ≤ children) :
    node ≤ baseUpper - childrenLower := by
  rw [hnode]
  exact sub_le_sub hbase hchildren

theorem discard_nonnegative_subtracted_tail
    [PartialOrder R] [IsOrderedAddMonoid R]
    {total kept omitted : R} (htotal : total = kept + omitted)
    (homitted : 0 ≤ omitted) :
    -total ≤ -kept := by
  rw [htotal]
  exact neg_le_neg (le_add_of_nonneg_right homitted)

/-- Truncating a subtractive Buchstab sum gives an upper bound when the
omitted terms are nonnegative. -/
theorem truncate_subtractive_buchstab_sum
    [PartialOrder R] [IsOrderedAddMonoid R]
    {target coarse kept omitted : R}
    (htarget : target = coarse - (kept + omitted))
    (homitted : 0 ≤ omitted) :
    target ≤ coarse - kept := by
  rw [htarget]
  exact sub_le_sub_left (le_add_of_nonneg_right homitted) coarse

/-- If the last Buchstab layer has negative sign, retaining only a
nonnegative good part and discarding its complement preserves an upper
bound. -/
theorem retain_negative_good_part
    [PartialOrder R] [IsOrderedAddMonoid R]
    {pre full good discarded : R} (hfull : full = good + discarded)
    (hdiscarded : 0 ≤ discarded) :
    pre - full ≤ pre - good := by
  rw [hfull]
  exact sub_le_sub_left (le_add_of_nonneg_right hdiscarded) pre

/-- Abstract sifted sums are nonnegative when every underlying weight is. -/
theorem finiteSiftedWeight_nonneg
    [PartialOrder R] [IsOrderedAddMonoid R]
    (A : Finset Ω) (w : Ω → R) (bad : ι → Ω → Bool)
    (active cutoff : List ι) (hw : ∀ x ∈ A, 0 ≤ w x) :
    0 ≤ finiteSiftedWeight A w bad active cutoff := by
  simp only [finiteSiftedWeight]
  apply Finset.sum_nonneg
  intro x hx
  split
  · exact hw x hx
  · exact le_rfl

end AbstractBuchstab

end Landau
