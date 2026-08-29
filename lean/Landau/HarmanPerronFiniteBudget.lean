import Landau.HarmanFiniteTransferCombinatorics
import Mathlib

namespace Landau

/-!
# Gate 2: finite Perron error budget

The lemmas below take the paper's separation and truncation *hypotheses*
and check the resulting power-saving arithmetic.  They do **not** prove
Perron's formula, the displayed contour integral, or that the actual
sifted sums satisfy those hypotheses.
-/

/-- Gate 2 (log separation): if `U<V` are positive integers, then
`log((V-1/2)/U) ≥ 2/(4U+1)`.  Combined with `U≤x^C` this is the paper's
`≫_C x^{-C}` lower bound.  It does not estimate a contour integral. -/
theorem log_ratio_ge_two_div_four_U_succ
    {U V : ℕ} (hU : 0 < U) (hUV : U < V) :
    (2 : ℝ) / (4 * (U : ℝ) + 1) ≤
      Real.log (((V : ℝ) - 1 / 2) / (U : ℝ)) := by
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hVge : (U : ℝ) + 1 ≤ V := by exact_mod_cast hUV
  set t := ((V : ℝ) - 1 / 2 - (U : ℝ)) / (U : ℝ)
  have ht : 0 ≤ t := by
    unfold t
    exact div_nonneg (by linarith [hVge]) hUpos.le
  have ht0 : (1 : ℝ) / (2 * (U : ℝ)) ≤ t := by
    have hnum : (1 : ℝ) / 2 ≤ (V : ℝ) - 1 / 2 - (U : ℝ) := by linarith [hVge]
    have hhalf : (1 : ℝ) / 2 / (U : ℝ) ≤ t := by
      unfold t
      exact (div_le_div_iff_of_pos_right hUpos).mpr hnum
    convert hhalf using 1
    field_simp
  have hlog : 2 * t / (2 + t) ≤ Real.log (1 + t) := by
    convert Real.le_log_one_add_of_nonneg ht using 1
    ring
  have harg : (1 : ℝ) + t = ((V : ℝ) - 1 / 2) / (U : ℝ) := by
    unfold t
    field_simp [hUpos.ne']
  have hfun_mono :
      2 * ((1 : ℝ) / (2 * (U : ℝ))) / (2 + 1 / (2 * (U : ℝ))) ≤
        2 * t / (2 + t) := by
    have hden0 : 0 < 2 + (1 : ℝ) / (2 * (U : ℝ)) := by positivity
    have hden1 : 0 < 2 + t := by linarith
    refine (div_le_div_iff₀ hden0 hden1).2 ?_
    nlinarith [ht0]
  have hsimp :
      2 * ((1 : ℝ) / (2 * (U : ℝ))) / (2 + 1 / (2 * (U : ℝ))) =
        2 / (4 * (U : ℝ) + 1) := by
    field_simp
    ring
  calc
    (2 : ℝ) / (4 * (U : ℝ) + 1) = _ := hsimp.symm
    _ ≤ 2 * t / (2 + t) := hfun_mono
    _ ≤ Real.log (1 + t) := hlog
    _ = Real.log (((V : ℝ) - 1 / 2) / (U : ℝ)) := by rw [harg]

/-- Gate 2 (polynomial comparison): if `U≤X^C` and `X≥1`, then
`2/(4U+1) ≥ (2/5) X^{-C}`. -/
theorem two_div_four_U_succ_ge_two_fifths
    {U : ℕ} {X : ℝ} {C : ℕ} (hU : 0 < U)
    (hX : (1 : ℝ) ≤ X) (hUX : (U : ℝ) ≤ X ^ (C : ℝ)) :
    (2 : ℝ) / (5 * X ^ (C : ℝ)) ≤ (2 : ℝ) / (4 * (U : ℝ) + 1) := by
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hdenU : 0 < 4 * (U : ℝ) + 1 := by linarith
  have hpowPos : 0 < X ^ (C : ℝ) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hX) _
  have hdenX : 0 < 5 * X ^ (C : ℝ) := mul_pos (by norm_num) hpowPos
  refine (div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
    hdenX hdenU).2 ?_
  have h1 : (1 : ℝ) ≤ X ^ (C : ℝ) := by
    calc
      (1 : ℝ) = X ^ (0 : ℝ) := (Real.rpow_zero X).symm
      _ ≤ X ^ (C : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX (by exact_mod_cast (Nat.zero_le C))
  have : 4 * (U : ℝ) + 1 ≤ 4 * X ^ (C : ℝ) + 1 := by linarith
  have : 4 * X ^ (C : ℝ) + 1 ≤ 5 * X ^ (C : ℝ) := by linarith [h1]
  linarith

/-- Gate 2 (explicit `≫_C X^{-C}` form): the two previous lemmas compose. -/
theorem log_ratio_ge_two_fifths_pow
    {U V : ℕ} {X : ℝ} {C : ℕ} (hU : 0 < U) (hUV : U < V)
    (hX : (1 : ℝ) ≤ X) (hUX : (U : ℝ) ≤ X ^ (C : ℝ)) :
    (2 : ℝ) / (5 * X ^ (C : ℝ)) ≤
      Real.log (((V : ℝ) - 1 / 2) / (U : ℝ)) :=
  (two_div_four_U_succ_ge_two_fifths hU hX hUX).trans
    (log_ratio_ge_two_div_four_U_succ hU hUV)

/-- Gate 2 (integer form used in the paper): `A'>A+B+C` and `X≥2` make
`X^B · 2 · X^{C-A'} ≤ X^{-A}`.  This is the summed-truncation budget after
the log-separation lower bound has been granted. -/
theorem perron_truncation_nat_budget
    {X : ℝ} {A A' B C : ℕ}
    (hX : (2 : ℝ) ≤ X) (hA' : A + B + C + 1 ≤ A') :
    X ^ (B : ℝ) * (2 * X ^ ((C : ℝ) - (A' : ℝ))) ≤
      X ^ (-(A : ℝ)) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hexp : (B : ℝ) + (C : ℝ) - (A' : ℝ) + 1 ≤ -(A : ℝ) := by
    have : (A + B + C + 1 : ℕ) ≤ A' := hA'
    have : (A + B + C + 1 : ℝ) ≤ (A' : ℝ) := by exact_mod_cast this
    linarith
  have hpow :
      X ^ ((B : ℝ) + (C : ℝ) - (A' : ℝ) + 1) ≤ X ^ (-(A : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  have hexpB : (B : ℝ) + ((C : ℝ) - (A' : ℝ)) =
      (B : ℝ) + (C : ℝ) - (A' : ℝ) := by ring
  calc
    X ^ (B : ℝ) * (2 * X ^ ((C : ℝ) - (A' : ℝ))) =
        2 * (X ^ (B : ℝ) * X ^ ((C : ℝ) - (A' : ℝ))) := by ring
    _ = 2 * X ^ ((B : ℝ) + ((C : ℝ) - (A' : ℝ))) := by
      rw [← Real.rpow_add hXpos]
    _ = 2 * X ^ ((B : ℝ) + (C : ℝ) - (A' : ℝ)) := by rw [hexpB]
    _ ≤ X * X ^ ((B : ℝ) + (C : ℝ) - (A' : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hX
        (Real.rpow_pos_of_pos hXpos _).le
    _ = X ^ (1 : ℝ) * X ^ ((B : ℝ) + (C : ℝ) - (A' : ℝ)) := by
      rw [Real.rpow_one]
    _ = X ^ ((1 : ℝ) + ((B : ℝ) + (C : ℝ) - (A' : ℝ))) := by
      rw [← Real.rpow_add hXpos]
    _ = X ^ ((B : ℝ) + (C : ℝ) - (A' : ℝ) + 1) := by ring_nf
    _ ≤ X ^ (-(A : ℝ)) := hpow

end Landau
