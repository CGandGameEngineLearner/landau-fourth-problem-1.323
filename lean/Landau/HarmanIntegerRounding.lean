import Mathlib

namespace Landau

/-!
# Kernel-checked integer rounding for the recursive `1.323` certificate

This module contains only the fixed-point operations and their exact rational
rounding specifications. The analytic Type-I/II and linear-sieve inputs are
external to the formalization.
-/

def scale : Nat := 1000000000000
def omegaUpper : Nat := 561700000000
def omegaLower : Nat := 560700000000

def floorScaled (num den : Nat) : Nat := scale * num / den
def ceilScaled (num den : Nat) : Nat := (scale * num + den - 1) / den
def mulDown (x y : Nat) : Nat := x * y / scale
def mulUp (x y : Nat) : Nat := (x * y + scale - 1) / scale

/- The two endpoint parametrizations are the exact integer geometry used by
the canonical alpha/beta certificate grid. -/
def commonBetaNum (n b i k : Nat) : Nat :=
  8 * b * (n - i) + k * (4 * n + 5 * i - 3)

def containingBetaNum (n b i k : Nat) : Nat :=
  8 * b * (n - i - 1) + k * (4 * n + 5 * i + 8)

theorem floorScaled_spec (num den : Nat) (hden : 0 < den) :
    ((floorScaled num den : Nat) : ℚ) / scale ≤ (num : ℚ) / den := by
  apply (div_le_div_iff₀ (by norm_num [scale] : (0 : ℚ) < scale)
    (by exact_mod_cast hden : (0 : ℚ) < den)).2
  have h := Nat.div_mul_le_self (scale * num) den
  have h' : floorScaled num den * den ≤ num * scale := by
    simpa [floorScaled, Nat.mul_comm] using h
  exact_mod_cast h'

theorem ceilScaled_spec (num den : Nat) (hden : 0 < den) :
    (num : ℚ) / den ≤ ((ceilScaled num den : Nat) : ℚ) / scale := by
  apply (div_le_div_iff₀ (by exact_mod_cast hden : (0 : ℚ) < den)
    (by norm_num [scale] : (0 : ℚ) < scale)).2
  have h : scale * num ≤ den * ceilScaled num den := by
    simpa [ceilScaled, Nat.ceilDiv_eq_add_pred_div] using
      (le_smul_ceilDiv (α := Nat) (β := Nat)
        (a := den) (b := scale * num) hden)
  have h' : num * scale ≤ ceilScaled num den * den := by
    simpa [Nat.mul_comm] using h
  exact_mod_cast h'

theorem mulDown_spec (x y : Nat) :
    ((mulDown x y : Nat) : ℚ) / scale ≤
      ((x : ℚ) / scale) * ((y : ℚ) / scale) := by
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (by norm_num [scale] : (0 : ℚ) < scale)
    (by norm_num [scale] : (0 : ℚ) < scale * scale)).2
  have h := Nat.div_mul_le_self (x * y) scale
  have h' : mulDown x y * (scale * scale) ≤ x * y * scale := by
    simpa [mulDown, Nat.mul_assoc] using Nat.mul_le_mul_right scale h
  exact_mod_cast h'

theorem mulUp_spec (x y : Nat) :
    ((x : ℚ) / scale) * ((y : ℚ) / scale) ≤
      ((mulUp x y : Nat) : ℚ) / scale := by
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (by norm_num [scale] : (0 : ℚ) < scale * scale)
    (by norm_num [scale] : (0 : ℚ) < scale)).2
  have h : x * y ≤ scale * mulUp x y := by
    simpa [mulUp, Nat.ceilDiv_eq_add_pred_div] using
      (le_smul_ceilDiv (α := Nat) (β := Nat)
        (a := scale) (b := x * y) (by norm_num [scale]))
  have h' : x * y * scale ≤ mulUp x y * (scale * scale) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right scale h
  exact_mod_cast h'

end Landau
