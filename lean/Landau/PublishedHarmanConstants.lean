import Mathlib

namespace Landau

/-!
# Published Harman-sieve constants used by the `1.323` endpoint

These rational constants are quoted analytic inputs from Merikoski's
published sieve calculation. This file records only their exact decimal
values; it does not reprove the underlying Type-I/II or Buchstab estimates.
-/

def publishedF1Upper : ℚ := 287 / 10000
def publishedF2Upper : ℚ := 8622 / 100000
def publishedF3Upper : ℚ := 3107 / 100000
def publishedF4Upper : ℚ := 11 / 100000
def publishedF5 : ℚ := 29 / 72
def switchedF6Lower : ℚ := 149403 / 2500000

end Landau
