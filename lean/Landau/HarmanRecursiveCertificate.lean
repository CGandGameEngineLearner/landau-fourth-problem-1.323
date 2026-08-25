import Landau.HarmanIntegerRounding
import Landau.HarmanRecursiveEndpoint

namespace Landau

/-!
# Kernel-checked recursive Harman certificate

This module independently recomputes the integer algorithm in
`scripts/certify_harman_recursive_tail.cpp` and
`scripts/audit_harman_recursive_tail.py`.  Besides the original three-step
Type-II contribution it includes

* the rational lower-linear-sieve envelope in the three-prime term; and
* a lower bound for the omitted `tau < beta₁ < alpha-1` branch, with one
  recursively improved child upper bound.

Only natural-number arithmetic is used. The primitive outward-rounding
lemmas are provided by `HarmanIntegerRounding`.
-/

structure WeightedInterval where
  lo : Nat
  hi : Nat
  weight : Nat
deriving DecidableEq, Repr

def addWeightedClipped (lo hi weight domainLo domainHi : Nat)
    (xs : List WeightedInterval) : List WeightedInterval :=
  let lo' := max lo domainLo
  let hi' := min hi domainHi
  if lo' < hi' ∧ 0 < weight then
    { lo := lo', hi := hi', weight := weight } :: xs
  else xs

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

def sortNats (xs : List Nat) : List Nat := xs.foldr insertNat []

def maxCoveringWeight (xs : List WeightedInterval) (lo hi : Nat) : Nat :=
  xs.foldl (fun answer x =>
    if x.lo ≤ lo ∧ hi ≤ x.hi then max answer x.weight else answer) 0

def weightedSegmentsLower (xs : List WeightedInterval) (den current : Nat) :
    List Nat → Nat
  | [] => 0
  | next :: rest =>
      let weight := maxCoveringWeight xs current next
      let component :=
        if 0 < current ∧ current < next ∧ 0 < weight then
          mulDown (floorScaled den current - ceilScaled den next) weight
        else 0
      component + weightedSegmentsLower xs den next rest

/-- Lower fixed-point sum for the pointwise maximum of finitely many
weighted reciprocal-square intervals.  Repeated endpoints are harmless. -/
def weightedReciprocalLower (xs : List WeightedInterval) (den : Nat) : Nat :=
  let endpoints := sortNats (xs.flatMap fun x => [x.lo, x.hi])
  match endpoints with
  | [] => 0
  | first :: rest => weightedSegmentsLower xs den first rest

structure SieveThreshold where
  p : Nat
  q : Nat
  weight : Nat
deriving DecidableEq, Repr

def thresholdPairs : List (Nat × Nat) :=
  [(201, 100), (21, 10), (11, 5), (23, 10), (12, 5), (5, 2),
   (13, 5), (27, 10), (14, 5), (29, 10), (3, 1), (31, 10),
   (16, 5), (33, 10), (17, 5), (7, 2), (18, 5), (37, 10),
   (19, 5), (39, 10), (4, 1)]

def sieveThresholds : List SieveThreshold :=
  thresholdPairs.map fun pq =>
    { p := pq.1
      q := pq.2
      weight := floorScaled (4 * (pq.1 - 2 * pq.2) * pq.2)
        (pq.1 * pq.1) }

structure ExponentCell where
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr

/-- Uniform Type-II intervals and nested rational lower-sieve intervals for
the third selected prime. -/
def thirdPrimeLowerIntervals (b1 b2 : ExponentCell)
    (domainLo domainHi aMax sigmaMin half : Nat) : List WeightedInterval :=
  let initial :=
    if aMax ≤ b1.lo + b2.lo ∧ b1.hi + b2.hi ≤ sigmaMin then
      addWeightedClipped domainLo domainHi omegaLower domainLo domainHi []
    else
      let xs := addWeightedClipped (aMax - b1.lo) (sigmaMin - b1.hi)
        omegaLower domainLo domainHi []
      let xs := addWeightedClipped (aMax - b2.lo) (sigmaMin - b2.hi)
        omegaLower domainLo domainHi xs
      addWeightedClipped (aMax - b1.lo - b2.lo)
        (sigmaMin - b1.hi - b2.hi) omegaLower domainLo domainHi xs
  let residual := half - b1.hi - b2.hi
  sieveThresholds.foldl (fun xs threshold =>
    let upper := threshold.q * residual / (threshold.p + threshold.q)
    addWeightedClipped domainLo upper threshold.weight domainLo domainHi xs)
    initial

structure RecursiveAlphaBounds where
  alphaLo : Nat
  alphaHi : Nat
  gammaMin : Nat
  gammaMax : Nat
  tauMax : Nat
  aMin : Nat
  aMax : Nat
  sigmaMin : Nat
  xiMin : Nat
deriving DecidableEq, Repr

def recursiveAlphaBounds (i n : Nat) : RecursiveAlphaBounds :=
  let loNum := 14 * n + i
  let hiNum := loNum + 1
  { alphaLo := floorScaled loNum (12 * n)
    alphaHi := ceilScaled hiNum (12 * n)
    gammaMin := floorScaled (60 * n - 4 * hiNum) (36 * n)
    gammaMax := ceilScaled (60 * n - 4 * loNum) (36 * n)
    tauMax := ceilScaled (18 * n - loNum) (24 * n)
    aMin := floorScaled (loNum - 12 * n) (12 * n)
    aMax := ceilScaled (hiNum - 12 * n) (12 * n)
    sigmaMin := floorScaled (24 * n - hiNum) (36 * n)
    xiMin := floorScaled (18 * n - hiNum) (12 * n) }

def equalExponentCell (lo hi i steps : Nat) : ExponentCell :=
  let width := hi - lo
  { lo := lo + width * i / steps
    hi := lo + width * (i + 1) / steps }

/-- Upper bound for one two-prime child.  `none` means that the coarse box
does not leave a positive Type-I level. -/
def pairChildUpper (ab : RecursiveAlphaBounds)
    (b1 b2 : ExponentCell) : Option Nat :=
  if 0 < b2.lo ∧ b2.lo < b2.hi then
    let selectedHi := b1.hi + b2.hi
    let deltaMin := scale / 2 - selectedHi
    if deltaMin = 0 then none
    else
      let byDelta := ceilScaled (2 * scale) deltaMin
      let byBeta := ceilScaled (2 * scale) (3 * b2.lo)
      let direct := max byDelta byBeta
      if ab.aMax ≤ b1.lo + b2.lo ∧ b1.hi + b2.hi ≤ ab.sigmaMin then
        some (min direct (ceilScaled omegaUpper b2.lo))
      else if selectedHi ≤ ab.xiMin ∧ 0 < ab.gammaMin ∧ ab.gammaMax < b2.lo then
        let intervals := thirdPrimeLowerIntervals b1 b2 ab.gammaMax b2.lo
          ab.aMax ab.sigmaMin (scale / 2)
        let childrenLower := weightedReciprocalLower intervals scale
        let baseUpper := ceilScaled omegaUpper ab.gammaMin
        if childrenLower ≤ baseUpper then
          some (min direct (baseUpper - childrenLower))
        else some direct
      else some direct
  else none

def recursiveTailLower (ab : RecursiveAlphaBounds) (steps : Nat) : Nat :=
  if 0 < ab.gammaMin ∧ ab.tauMax < ab.aMin then
    (List.range steps).foldl (fun total i1 =>
      let b1 := equalExponentCell ab.tauMax ab.aMin i1 steps
      if 0 < b1.lo ∧ b1.lo < b1.hi then
        let baseLower := floorScaled omegaLower ab.gammaMax
        let children : Option Nat := (List.range steps).foldl (fun answer i2 =>
          match answer with
          | none => none
          | some subtotal =>
              let b2 := equalExponentCell ab.gammaMin b1.hi i2 steps
              match pairChildUpper ab b1 b2 with
              | none => none
              | some upper =>
                  let logUpper := ceilScaled (b2.hi - b2.lo) b2.lo
                  some (subtotal + mulUp upper logUpper)) (some 0)
        match children with
        | none => total
        | some childrenUpper =>
            if childrenUpper < baseLower then
              let nodeLower := baseLower - childrenUpper
              let logLower := floorScaled (b1.hi - b1.lo) b1.hi
              total + mulDown (mulDown ab.alphaLo nodeLower) logLower
            else total
      else total) 0
  else 0

def weightedRowBoxSum (n b i den i1 : Nat) : Nat :=
  let b1 : ExponentCell :=
    { lo := commonBetaNum n b i i1
      hi := commonBetaNum n b i (i1 + 1) }
  (List.range (i1 - 1)).foldl (fun total j =>
    let i2 := j + 1
    let b2 : ExponentCell :=
      { lo := commonBetaNum n b i i2
        hi := commonBetaNum n b i (i2 + 1) }
    let intervals := thirdPrimeLowerIntervals b1 b2
      (commonBetaNum n b i 0) b2.lo
      ((2 * n + i + 1) * 6 * b) ((10 * n - i - 1) * 2 * b) (den / 2)
    let beta3Lower := weightedReciprocalLower intervals den
    let reciprocalB1B2 := floorScaled (den * den) (b1.hi * b2.hi)
    total + mulDown beta3Lower reciprocalB1B2) 0

def weightedTripleLower (n b i den commonWidthLower : Nat) : Nat :=
  let widthSquare := mulDown commonWidthLower commonWidthLower
  (List.range (b - 1)).foldl (fun total j =>
    let i1 := j + 1
    total + mulDown widthSquare (weightedRowBoxSum n b i den i1)) 0

structure RecursiveCellData where
  saving : Nat
  tail : Nat
  a3 : Nat
deriving DecidableEq, Repr

def recursiveCellData (n b tailSteps i : Nat) : RecursiveCellData :=
  let alphaLoNum := 14 * n + i
  let alphaHiNum := alphaLoNum + 1
  if 122 * 12 * n ≤ 100 * alphaLoNum ∨ n ≤ i + 1 then
    { saving := 0, tail := 0, a3 := 0 }
  else
    let den := 72 * n * b
    let commonWidthNum := 4 * n + 5 * i - 3
    if commonWidthNum = 0 then
      { saving := 0, tail := 0, a3 := 0 }
    else
      let alphaGammaUpper := ceilScaled (3 * alphaHiNum) (4 * (n - i - 1))
      let a0Upper := mulUp omegaUpper alphaGammaUpper
      let commonLogLower := (List.range b).foldl (fun total k =>
        total + floorScaled commonWidthNum (commonBetaNum n b i (k + 1))) 0
      let alphaGammaLower := floorScaled (3 * alphaLoNum) (4 * (n - i))
      let a1Lower := mulDown (mulDown omegaLower alphaGammaLower) commonLogLower
      let containingWidthNum := 4 * n + 5 * i + 8
      let containingLogUpper := (List.range b).foldl (fun total k =>
        total + ceilScaled containingWidthNum (containingBetaNum n b i k)) 0
      let logSquareUpper := mulUp containingLogUpper containingLogUpper
      let a2Upper :=
        (mulUp (mulUp omegaUpper alphaGammaUpper) logSquareUpper + 1) / 2
      let commonWidthLower := floorScaled commonWidthNum den
      let triple := weightedTripleLower n b i den commonWidthLower
      let alphaLo := floorScaled alphaLoNum (12 * n)
      let a3Lower := mulDown alphaLo triple
      let tailLower := recursiveTailLower (recursiveAlphaBounds i n) tailSteps
      let linearLower := floorScaled (4 * alphaLoNum) (12 * n)
      { saving := linearLower + a1Lower + a3Lower + tailLower -
          (a0Upper + a2Upper)
        tail := tailLower
        a3 := a3Lower }

structure RecursiveCertificateData where
  savingSum : Nat
  tailSum : Nat
  a3Sum : Nat
  positive : Nat
deriving DecidableEq, Repr

def recursiveCertificateData (n b tailSteps : Nat) : RecursiveCertificateData :=
  (List.range n).foldl (fun data i =>
    let cell := recursiveCellData n b tailSteps i
    { savingSum := data.savingSum + cell.saving
      tailSum := data.tailSum + cell.tail
      a3Sum := data.a3Sum + cell.a3
      positive := data.positive + if 0 < cell.saving then 1 else 0 })
    { savingSum := 0, tailSum := 0, a3Sum := 0, positive := 0 }

/-- Certificate data on the consecutive alpha indices
`start, ..., start+count-1`.  The canonical computation is split into four
such blocks so each kernel reduction remains cacheable and memory-bounded. -/
def recursiveCertificateDataRange
    (n b tailSteps start count : Nat) : RecursiveCertificateData :=
  (List.range count).foldl (fun data j =>
    let cell := recursiveCellData n b tailSteps (start + j)
    { savingSum := data.savingSum + cell.saving
      tailSum := data.tailSum + cell.tail
      a3Sum := data.a3Sum + cell.a3
      positive := data.positive + if 0 < cell.saving then 1 else 0 })
    { savingSum := 0, tailSum := 0, a3Sum := 0, positive := 0 }

def addRecursiveCertificateData
    (x y : RecursiveCertificateData) : RecursiveCertificateData :=
  { savingSum := x.savingSum + y.savingSum
    tailSum := x.tailSum + y.tailSum
    a3Sum := x.a3Sum + y.a3Sum
    positive := x.positive + y.positive }

def recursiveCertificateSaving (n b tailSteps : Nat) : Nat :=
  (recursiveCertificateData n b tailSteps).savingSum / (12 * n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem recursive_certificate_small_data :
    recursiveCertificateData 60 20 15 =
      { savingSum := 6391666702852
        tailSum := 6261702215591
        a3Sum := 25729812106832
        positive := 17 } := by
  native_decide

end Landau
