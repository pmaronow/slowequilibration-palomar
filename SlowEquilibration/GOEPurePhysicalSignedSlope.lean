-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEPhysicalSignedMean

/-! The exact finite-dimensional signed physical GOE determinant slope.
The local-maximum restriction is treated separately in the pure one-point
intensity argument. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEPurePhysicalSignedSlope
open Polynomial GOEPhysicalSignedMean OAI.CriticalSK GOEScaling
open JacobiPrefactors GOELogPotential
set_option maxHeartbeats 400000

theorem signedPhysicalMean_hasDerivAt (n N : ℕ) (hN : 0 < N)
    {b : ℝ} (hb : 0 ≤ b) (k : ℝ) :
    HasDerivAt (signedPhysicalMean (n+1) N b)
      ((n+1 : ℝ)*signedPhysicalMean n N b k) k := by
  have hp := (scaledHermite (b/N) (n+1)).hasDerivAt k
  rw [derivative_scaledHermite_succ] at hp
  simp only [eval_mul,eval_C] at hp
  convert hp using 1
  · ext t
    exact signedPhysicalMean_eq_scaledHermite (n+1) hN hb t
  · rw [signedPhysicalMean_eq_scaledHermite n hN hb k]

theorem signedPhysicalMean_log_hasDerivAt (n N : ℕ) (hN : 0 < N)
    (hmN : n+1 ≤ N) {b k : ℝ} (hb : 0 < b)
    (hk : 2*Real.sqrt b < k) :
    HasDerivAt (fun t => Real.log (signedPhysicalMean (n+1) N b t))
      ((n+1 : ℝ)*signedPhysicalMean n N b k/
        signedPhysicalMean (n+1) N b k) k := by
  exact (signedPhysicalMean_hasDerivAt n N hN hb.le k).log
    (signedPhysicalMean_pos n hN hmN hb hk).ne'

/-- The source's finite Hermite resolvent is exactly the signed
adjacent-dimensional ratio at the actual covariance scale. -/
theorem signedPhysicalMean_ratio_eq_jacobi (n : ℕ) {N : ℕ}
    (hN : 0 < N) {b k : ℝ} (hb : 0 < b)
    (hk : 2*scaleFactor n N b < k) :
    signedPhysicalMean n N b k/signedPhysicalMean (n+1) N b k =
      jacobiNormalizedResolvent n (k/scaleFactor n N b-2)/
        scaleFactor n N b := by
  let a := scaleFactor n N b
  let A := signedPhysicalMean (n+1) N b k
  let B := signedPhysicalMean n N b k
  let C := signedPhysicalMean (n+2) N b k
  let j := jacobiNormalizedResolvent n (k/a-2)
  have ha : 0 < a := scaleFactor_pos n hN hb
  have hz : 2 < k/a := (lt_div_iff₀ ha).mpr hk
  have hA : 0 < A := by
    dsimp only [A]
    rw [signedPhysicalMean_scaling n hN hb k,
      GOEExpectedDeterminant.standard_signed_mean_eq_hermiteValue]
    have hp : 0 < hermiteValue n (k/a) := by
      convert hermiteValue_pos n (show 0 < k/a-2 by linarith) using 1
      congr 1
      ring
    exact mul_pos (pow_pos ha _) hp
  have ha2 : a^2=(b/N)*(n+1:ℝ) := by
    dsimp only [a]
    rw [scaleFactor_square n hN hb.le]
    field_simp
  have hRec : C=k*A-a^2*B := by
    dsimp only [A,B,C]
    rw [signedPhysicalMean_three_term n hN hb.le k]
    rw [ha2]
  have hRatio : C/A=k-a*j := adjacent_signed_mean_ratio_eq_jacobi n hN hb hk
  have hMain : a*B=j*A := by
    have hR := (div_eq_iff hA.ne').mp hRatio
    rw [hRec] at hR
    have hMul : a*(a*B)=a*(j*A) := by nlinarith [hR]
    exact mul_left_cancel₀ ha.ne' hMul
  apply (div_eq_div_iff hA.ne' ha.ne').mpr
  simpa only [A,B,j,mul_comm] using hMain

/-- The exact finite signed logarithmic slope, before comparing the Hermite
resolvent with its semicircle limit. -/
theorem signedPhysicalMean_log_hasDerivAt_jacobi (n N : ℕ) (hN : 0 < N)
    (hmN : n+1 ≤ N) {b k : ℝ} (hb : 0 < b)
    (hk : 2*Real.sqrt b < k) :
    HasDerivAt (fun t => Real.log (signedPhysicalMean (n+1) N b t))
      ((n+1 : ℝ)/scaleFactor n N b*
        jacobiNormalizedResolvent n (k/scaleFactor n N b-2)) k := by
  have hscale : scaleFactor n N b ≤ Real.sqrt b :=
    scaleFactor_le_sqrt hN hmN hb.le
  have hk' : 2*scaleFactor n N b<k := by linarith
  have hd := signedPhysicalMean_log_hasDerivAt n N hN hmN hb hk
  rw [show ((n+1:ℝ)*signedPhysicalMean n N b k)/
      signedPhysicalMean (n+1) N b k =
      (n+1:ℝ)*(signedPhysicalMean n N b k/
        signedPhysicalMean (n+1) N b k) by ring,
    signedPhysicalMean_ratio_eq_jacobi n hN hb hk'] at hd
  convert hd using 1
  ring

end SlowEquilibration.GOEPurePhysicalSignedSlope
