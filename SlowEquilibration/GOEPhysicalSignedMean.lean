-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEAdjugateJacobiMean
public import SlowEquilibration.GOEPhysicalPotential

/-! Actual signed physical GOE determinant means, including the same-variance
adjacent-dimensional recurrence. All means are ordinary integrals under the
literal coefficient-Gaussian Matrix law. -/
@[expose] public section
namespace SlowEquilibration.GOEPhysicalSignedMean
noncomputable section
open MeasureTheory ProbabilityTheory Filter Function Polynomial
open OAI.CriticalSK GOEAsymptotics GOEScaling GOEExpectedDeterminant
open GOEAdjugateJacobiMean GOESignedAbsoluteTransfer JacobiPrefactors GOELogPotential
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal signed mean in dimension m, at off-diagonal variance b/N. -/
def signedPhysicalMean (m N : ℕ) (b k : ℝ) : ℝ :=
  ∫ W : Matrix (Fin m) (Fin m) ℝ,
    (k • (1 : Matrix (Fin m) (Fin m) ℝ)-W).det ∂SphericalGaussianJet.goeLaw m N b

lemma signedPhysicalMean_eq_meanDet (m : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 ≤ b) (k : ℝ) :
    signedPhysicalMean m N b k=meanDet m (Real.sqrt (b/(2*N))) k := by
  have hN' : (0:ℝ)<N:=by exact_mod_cast hN
  have hs : 2*(Real.sqrt (b/(2*N)))^2=b/N := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ b/(2*(N:ℝ)))]
    field_simp
  have hmap:=goeLaw_bridge m N b (Real.sqrt (b/(2*N))) hs
  have hi:=integral_map (μ:=SphericalGaussianJet.goeLaw m N b)
    (matrixToGaussian_measurable m).aemeasurable
    (shifted_det_measurable m k).aestronglyMeasurable
  rw [hmap] at hi
  exact hi.symm

/-- The physical covariance parameter b/N is exactly the parameter in the
scaled Hermite polynomial, rather than an asymptotic replacement of it. -/
theorem signedPhysicalMean_eq_scaledHermite (m : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 ≤ b) (k : ℝ) :
    signedPhysicalMean m N b k=(scaledHermite (b/N) m).eval k := by
  rw [signedPhysicalMean_eq_meanDet m hN hb k,meanDet_eq_scaledHermite]
  have hs : 2*(Real.sqrt (b/(2*N)))^2=b/N := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ b/(2*(N:ℝ)))]
    field_simp
  rw [hs]

/-- Actual same-variance adjacent means, proved from Gaussian first-row
integration upstream, retain the common ambient normalization N. -/
theorem signedPhysicalMean_three_term (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 ≤ b) (k : ℝ) :
    signedPhysicalMean (n+2) N b k=k*signedPhysicalMean (n+1) N b k-
      (b/N)*(n+1:ℝ)*signedPhysicalMean n N b k := by
  simp only [signedPhysicalMean_eq_scaledHermite _ hN hb k]
  rw [scaledHermite_three_term]
  simp only [eval_sub,eval_mul,eval_X,eval_C]

/-- Ordinary polynomial homogeneity for the exact finite Hermite recurrence. -/
lemma scaledHermite_eval_dilation (n : ℕ) (v k : ℝ) {a : ℝ} (ha : a≠0) :
    (scaledHermite (a^2*v) n).eval k=a^n*(scaledHermite v n).eval (k/a) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [scaledHermite];field_simp
  | more n h0 h1 =>
    rw [scaledHermite_three_term,scaledHermite_three_term]
    simp only [eval_sub,eval_mul,eval_X,eval_C]
    rw [h0,h1]
    simp only [pow_succ]
    field_simp [ha]

lemma signedPhysicalMean_scaling (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) (k : ℝ) :
    signedPhysicalMean (n+1) N b k=(scaleFactor n N b)^(n+1)*
      (∫ A,signedDet n (k/scaleFactor n N b) A
        ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) := by
  have ha:=scaleFactor_pos n hN hb
  have hm : (n+1:ℝ)≠0:=by positivity
  have hvar : b/(N:ℝ)=(scaleFactor n N b)^2*(n+1:ℝ)⁻¹ := by
    rw [scaleFactor_square n hN hb.le]
    field_simp
  rw [signedPhysicalMean_eq_scaledHermite _ hN hb.le k,hvar,
    scaledHermite_eval_dilation _ _ _ ha.ne',standard_signed_mean_eq_hermiteValue]
  rfl

lemma signedPhysicalMean_pos (n : ℕ) {N : ℕ} (hN : 0 < N)
    (hmN : n+1≤N) {b k : ℝ} (hb : 0 < b) (hk : 2*Real.sqrt b<k) :
    0 < signedPhysicalMean (n+1) N b k := by
  have ha:=scaleFactor_pos n hN hb
  have hs : 2<k/scaleFactor n N b := by
    apply (lt_div_iff₀ ha).mpr
    exact (mul_le_mul_of_nonneg_left (scaleFactor_le_sqrt hN hmN hb.le)
      (by norm_num : (0:ℝ)≤2)).trans_lt hk
  rw [signedPhysicalMean_scaling n hN hb k,standard_signed_mean_eq_hermiteValue]
  have hpos : 0 < hermiteValue n (k/scaleFactor n N b) := by
    convert hermiteValue_pos n (show 0 < k/scaleFactor n N b-2 by linarith) using 1
    congr 1
    ring
  exact mul_pos (pow_pos ha _) hpos

/-- Exact same-variance adjacent ratio expressed through the actual Jacobi
resolvent of the smaller dimension. No adjacent-mean limit is assumed. -/
theorem adjacent_signed_mean_ratio_eq_jacobi (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b k : ℝ} (hb : 0 < b) (hk : 2*scaleFactor n N b<k) :
    signedPhysicalMean (n+2) N b k/signedPhysicalMean (n+1) N b k=
      k-scaleFactor n N b*jacobiNormalizedResolvent n (k/scaleFactor n N b-2) := by
  let a:=scaleFactor n N b
  let v:=(n+1:ℝ)⁻¹
  let z:=k/a
  let s:=z-2
  have ha : 0<a:=scaleFactor_pos n hN hb
  have hs : 0<s := by
    have hz:=(lt_div_iff₀ ha).mpr hk
    dsimp only [s,z]
    linarith
  have hz : 2+s=z:=by dsimp only [s];ring
  have hvar : b/(N:ℝ)=a^2*v := by
    dsimp only [a,v]
    rw [scaleFactor_square n hN hb.le]
    field_simp
  have hP : (scaledHermite v (n+1)).eval z≠0:= by
    have hh := hermiteValue_pos n hs
    rw [hz] at hh
    exact hh.ne'
  have hratio:=adjugate_mean_div_signed_mean_eq_jacobi n hs
  rw [normalizedAdjugateTrace_mean,standard_signed_mean_eq_hermiteValue,hz] at hratio
  change (scaledHermite v n).eval z/(scaledHermite v (n+1)).eval z=
    jacobiNormalizedResolvent n s at hratio
  rw [signedPhysicalMean_eq_scaledHermite _ hN hb.le k,
    signedPhysicalMean_eq_scaledHermite _ hN hb.le k,hvar,
    scaledHermite_eval_dilation _ _ _ ha.ne',scaledHermite_eval_dilation _ _ _ ha.ne']
  rw [scaledHermite_three_term]
  simp only [eval_sub,eval_mul,eval_X,eval_C]
  rw [← hratio]
  dsimp only [v,z,s]
  have hn : (n+1:ℝ)≠0:=by positivity
  rw [inv_mul_cancel₀ hn]
  field_simp [ha.ne', hP]
  let P : ℝ := (scaledHermite (1/(n+1:ℝ)) (n+1)).eval (k/a)
  let T : ℝ := (scaledHermite (1/(n+1:ℝ)) n).eval (k/a)
  have hP0 : P≠0 := by simpa only [P,v,z,one_div] using hP
  change a^(n+2)*(k*P-a*T)/P = a*a^(n+1)*(k-T*a/P)
  have haPow : a^(n+2)=a*a^(n+1) := by
    rw [show n+2=(n+1)+1 by omega,pow_succ]
    ring
  rw [haPow]
  field_simp [hP0]

end
end SlowEquilibration.GOEPhysicalSignedMean
