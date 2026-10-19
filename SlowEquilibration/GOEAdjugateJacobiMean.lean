-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEExpectedDeterminant

/-! Exact determinant-weighted inverse-trace mean of the actual GOE law.
The ordinary adjugate expectation is identified with the Jacobi logarithmic
resolvent, whose finite-dimensional semicircle error is already proved. -/
@[expose] public section
namespace SlowEquilibration.GOEAdjugateJacobiMean
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Polynomial
open GOEAsymptotics OAI.CriticalSK GOEExpectedDeterminant GOESignedAbsoluteTransfer
open JacobiPrefactors GOELogPotential JacobiLogLimit
open scoped NNReal ENNReal Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def normalizedAdjugateTrace (n : ℕ) (k : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  (shifted (n+1) k (symmetrizeGaussianMatrix (goeScale n) A)).adjugate.trace/(n+1)

lemma normalizedAdjugateTrace_integrable (n : ℕ) (k : ℝ) :
    Integrable (normalizedAdjugateTrace n k)
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) := by
  have hi : Integrable (fun B : GOEAsymptotics.GaussianMatrix (n+1)=>
      (shifted (n+1) k B).adjugate.trace) (OAI.CriticalSK.goeLaw (Fin (n+1)) (goeScale n)) := by
    simp only [Matrix.trace,Matrix.diag]
    exact integrable_finsetSum _ (fun i _=>adjugate_diagonal_integrable n (goeScale n) k i)
  have hm:=(symmetrizeGaussianMatrix_continuous (ι:=Fin (n+1)) (goeScale n)).measurable
  have hf : Measurable (fun B : GOEAsymptotics.GaussianMatrix (n+1)=>
      (shifted (n+1) k B).adjugate.trace) := by unfold shifted;fun_prop
  have hmap : (stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))).map
      (symmetrizeGaussianMatrix (goeScale n))=OAI.CriticalSK.goeLaw (Fin (n+1)) (goeScale n) := rfl
  rw [← hmap] at hi
  exact ((integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hi).div_const _

lemma normalizedAdjugateTrace_mean (n : ℕ) (k : ℝ) :
    (∫ A,normalizedAdjugateTrace n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))=
      (scaledHermite (n+1:ℝ)⁻¹ n).eval k := by
  have hm:=(symmetrizeGaussianMatrix_continuous (ι:=Fin (n+1)) (goeScale n)).measurable
  have hf : Measurable (fun B : GOEAsymptotics.GaussianMatrix (n+1)=>
      (shifted (n+1) k B).adjugate.trace) := by unfold shifted;fun_prop
  have hmap : (stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))).map
      (symmetrizeGaussianMatrix (goeScale n))=OAI.CriticalSK.goeLaw (Fin (n+1)) (goeScale n) := rfl
  have hI:=integral_map (μ:=stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))
    hm.aemeasurable hf.aestronglyMeasurable
  rw [hmap,mean_adjugate_trace] at hI
  unfold normalizedAdjugateTrace
  rw [integral_div,← hI,meanDet_eq_scaledHermite,goeScale_square n]
  exact mul_div_cancel_left₀ _ (by positivity : (n+1:ℝ)≠0)

/-- Exact ratio of the two genuine ordinary expectations. No inverse or
spectral asymptotic is assumed for the actual random matrix. -/
theorem adjugate_mean_div_signed_mean_eq_jacobi (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ A,normalizedAdjugateTrace n (2+s) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))/
      (∫ A,signedDet n (2+s) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))=
        jacobiNormalizedResolvent n s := by
  rw [normalizedAdjugateTrace_mean,standard_signed_mean_eq_hermiteValue]
  have hratio:=jacobi_logarithmic_ratio (n:=n+1) hs
  simp only [Nat.cast_add,Nat.cast_one] at hratio
  rw [jacobi_charpoly (by positivity : 0 ≤ (n+1:ℝ)⁻¹) (n+1),
    derivative_scaledHermite_succ,eval_mul,eval_C] at hratio
  rw [← normalized_resolvent_eq_empirical n s] at hratio
  unfold hermiteValue
  have hn : (n+1:ℝ)≠0:=by positivity
  apply (mul_left_cancel₀ hn)
  simpa only [mul_div_assoc] using hratio

/-- True finite-dimensional semicircle error for the actual adjugate mean
ratio, uniform in dimension and valid at every positive shift. -/
theorem adjugate_mean_ratio_semicircle_error (n : ℕ) {s : ℝ} (hs : 0 < s) :
    |(∫ A,normalizedAdjugateTrace n (2+s) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))/
      (∫ A,signedDet n (2+s) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))-
      semicircleResolvent s| ≤ 1/((n+1:ℝ)*s^3) := by
  rw [adjugate_mean_div_signed_mean_eq_jacobi n hs,abs_sub_comm,
    abs_of_nonneg (normalized_resolvent_error_bound n hs).1]
  have h:=(normalized_resolvent_error_bound n hs).2
  rw [show 1/((n+1:ℝ)*s^3)=(1/s^3)/(n+1:ℝ) by field_simp]
  apply (le_div_iff₀ (by positivity : 0 < (n+1:ℝ))).mpr
  simpa only [mul_comm] using h

end
end SlowEquilibration.GOEAdjugateJacobiMean
