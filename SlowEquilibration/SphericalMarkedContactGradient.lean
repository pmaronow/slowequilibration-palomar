-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedStrongConcavity

/-! The genuine Fréchet gradient of the actual marked complexity at its
source contact, and uniqueness of its global radial maximizer there. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set TwoAtomStationarity SphericalSequentialRegression
set_option maxHeartbeats 400000

def sourceMarkedGradient (μ : FiniteMixture) (Q e k : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-sourceEnergySlope μ Q e k) • ContinuousLinearMap.fst ℝ ℝ ℝ+
    sourceRadialProfileDerivative μ Q e k • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The actual marked complexity has its genuine two-coordinate Fréchet
derivative throughout the positive exterior spectral region. -/
theorem sourceMarkedComplexity_hasFDerivAt (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    HasFDerivAt (fun z : ℝ × ℝ => sourceRadialProfile μ Q z.1 z.2)
      (sourceMarkedGradient μ Q e k) (e,k) := by
  let A := sourceEnergyCurvature μ Q
  let B := sourceEnergyRadialCross μ Q
  let C := sourceRadialCurvature μ Q
  let s := Real.sqrt (Q^2*μ.xi2 Q)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))
  have hz : 2 < k/s := (lt_div_iff₀ hs).mpr hk
  have hf : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (e,k) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hg : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (e,k) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hq := (((hf.pow 2).const_mul A).add ((hf.mul hg).const_mul (2*B))).add
    ((hg.pow 2).const_mul C)
  let S : (ℝ × ℝ) →L[ℝ] ℝ := s⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hScale : HasFDerivAt (fun z : ℝ × ℝ => z.2/s) S (e,k) := by
    convert S.hasFDerivAt using 1
    funext z
    simp [S,div_eq_mul_inv,mul_comm]
  have hp := (SemicirclePotential.potential_hasDerivAt hz).hasFDerivAt.comp (e,k) hScale
  have hc := ((hasFDerivAt_const
    (1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2) (e,k)).sub (hq.mul_const (1/2 : ℝ))).add hp
  refine (hc.congr_of_eventuallyEq (f₁ := fun z : ℝ × ℝ => sourceRadialProfile μ Q z.1 z.2) ?_).congr_fderiv ?_
  · apply Filter.Eventually.of_forall
    intro z
    change 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
        scoreQuadratic μ Q (scorePairEquiv (z.1,z.2))/2+
        SemicirclePotential.potential (z.2/s)=_
    rw [source_scoreQuadratic_precision_form]
    dsimp [A,B,C,s]
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [sourceMarkedGradient,sourceEnergySlope,sourceEnergyRadialCross,
      sourceRadialProfileDerivative,sourceRadialSlope,A,B,C,s,S,div_eq_mul_inv]
    ring

theorem sourceMarkedGradient_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    sourceMarkedGradient μ Q (markE μ β x Q) (markK μ β Q)=
      (-(β*x)) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
  unfold sourceMarkedGradient
  rw [sourceEnergySlope_at_contact μ h hnp,sourceContact_radial_profile_derivative_zero μ h hnp]
  simp

/-- The full source contact gradient is (-beta*x,0) in the actual energy
and radial coordinates, certified as a genuine Fréchet derivative. -/
theorem sourceContact_markedComplexity_hasFDerivAt (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    HasFDerivAt (fun z : ℝ × ℝ => sourceRadialProfile μ Q z.1 z.2)
      ((-(β*x)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (markE μ β x Q,markK μ β Q) := by
  rw [←sourceMarkedGradient_at_contact μ h hnp]
  exact sourceMarkedComplexity_hasFDerivAt μ h.overlap_range.1 _ _ (sourceContact_markK_above_edge μ h)

/-- The literal source radial mark is the unique global maximizer at the
literal source contact energy, over the entire unrestricted radial line. -/
theorem sourceContact_unique_global_radial_maximizer (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    {k : ℝ} (hk : k ≠ markK μ β Q) :
    sourceRadialProfile μ Q (markE μ β x Q) k <
      sourceRadialProfile μ Q (markE μ β x Q) (markK μ β Q) := by
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  have hLoss := sourceMarkedComplexity_global_loss μ h hnp (markE μ β x Q) k
  have hp : 0 < sourceMarkedLeastCurvature μ Q*(k-markK μ β Q)^2/2 := by
    exact div_pos (mul_pos hκ (sq_pos_of_ne_zero (sub_ne_zero.mpr hk))) (by norm_num)
  rw [sourceContact_radialProfile_zero μ h hnp]
  simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_add] at hLoss
  linarith

end SlowEquilibration.SphericalMarkedWindows
