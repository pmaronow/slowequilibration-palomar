-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventLipschitz
public import SlowEquilibration.GOEClippedDeterminants
public import SlowEquilibration.SubGaussianSecondMoment

/-! Quantitative actual centered clipped GOE inverse-trace fluctuations.
The normalized trace is Frobenius Lipschitz with constant of order 1/N;
its genuine Gaussian concentration gives square fluctuation of order 1/N². -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open GOEAsymptotics OAI.CriticalSK GOEClippedDeterminants SpectralTraceLipschitz GOEEdgeConcentration
open scoped NNReal ENNReal Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def realizedClippedResolvent (n : ℕ) (s ρ : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  clippedResolvent n s ρ (GOEDeterminantMoments.realization n A)

def resolventLip (n : ℕ) (ρ : ℝ) : ℝ≥0 :=
  clippedLip n (ρ^2)/(n+1)

lemma inverse_spectral_function_lipschitz (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith (1/ρ^2).toNNReal (fun z : ℝ=>(max ρ (k-z))⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [Real.dist_eq,Real.coe_toNNReal _ (by positivity : 0 ≤ 1/ρ^2)]
  have h:=clipped_inverse_lipschitz hρ (k-a) (k-b)
  rw [show k-a-(k-b)=-(a-b) by ring,abs_neg] at h
  simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using h

lemma realizedClippedResolvent_lipschitz (n : ℕ) (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith (resolventLip n ρ) (realizedClippedResolvent n s ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  have h:=spectral_trace_difference
    (symmetrizeGaussianMatrix (goeScale n) A) (symmetrizeGaussianMatrix (goeScale n) B)
    (symmetrize_symmetric _ _) (symmetrize_symmetric _ _)
    (fun z : ℝ=>(max ρ (2+s-z))⁻¹) (inverse_spectral_function_lipschitz (2+s) hρ)
  have hh:=h.trans (mul_le_mul_of_nonneg_left
    (GOEDeterminantMoments.symmetrize_difference_norm (goeScale n) A B) (by positivity))
  change |realizedClippedResolvent n s ρ A-realizedClippedResolvent n s ρ B| ≤
    (resolventLip n ρ:ℝ)*‖A-B‖
  have heig (C : GOEAsymptotics.GaussianMatrix (n+1)) :
      eigenvalues n (GOEDeterminantMoments.realization n C)=realizedEigenvalues n C := by
    unfold eigenvalues GOEDeterminantMoments.realization realizedEigenvalues
    rw [matrixToGaussian_gaussianToMatrix]
  unfold realizedClippedResolvent clippedResolvent
  rw [heig A,heig B,← sub_div,abs_div,abs_of_pos (by positivity : 0 < (n+1:ℝ))]
  apply (div_le_iff₀ (by positivity : 0 < (n+1:ℝ))).mpr
  convert hh using 1
  · rfl
  · change ((Real.sqrt (n+1:ℝ)*(1/|ρ^2|)*(2*|goeScale n|))/(n+1:ℝ))*‖A-B‖*(n+1:ℝ)=_
    rw [abs_of_nonneg (sq_nonneg ρ),Real.coe_toNNReal _ (by positivity)]
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    field_simp

lemma resolventLip_square (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (resolventLip n ρ:ℝ)^2=2/(ρ^4*(n+1:ℝ)^2) := by
  simp only [resolventLip,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
    div_pow,clippedLip_square n (sq_pos_of_pos hρ)]
  field_simp

/-- The actual normalized clipped inverse trace has a genuine centered MGF
with parameter proportional to 1/N² at every dimension and shift. -/
theorem realizedClippedResolvent_centered_subGaussian (n : ℕ) (s : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    HasSubgaussianMGF (fun A=>realizedClippedResolvent n s ρ A-
        ∫ B,realizedClippedResolvent n s ρ B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))
      (Real.pi^2/(2*ρ^4*(n+1:ℝ)^2)).toNNReal
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) := by
  have h:=SphericalAging.GaussianLipschitzConcentration.centered_hasSubgaussianMGF _
    (realizedClippedResolvent_lipschitz n s hρ)
  have hc : SphericalAging.GaussianSmoothConcentration.rotationConstant (resolventLip n ρ)=
      (Real.pi^2/(2*ρ^4*(n+1:ℝ)^2)).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    change (Real.pi/2)^2*(resolventLip n ρ:ℝ)^2=_
    rw [resolventLip_square n hρ]
    field_simp
  rwa [hc] at h

/-- Genuine normalized-trace centered mean square, with no moment premise. -/
theorem realizedClippedResolvent_centered_square_bound (n : ℕ) (s : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun A=>(realizedClippedResolvent n s ρ A-
      ∫ B,realizedClippedResolvent n s ρ B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))^2)
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) ∧
    (∫ A,(realizedClippedResolvent n s ρ A-
      ∫ B,realizedClippedResolvent n s ρ B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))^2
      ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) ≤
      4*Real.exp (Real.pi^2/(4*ρ^4))/(n+1:ℝ)^2 := by
  have h:=SubGaussianSecondMoment.square_integral_le
    (realizedClippedResolvent_centered_subGaussian n s hρ)
    (t:=(n+1:ℝ)) (by positivity)
  refine ⟨h.1,h.2.trans_eq ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  have hn : (n+1:ℝ)≠0:=by positivity
  have he : (Real.pi^2/(2*ρ^4*(n+1:ℝ)^2))*(n+1:ℝ)^2/2=Real.pi^2/(4*ρ^4) := by
    field_simp
    ring
  rw [he]

/-- The same genuine centered mean-square rate under the manuscript's
literal symmetric Matrix GOE law. -/
theorem clippedResolvent_centered_square_bound (n : ℕ) (s : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun W=>(clippedResolvent n s ρ W-
      ∫ V,clippedResolvent n s ρ V ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)^2)
      (SphericalGaussianJet.goeLaw (n+1) (n+1) 1) ∧
    (∫ W,(clippedResolvent n s ρ W-
      ∫ V,clippedResolvent n s ρ V ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)^2
      ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1) ≤
      4*Real.exp (Real.pi^2/(4*ρ^4))/(n+1:ℝ)^2 := by
  have hm:=GOEDeterminantMoments.realization_measurable n
  have hr:=clippedResolvent_measurable n s ρ
  have hmean : (∫ V,clippedResolvent n s ρ V ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1)=
      ∫ B,realizedClippedResolvent n s ρ B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)) := by
    rw [← GOEDeterminantMoments.realization_law n,integral_map hm.aemeasurable hr.aestronglyMeasurable]
    rfl
  have h:=realizedClippedResolvent_centered_square_bound n s hρ
  have hf : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      (clippedResolvent n s ρ W-∫ B,realizedClippedResolvent n s ρ B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))^2)
      := ((hr.sub_const _).pow_const 2)
  rw [hmean,← GOEDeterminantMoments.realization_law n]
  constructor
  · exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr h.1
  · rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
    exact h.2

end
end SlowEquilibration.GOEClippedResolvent
