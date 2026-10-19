-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedAdjugateTransfer
public import SlowEquilibration.WeightedTraceMean
public import SlowEquilibration.SignedExponentialNormalizedMoments

/-! Genuine quantitative outside-edge inverse-trace mean bias.
The actual Gaussian concentration, exact adjugate/Jacobi expectation and
actual spectral exceptional event are assembled without a spectral-rate
assumption. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics OAI.CriticalSK GOEClippedDeterminants GOEEdgeConcentration
open GOESignedAbsoluteTransfer GOEAdjugateJacobiMean WeightedTraceMean
open SignedExponentialNormalizedMoments
open scoped NNReal ENNReal Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual trace mean bias before replacing the genuine edge probability
by its proved exponential bound. All shifts above the fixed gap are covered. -/
theorem realizedClippedResolvent_mean_bias_eventually {g ρ : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/2) :
    ∀ᶠ n : ℕ in atTop,∀ s : ℝ,g ≤ s →
    |(∫ A,realizedClippedResolvent n s ρ A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))-semicircleResolvent s| ≤
      Real.sqrt (4*Real.exp (4/(g/2)^2))*Real.sqrt (4*Real.exp (Real.pi^2/(4*ρ^4)))/(n+1:ℝ)+
      2*(ρ⁻¹+(g/2)⁻¹)*Real.exp (2/(g/2)^2)*
        Real.sqrt ((stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))).real (gapBad n g))+
      1/((n+1:ℝ)*s^3) := by
  filter_upwards [signed_absolute_expectations_eventually hg] with n hn
  intro s hs
  let P:=stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))
  let Y:=clippedTrace n (2+s) (g/2)
  let S:=signedDet n (2+s)
  let M:=∫ A,S A ∂P
  let D:=fun A=>S A/M
  let X:=realizedClippedResolvent n s ρ
  let J:=fun A=>normalizedAdjugateTrace n (2+s) A/M
  let U:=fun A=>Real.exp (Y A)/M
  have hSigned:=hn (2+s) (by linarith : 2+g≤2+s)
  have hM : 0 < M:=hSigned.2.1
  have hY : Integrable Y P:=clippedTrace_integrable n (2+s) (by positivity)
  have hG : HasSubgaussianMGF (fun A=>Y A-∫ B,Y B ∂P) (2/(g/2)^2).toNNReal P :=
    GOESharpMoments.clippedTrace_centered_sharpGaussian n (2+s) (by positivity)
  have hdom : ∀ᵐ A ∂P,|S A|≤Real.exp (Y A) :=
    ae_of_all P (fun A=>absoluteDet_le_exp_clippedTrace n (2+s) (by positivity) A)
  have hMom:=normalized_second_moment hY (signedDet_measurable n (2+s)).aemeasurable
    hG hdom hSigned.2.2.1
  have hD : MemLp D 2 P:=hMom.2.1
  have hDsecond : (∫ A,D A^2 ∂P)≤4*Real.exp (4/(g/2)^2) := by
    have he : 2*(2/(g/2)^2)=4/(g/2)^2 := by ring
    simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 2/(g/2)^2),he] using hMom.2.2
  have hDmean : (∫ A,D A ∂P)=1 := by
    unfold D
    rw [integral_div]
    exact div_self hM.ne'
  have hXMeas : Measurable X:=(realizedClippedResolvent_lipschitz n s hρ).continuous.measurable
  have hXbounds (A) : 0 ≤ X A ∧ X A≤ρ⁻¹ := by
    simpa only [X,realizedClippedResolvent,one_div] using clippedResolvent_bounds n s hρ (GOEDeterminantMoments.realization n A)
  have hX : MemLp X 2 P:=MemLp.of_bound hXMeas.aestronglyMeasurable
    (ρ⁻¹) (ae_of_all P (fun A=>by rw [Real.norm_eq_abs,abs_of_nonneg (hXbounds A).1];exact (hXbounds A).2))
  have hVar:=realizedClippedResolvent_centered_square_bound n s hρ
  have hCov:=mean_minus_weighted_mean_bound hD hX hDmean
  have hCovBound : |(∫ A,X A ∂P)-(∫ A,D A*X A ∂P)| ≤
      Real.sqrt (4*Real.exp (4/(g/2)^2))*Real.sqrt (4*Real.exp (Real.pi^2/(4*ρ^4)))/(n+1:ℝ) := by
    calc
      _ ≤ _ :=hCov
      _ ≤ Real.sqrt (4*Real.exp (4/(g/2)^2))*
          Real.sqrt (4*Real.exp (Real.pi^2/(4*ρ^4))/(n+1:ℝ)^2) := by
        exact mul_le_mul (Real.sqrt_le_sqrt hDsecond) (Real.sqrt_le_sqrt hVar.2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _=_ := by
        rw [Real.sqrt_div (by positivity),Real.sqrt_sq (by positivity : 0 ≤ (n+1:ℝ))]
        ring
  have hUi : Integrable U P:=(exponential_integrable hG).div_const M
  have hDXi : Integrable (fun A=>D A*X A) P:=hD.integrable_mul hX
  have hJi : Integrable J P:=(normalizedAdjugateTrace_integrable n (2+s)).div_const M
  have hB : MeasurableSet (gapBad n g):=gapBad_measurable n g
  have hDelta (A : GOEAsymptotics.GaussianMatrix (n+1)) :
      |J A-D A*X A|≤(ρ⁻¹+(g/2)⁻¹)*(gapBad n g).indicator U A := by
    by_cases hA : A ∈ gapBad n g
    · rw [indicator_of_mem hA]
      have hJ : |J A|≤(g/2)⁻¹*U A := by
        change |normalizedAdjugateTrace n (2+s) A/M|≤(g/2)⁻¹*(Real.exp (Y A)/M)
        rw [abs_div,abs_of_pos hM]
        have hh:=div_le_div_of_nonneg_right (normalizedAdjugateTrace_abs_le_clipped n (2+s) (by positivity : 0 < g/2) A) hM.le
        simpa only [Y,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
      have hDabs : |D A|≤U A := by
        change |S A/M|≤Real.exp (Y A)/M
        rw [abs_div,abs_of_pos hM]
        exact div_le_div_of_nonneg_right (absoluteDet_le_exp_clippedTrace n (2+s) (by positivity) A) hM.le
      have hDX : |D A*X A|≤ρ⁻¹*U A := by
        rw [abs_mul,abs_of_nonneg (hXbounds A).1]
        exact (mul_le_mul hDabs (hXbounds A).2 (hXbounds A).1 (by positivity : 0 ≤ U A)).trans_eq (by ring)
      exact (abs_sub _ _).trans (by nlinarith [hJ,hDX])
    · rw [indicator_of_notMem hA]
      have heq:=normalizedAdjugateTrace_eq_det_mul_clipped_of_gap n hg hs hρg A hA
      change |normalizedAdjugateTrace n (2+s) A/M-(S A/M)*X A|≤_ 
      rw [heq]
      have he : signedDet n (2+s) A*realizedClippedResolvent n s ρ A/M-(S A/M)*X A=0 := by
        dsimp only [S,X]
        ring
      rw [he,abs_zero,mul_zero]
  have hRare:=normalized_exponential_on_bad hY hG hSigned.2.2.1 hB
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2/(g/2)^2)] at hRare
  have hWeightedError : |(∫ A,D A*X A ∂P)-(∫ A,J A ∂P)| ≤
      2*(ρ⁻¹+(g/2)⁻¹)*Real.exp (2/(g/2)^2)*Real.sqrt (P.real (gapBad n g)) := by
    have hDI:=hJi.sub hDXi
    have hInt:=integral_mono_ae hDI.abs ((hUi.indicator hB).const_mul (ρ⁻¹+(g/2)⁻¹))
      (ae_of_all P hDelta)
    rw [integral_const_mul,integral_indicator hB] at hInt
    have hnI:=norm_integral_le_integral_norm (μ:=P) (fun A=>J A-D A*X A)
    rw [integral_sub hJi hDXi,Real.norm_eq_abs,abs_sub_comm] at hnI
    have hBound:=hnI.trans hInt
    exact hBound.trans ((mul_le_mul_of_nonneg_left hRare (by positivity : 0 ≤ ρ⁻¹+(g/2)⁻¹)).trans_eq (by ring))
  have hJac:=adjugate_mean_ratio_semicircle_error n (hg.trans_le hs)
  have hJI : (∫ A,J A ∂P)=(∫ A,normalizedAdjugateTrace n (2+s) A ∂P)/M := by
    exact integral_div _ _
  rw [← hJI] at hJac
  exact ((abs_sub_le _ _ _).trans (add_le_add hCovBound
    ((abs_sub_le _ _ _).trans (add_le_add hWeightedError hJac)))).trans_eq (by ring)

end
end SlowEquilibration.GOEClippedResolvent
