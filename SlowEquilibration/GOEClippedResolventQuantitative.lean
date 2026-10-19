-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventMeanBias
public import SlowEquilibration.GOEEdgePolynomialRate
public import SlowEquilibration.QuadraticPerturbation

/-! Actual quantitative clipped GOE outside-edge resolvent rate.
The centered fluctuation, exact Jacobi weighted mean and exponentially rare
actual edge event give a genuine uniform mean-square rate of order 1/N². -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEClippedDeterminants
open GOEEdgePolynomialRate BoundedQuadraticConvergence
open scoped NNReal ENNReal Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def meanBiasConstant (g ρ : ℝ) : ℝ :=
  Real.sqrt (4*Real.exp (4/(g/2)^2))*Real.sqrt (4*Real.exp (Real.pi^2/(4*ρ^4)))+
  2*(ρ⁻¹+(g/2)⁻¹)*Real.exp (2/(g/2)^2)*(32*Real.pi^2/g^2)+1/g^3

lemma meanBiasConstant_nonneg {g ρ : ℝ} (hg : 0 < g) (hρ : 0 < ρ) :
    0 ≤ meanBiasConstant g ρ := by unfold meanBiasConstant;positivity

/-- The genuine actual normalized inverse-trace mean has an all-shift
outside-edge bias of order 1/N, without any rate supplied as a premise. -/
theorem realizedClippedResolvent_uniform_mean_rate {g ρ : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/2) :
    ∀ᶠ n : ℕ in atTop,∀ s : ℝ,g ≤ s →
    |(∫ A,realizedClippedResolvent n s ρ A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))-semicircleResolvent s| ≤
      meanBiasConstant g ρ/(n+1:ℝ) := by
  filter_upwards [realizedClippedResolvent_mean_bias_eventually hg hρ hρg,
    gapBad_sqrt_inverse_dimension_eventually hg] with n hBias hBad
  intro s hs
  have hN : 0 < (n+1:ℝ):=by positivity
  have htail : 1/((n+1:ℝ)*s^3)≤(1/g^3)/(n+1:ℝ) := by
    have hh:=one_div_le_one_div_of_le (mul_pos hN (pow_pos hg 3))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hs 3) hN.le)
    exact hh.trans_eq (by field_simp)
  calc
    _ ≤ _ :=hBias s hs
    _ ≤ Real.sqrt (4*Real.exp (4/(g/2)^2))*Real.sqrt (4*Real.exp (Real.pi^2/(4*ρ^4)))/(n+1:ℝ)+
      2*(ρ⁻¹+(g/2)⁻¹)*Real.exp (2/(g/2)^2)*((32*Real.pi^2/g^2)/(n+1:ℝ))+
      (1/g^3)/(n+1:ℝ) := by
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hBad (by positivity))) htail
    _ = _ := by unfold meanBiasConstant;ring

/-- Genuine Gaussian-realization mean-square rate, uniformly over the
entire positive outside-edge ray. This has no spectral-rate hypothesis. -/
theorem realizedClippedResolvent_uniform_L2_rate {g ρ : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ s : ℝ,g ≤ s →
      (∫ A,(realizedClippedResolvent n s ρ A-semicircleResolvent s)^2
        ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) ≤ C/(n+1:ℝ)^2 := by
  let V:=4*Real.exp (Real.pi^2/(4*ρ^4))
  let B:=meanBiasConstant g ρ
  refine ⟨2*V+2*B^2,by dsimp only [V];positivity,?_⟩
  filter_upwards [realizedClippedResolvent_uniform_mean_rate hg hρ hρg] with n hn
  intro s hs
  let P:=stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))
  let m:=∫ A,realizedClippedResolvent n s ρ A ∂P
  let F:=fun A=>realizedClippedResolvent n s ρ A-semicircleResolvent s
  let G:=fun A=>realizedClippedResolvent n s ρ A-m
  have hMeas:=(realizedClippedResolvent_lipschitz n s hρ).continuous.measurable
  have hR : MemLp (realizedClippedResolvent n s ρ) 2 P :=
    MemLp.of_bound hMeas.aestronglyMeasurable (ρ⁻¹) (ae_of_all P (fun A=>by
      have hh:=clippedResolvent_bounds n s hρ (GOEDeterminantMoments.realization n A)
      change |clippedResolvent n s ρ (GOEDeterminantMoments.realization n A)|≤ρ⁻¹
      rw [abs_of_nonneg hh.1]
      simpa only [one_div] using hh.2))
  have hFMeas : AEStronglyMeasurable F P:=(hMeas.sub_const _).aestronglyMeasurable
  have hF : Integrable (fun A=>F A^2) P:=
    (memLp_two_iff_integrable_sq hFMeas).mp (hR.sub (memLp_const _))
  have hVar:=realizedClippedResolvent_centered_square_bound n s hρ
  have hG : Integrable (fun A=>G A^2) P:=hVar.1
  have hBound:=integral_square_perturbation_bound P F G hF hG
    (K:=|m-semicircleResolvent s|) (abs_nonneg _) (fun A=>by
      change |(realizedClippedResolvent n s ρ A-semicircleResolvent s)-
        (realizedClippedResolvent n s ρ A-m)|≤|m-semicircleResolvent s|
      rw [show (realizedClippedResolvent n s ρ A-semicircleResolvent s)-
        (realizedClippedResolvent n s ρ A-m)=m-semicircleResolvent s by ring])
  have hMean : |m-semicircleResolvent s|^2≤(B/(n+1:ℝ))^2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hn s hs) 2
  calc
    _ ≤ _ :=hBound
    _ ≤ 2*(V/(n+1:ℝ)^2)+2*(B/(n+1:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hVar.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hMean (by norm_num))
    _ = _ := by rw [div_pow];ring

/-- The same actual uniform N^−2 mean-square conclusion under the literal
Matrix GOE law used in the manuscript and posterior Hessian identification. -/
theorem clippedResolvent_uniform_L2_rate {g ρ : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ s : ℝ,g ≤ s →
      (∫ W,(clippedResolvent n s ρ W-semicircleResolvent s)^2
        ∂SphericalGaussianJet.goeLaw (n+1) (n+1) 1) ≤ C/(n+1:ℝ)^2 := by
  obtain ⟨C,hC,h⟩:=realizedClippedResolvent_uniform_L2_rate hg hρ hρg
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with n hn
  intro s hs
  have hm:=GOEDeterminantMoments.realization_measurable n
  have hf : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      (clippedResolvent n s ρ W-semicircleResolvent s)^2):=
    ((clippedResolvent_measurable n s ρ).sub_const _).pow_const 2
  rw [← GOEDeterminantMoments.realization_law n,integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact hn s hs

end
end SlowEquilibration.GOEClippedResolvent
