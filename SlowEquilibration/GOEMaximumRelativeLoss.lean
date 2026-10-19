-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEMaximumDeterminant

@[expose] public section

/-! # Genuine exponentially small determinant loss from nonmaximum Hessians -/
namespace SlowEquilibration.GOEMaximumDeterminant
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open GOERawMoments GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

theorem excluded_determinant_relative_loss {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      (∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
        ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b) ≤
          C*Real.exp (-c*(n+2 : ℕ))*physicalMean n (n+2) b k := by
  obtain ⟨C,hC,hmom⟩ := normalized_physical_moments 1 (b := b) (g := g) (Z := Z)
    (r := 2) hb hg (by norm_num)
  let c : ℝ := (g/Real.sqrt b)^2/(64*Real.pi^2)
  have hc : 0 < c := by dsimp [c];positivity
  refine ⟨Real.sqrt C,c,Real.sqrt_pos.mpr hC,hc,?_⟩
  filter_upwards [nonmaximum_probability_eventually hb hg] with n hprob
  intro k hk
  obtain ⟨hD,hm,hM,hMC⟩ := hmom n k hk.1 hk.2
  have hh := determinant_event_holder (SphericalGaussianJet.goeLaw (n+1) (n+2) b)
    (matrixAbsoluteDet n k) hD (.of_forall fun _ => abs_nonneg _) hm
    _ (maximumEvent_measurable n k).compl hM hMC (hprob k hk.1)
  have hexp : Real.sqrt (Real.exp (-(n+1 : ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2))) ≤
      Real.exp (-c*(n+2 : ℕ)) := by
    rw [Real.sqrt_eq_rpow,← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hN : (n+2 : ℕ) ≤ 2*(n+1 : ℝ) := by push_cast; nlinarith
    have hh := mul_le_mul_of_nonneg_right hN hc.le
    have heq : (-(n+1 : ℝ)*(g/Real.sqrt b)^2/(16*Real.pi^2))*(1/2)=
        -(2*(n+1 : ℝ)*c) := by
      dsimp [c]
      field_simp
      ring
    rw [heq]
    nlinarith [hh]
  have hu := hh.trans (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _))
  exact (div_le_iff₀ hm).mp hu

theorem maximumMean_relative_comparison {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2*Real.sqrt b+g) Z,
      physicalMean n (n+2) b k ≤
        (1+C*Real.exp (-c*(n+2 : ℕ)))*maximumMean n (n+2) b k := by
  obtain ⟨C,c,hC,hc,hloss⟩ := excluded_determinant_relative_loss (Z := Z) hb hg
  refine ⟨2*C,c,by positivity,hc,?_⟩
  filter_upwards [hloss,maximumMean_comparison_eventually (Z := Z) hb hg] with n hn hhalf
  intro k hk
  obtain ⟨D,hD,hmom⟩ := normalized_physical_moments 1 (b := b) (g := g) (Z := Z)
    (r := 2) hb hg (by norm_num)
  have hint := (hmom n k hk.1 hk.2).1
  have he := integral_add_compl (maximumEvent_measurable n k) hint
  change maximumMean n (n+2) b k+
    (∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
      ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b)=physicalMean n (n+2) b k at he
  have hh := (hhalf k hk).1
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*C*Real.exp (-c*(n+2 : ℕ)))
  have hbad := hn k hk
  nlinarith

end
end SlowEquilibration.GOEMaximumDeterminant
