-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalLocalMaxPhysicalIntensity

/-! Genuine exponentially vanishing relative error between ordinary GOE
absolute determinants and determinants restricted to negative Hessians. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GOEMaximumDeterminant
open MeasureTheory ProbabilityTheory Set Filter
open GOEPhysicalNormalizedMoments GOEPhysicalPotential GOERawMoments
open scoped Topology ENNReal
set_option maxHeartbeats 300000

def maximumRelativeError (C b g : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt C*Real.exp (-(n+1 : ℕ)*(g/Real.sqrt b)^2/(32*Real.pi^2))

/-- The excluded determinant weight has its actual exponential relative
bound. This strengthens the old factor-one-half comparison. -/
theorem excluded_determinant_relative_error {b g Z : ℝ} (hb : 0<b) (hg : 0<g) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ k∈Icc (2*Real.sqrt b+g) Z,
      (∫ W in (maximumEvent n k)ᶜ,matrixAbsoluteDet n k W
        ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b) ≤ 
          maximumRelativeError C b g n*physicalMean n (n+2) b k := by
  obtain ⟨C,hC,hmom⟩ := normalized_physical_moments 1 (b := b) (g := g)
    (Z := Z) (r := 2) hb hg (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [nonmaximum_probability_eventually hb hg] with n hn
  intro k hk
  obtain ⟨hD,hm,hM,hMC⟩ := hmom n k hk.1 hk.2
  have hh := determinant_event_holder (SphericalGaussianJet.goeLaw (n+1) (n+2) b)
    (matrixAbsoluteDet n k) hD (ae_of_all _ (fun _ => abs_nonneg _)) hm
    _ (maximumEvent_measurable n k).compl hM hMC (hn k hk.1)
  have hroot : Real.sqrt (Real.exp (-(n+1 : ℕ)*(g/Real.sqrt b)^2/(16*Real.pi^2)))=
      Real.exp (-(n+1 : ℕ)*(g/Real.sqrt b)^2/(32*Real.pi^2)) := by
    have he : Real.exp (-(n+1 : ℕ)*(g/Real.sqrt b)^2/(32*Real.pi^2))^2=
        Real.exp (-(n+1 : ℕ)*(g/Real.sqrt b)^2/(16*Real.pi^2)) := by
      rw [sq,←Real.exp_add]
      congr 1
      ring
    rw [←he,Real.sqrt_sq (Real.exp_pos _).le]
  simp only [Nat.cast_add,Nat.cast_one] at hroot
  rw [hroot] at hh
  simpa only [maximumRelativeError,Nat.cast_add,Nat.cast_one] using (div_le_iff₀ hm).mp hh

/-- The comparison has an error tending to zero, rather than a fixed
positive multiplicative loss. -/
theorem maximumRelativeError_tendsto_zero {b g : ℝ} (hb : 0<b) (hg : 0<g) (C : ℝ) :
    Tendsto (maximumRelativeError C b g) atTop (𝓝 0) := by
  have hs : 0<Real.sqrt b := Real.sqrt_pos.mpr hb
  have ha : 0<(g/Real.sqrt b)^2/(32*Real.pi^2) := by positivity
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop ha)
  convert ht.const_mul (Real.sqrt C) using 1
  · funext n
    unfold maximumRelativeError
    simp only [Function.comp_apply]
    congr 2
    ring
  · simp only [mul_zero]

/-- Both true determinant means are asymptotically identical, uniformly
in every fixed exterior radial interval. -/
theorem maximumMean_relative_error_bounds {b g Z : ℝ} (hb : 0<b) (hg : 0<g) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ k∈Icc (2*Real.sqrt b+g) Z,
      (1-maximumRelativeError C b g n)*physicalMean n (n+2) b k ≤ maximumMean n (n+2) b k ∧
      maximumMean n (n+2) b k ≤ physicalMean n (n+2) b k := by
  obtain ⟨C,hC,herr⟩ := excluded_determinant_relative_error (Z := Z) hb hg
  obtain ⟨M,hM,hmom⟩ := normalized_physical_moments 1 (b := b) (g := g)
    (Z := Z) (r := 2) hb hg (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [herr] with n hn
  intro k hk
  have hD := (hmom n k hk.1 hk.2).1
  have he := integral_add_compl (maximumEvent_measurable n k) hD
  have hbad0 : 0 ≤ ∫ W in (maximumEvent n k)ᶜ,matrixAbsoluteDet n k W
      ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b := integral_nonneg (fun _ => abs_nonneg _)
  have hh := hn k hk
  dsimp only [maximumMean,physicalMean] at *
  constructor <;> nlinarith
end SlowEquilibration.GOEMaximumDeterminant
