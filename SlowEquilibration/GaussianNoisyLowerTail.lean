-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuantileLowerTail
public import SlowEquilibration.GaussianQuantileConvolution

/-! Independent scalar Gaussian noise removes atoms without imposing any
regularity on a random variable's distribution. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianNoisyLowerTail
open MeasureTheory ProbabilityTheory Set
open OAI.GaussianPropeller.Quantile
open GaussianQuantileConvolution GaussianQuantileLowerTail
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Symmetry identifies the two one-dimensional Gaussian half-lines. -/
theorem normal_Ici (a : ℝ) : (gaussianReal 0 1).real (Ici a) = Φ (-a) := by
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have h := congrArg (fun ν : Measure ℝ => ν.real (Iic (-a))) hneg
  rw [map_measureReal_apply measurable_neg measurableSet_Iic] at h
  have heq : (fun x : ℝ => -x) ⁻¹' Iic (-a) = Ici a := by ext x; simp
  rw [heq] at h
  exact h.trans (Φ_eq_gaussianReal (-a)).symm

/-- The CDF after adding an independent Gaussian is the Gaussian-smoothed CDF. -/
theorem noisy_cdf (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (s : ℝ) :
    (μ.prod (gaussianReal 0 1)).real {p : Ω × ℝ | F p.1-p.2 ≤ s} =
      ∫ z, Φ (s-F z) ∂μ := by
  have hs : MeasurableSet {p : Ω × ℝ | F p.1-p.2 ≤ s} := by measurability
  rw [← integral_indicator_one hs]
  have hi : Integrable ({p : Ω × ℝ | F p.1-p.2 ≤ s}.indicator
      (1 : Ω × ℝ → ℝ)) (μ.prod (gaussianReal 0 1)) := by
    simpa only [Pi.one_def] using (integrable_const (1 : ℝ)).indicator hs
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact .of_forall fun z => by
    change (∫ r : ℝ, {p : Ω × ℝ | F p.1-p.2 ≤ s}.indicator
      (1 : Ω × ℝ → ℝ) (z,r) ∂gaussianReal 0 1) = Φ (s-F z)
    have heq : (fun r : ℝ => {p : Ω × ℝ | F p.1-p.2 ≤ s}.indicator
        (1 : Ω × ℝ → ℝ) (z,r)) = (Ici (F z-s)).indicator 1 := by
      funext r
      simp only [indicator_apply, mem_ofPred_eq, mem_Ici, Pi.one_apply]
      split_ifs <;> first | rfl | (exfalso; linarith)
    rw [heq, integral_indicator_one measurableSet_Ici, normal_Ici]
    congr 1
    ring

/-- Noise produces a CDF strictly between zero and one at every finite point. -/
theorem noisy_cdf_mem (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (s : ℝ) :
    (μ.prod (gaussianReal 0 1)).real {p : Ω × ℝ | F p.1-p.2 ≤ s} ∈ Ioo (0 : ℝ) 1 := by
  rw [noisy_cdf μ F hF s]
  exact integral_Φ_mem ((measurable_const.sub hF).aestronglyMeasurable)

/-- Adding an independent standard normal preserves the mean. -/
theorem noisy_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF2 : MemLp F 2 μ) :
    (∫ p : Ω × ℝ, (F p.1-p.2) ∂μ.prod (gaussianReal 0 1)) = ∫ z, F z ∂μ := by
  have hi : Integrable F μ := hF2.integrable (by norm_num)
  have hg : Integrable (fun r : ℝ => r) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hsnd : (∫ p : Ω × ℝ, p.2 ∂μ.prod (gaussianReal 0 1)) = 0 := by
    simpa only [probReal_univ, one_smul, integral_id_gaussianReal] using
      (integral_fun_snd (μ := μ) (ν := gaussianReal 0 1) (fun r : ℝ => r))
  rw [integral_sub (hi.comp_fst _) (hg.comp_snd _), integral_fun_fst, hsnd]
  simp only [probReal_univ, one_smul, sub_zero]

/-- The variance increases by exactly one; the original variance is untouched. -/
theorem noisy_variance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF2 : MemLp F 2 μ) :
    variance (fun p : Ω × ℝ => F p.1-p.2) (μ.prod (gaussianReal 0 1)) =
      variance F μ + 1 := by
  have hg : MemLp (fun r : ℝ => -r) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).neg
  have hv : variance (fun r : ℝ => -r) (gaussianReal 0 1) = 1 := by
    calc
      _ = variance (fun r : ℝ => r) (gaussianReal 0 1) := variance_fun_neg
      _ = 1 := variance_fun_id_gaussianReal
  have h := variance_add_prod hF2 hg
  rw [hv] at h
  simpa only [sub_eq_add_neg] using h

/-- The original lower tail is at most twice the noisy lower tail. -/
theorem lower_tail_le_twice_noisy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (v : ℝ) :
    μ.real {z | F z ≤ v} ≤
      2*(μ.prod (gaussianReal 0 1)).real {p : Ω × ℝ | F p.1-p.2 ≤ v} := by
  have hsub : {z | F z ≤ v} ×ˢ Ici (0 : ℝ) ⊆
      {p : Ω × ℝ | F p.1-p.2 ≤ v} := by
    intro p hp
    exact sub_le_iff_le_add.mpr (hp.1.trans (le_add_of_nonneg_right hp.2))
  have h := measureReal_mono (μ := μ.prod (gaussianReal 0 1)) hsub
  rw [measureReal_prod_prod, normal_Ici, neg_zero, Φ_zero] at h
  linarith

/-- A concave smoothed quantile gives the variance-sensitive lower tail.
The sole concavity premise is supplied by smooth Ehrhard for a physical
coefficient log partition in the application. -/
theorem lower_tail_of_concave_smoothed_quantile (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (hF2 : MemLp F 2 μ)
    (hconc : ConcaveOn ℝ univ
      (fun s : ℝ => q (∫ z, Φ (s-F z) ∂μ))) {u : ℝ}
    (hu : 8*Real.sqrt (variance F μ+1) ≤ u) :
    μ.real {z | F z ≤ (∫ z, F z ∂μ)-u} ≤
      Real.exp (-u^2/(64*(variance F μ+1))) := by
  let σ := Real.sqrt (variance F μ+1)
  let ρ := μ.prod (gaussianReal 0 1)
  let X : Ω × ℝ → ℝ := fun p => F p.1-p.2
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by linarith [variance_nonneg F μ])
  have hσsq : σ^2 = variance F μ+1 := Real.sq_sqrt (by linarith [variance_nonneg F μ])
  have hX : Measurable X := (hF.comp measurable_fst).sub measurable_snd
  have hX2 : MemLp X 2 ρ :=
    (hF2.comp_fst _).sub ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_snd _)
  have hvar : variance X ρ = σ^2 := (noisy_variance μ F hF2).trans hσsq.symm
  have hQ : ConcaveOn ℝ univ (fun s : ℝ => q (ρ.real {p | X p ≤ s})) := by
    simpa only [ρ, X, noisy_cdf μ F hF] using hconc
  have htail := cdf_le_exp_of_concave_quantile ρ X hX hX2 (u := u)
    (noisy_cdf_mem μ F hF) hQ hσ hvar (by dsimp [σ] at *; linarith)
  have hmean : (∫ p, X p ∂ρ) = ∫ z, F z ∂μ := noisy_mean μ F hF2
  rw [hmean] at htail
  calc
    _ ≤ 2*ρ.real {p | X p ≤ (∫ z, F z ∂μ)-u} := lower_tail_le_twice_noisy μ F _
    _ ≤ 2*Real.exp (-u^2/(32*σ^2)) := mul_le_mul_of_nonneg_left htail (by norm_num)
    _ ≤ Real.exp (-u^2/(64*σ^2)) := two_mul_exp_variance_bound hσ hu
    _ = _ := by rw [hσsq]

end SlowEquilibration.GaussianNoisyLowerTail
