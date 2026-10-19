module
public import FourPapersCommon.GaussianVectorComparison

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Centered Gaussian vector laws are invariant under simultaneous sign reversal. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass
namespace FourPapersCommon

theorem centeredGaussian_map_neg {N : ℕ} (μ : Measure (EnergySpace N))
    [IsGaussian μ] (hμ0 : ∫ x, x ∂μ = 0) :
    μ.map (fun x => -x) = μ := by
  let ν := μ.map (fun x => -x)
  haveI : IsGaussian ν := by dsimp [ν]; infer_instance
  have hν0 : ∫ x, x ∂ν = 0 := by
    change (∫ x, id x ∂μ.map (fun x => -x)) = 0
    rw [integral_map_of_stronglyMeasurable measurable_neg stronglyMeasurable_id]
    change (∫ x, -x ∂μ) = 0
    rw [integral_neg, hμ0, neg_zero]
  apply IsGaussian.ext (by simpa only [id_eq] using hν0.trans hμ0.symm)
  ext x y
  rw [covarianceBilin_apply (IsGaussian.memLp_two_id (μ := ν)),
    covarianceBilin_apply (IsGaussian.memLp_two_id (μ := μ))]
  simp only [id_eq]
  rw [hν0, hμ0]
  simp only [sub_zero]
  rw [show ν = μ.map (fun x => -x) from rfl,
    integral_map_of_stronglyMeasurable measurable_neg (by fun_prop)]
  simp

theorem gaussianMeasure_positive_freeEnergy_comparison {N : ℕ}
    (μ ν : Measure (EnergySpace N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsGaussian μ] [IsGaussian ν]
    (hμ0 : ∫ x, x ∂μ = 0) (hν0 : ∫ x, x ∂ν = 0)
    (hdiag : ∀ σ : Config N, (∫ x, x σ * x σ ∂μ) = ∫ x, x σ * x σ ∂ν)
    (hcov : ∀ σ τ : Config N, (∫ x, x σ * x τ ∂μ) ≤ ∫ x, x σ * x τ ∂ν)
    (field : EnergySpace N) :
    (∫ x, free_energy_density (N := N) (-x + field) ∂ν) ≤
      ∫ x, free_energy_density (N := N) (-x + field) ∂μ := by
  have hc : Continuous (fun x : EnergySpace N => free_energy_density (N := N) (x + field)) :=
    (contDiff_free_energy_density (N := N)).continuous.comp (continuous_id.add continuous_const)
  have hi (ρ : Measure (EnergySpace N)) [IsGaussian ρ] (hρ0 : ∫ x, x ∂ρ = 0) :
      (∫ x, free_energy_density (N := N) (-x + field) ∂ρ) =
        ∫ x, free_energy_density (N := N) (x + field) ∂ρ := by
    have hh := integral_map_of_stronglyMeasurable (φ := fun x : EnergySpace N => -x)
      (μ := ρ) measurable_neg hc.stronglyMeasurable
    rw [centeredGaussian_map_neg ρ hρ0] at hh
    exact hh.symm
  rw [hi μ hμ0, hi ν hν0]
  exact gaussianMeasure_freeEnergy_comparison μ ν hμ0 hν0 hdiag hcov field

end FourPapersCommon
