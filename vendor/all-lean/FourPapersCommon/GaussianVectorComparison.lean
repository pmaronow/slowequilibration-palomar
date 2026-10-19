module
public import FourPapersCommon.GaussianComparison

@[expose] public section

/-! The comparison theorem applied to actual independent Gaussian energy vectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass
open scoped BigOperators Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable {N : ℕ}

theorem independent_gaussianFreeEnergy_comparison
    (X Y : Ω → EnergySpace N) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasGaussianLaw X volume) (hY : HasGaussianLaw Y volume)
    (hX0 : ∫ ω, X ω = 0) (hY0 : ∫ ω, Y ω = 0)
    (hXY : IndepFun X Y volume)
    (hdiag : ∀ σ : Config N, (∫ ω, X ω σ * X ω σ) = ∫ ω, Y ω σ * Y ω σ)
    (hcov : ∀ σ τ : Config N, (∫ ω, X ω σ * X ω τ) ≤ ∫ ω, Y ω σ * Y ω τ)
    (field : EnergySpace N) :
    (∫ ω, free_energy_density (N := N) (Y ω + field)) ≤
      ∫ ω, free_energy_density (N := N) (X ω + field) := by
  let E := WithLp 2 (EnergySpace N × EnergySpace N)
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (EnergySpace N) (EnergySpace N)
  let g : Ω → E := fun ω => e.symm (X ω, Y ω)
  have hgm : Measurable g := e.symm.continuous.measurable.comp (hXm.prodMk hYm)
  have hgG : HasGaussianLaw g volume := (hXY.hasGaussianLaw hX hY).map_equiv_fun e.symm
  have hg0 : ∫ ω, g ω = 0 := by
    calc
      (∫ ω, g ω) = e.symm (∫ ω, (X ω, Y ω)) :=
        e.symm.toContinuousLinearMap.integral_comp_comm (hX.integrable.prodMk hY.integrable)
      _ = 0 := by rw [integral_pair hX.integrable hY.integrable, hX0, hY0]; exact map_zero _
  let hg := PhysLean.Probability.GaussianIBP.IsGaussianHilbert.of_hasGaussianLaw g hgm hgG hg0
  let A : E →L[ℝ] EnergySpace N := WithLp.fstL 2 ℝ (EnergySpace N) (EnergySpace N)
  let B : E →L[ℝ] EnergySpace N := WithLp.sndL 2 ℝ (EnergySpace N) (EnergySpace N)
  have hcross (σ τ : Config N) : (∫ ω, A (g ω) σ * B (g ω) τ) = 0 := by
    let Lσ : EnergySpace N →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Config N => ℝ) σ
    let Lτ : EnergySpace N →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Config N => ℝ) τ
    have hmX : (∫ ω, X ω σ) = 0 := by
      simpa [Lσ, hX0] using Lσ.integral_comp_comm hX.integrable
    have hmY : (∫ ω, Y ω τ) = 0 := by
      simpa [Lτ, hY0] using Lτ.integral_comp_comm hY.integrable
    have hh := (hXY.comp Lσ.continuous.measurable Lτ.continuous.measurable).integral_mul_eq_mul_integral
      (Lσ.continuous.measurable.comp hXm).aestronglyMeasurable
        (Lτ.continuous.measurable.comp hYm).aestronglyMeasurable
    change (∫ ω, X ω σ * Y ω τ) = 0
    simpa [Lσ, Lτ, hmX, hmY] using hh
  exact gaussianFreeEnergy_covariance_comparison g hg A B hcross hdiag hcov field

theorem gaussianMeasure_freeEnergy_comparison
    (μ ν : Measure (EnergySpace N)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsGaussian μ] [IsGaussian ν]
    (hμ0 : ∫ x, x ∂μ = 0) (hν0 : ∫ x, x ∂ν = 0)
    (hdiag : ∀ σ : Config N, (∫ x, x σ * x σ ∂μ) = ∫ x, x σ * x σ ∂ν)
    (hcov : ∀ σ τ : Config N, (∫ x, x σ * x τ ∂μ) ≤ ∫ x, x σ * x τ ∂ν)
    (field : EnergySpace N) :
    (∫ x, free_energy_density (N := N) (x + field) ∂ν) ≤
      ∫ x, free_energy_density (N := N) (x + field) ∂μ := by
  letI : MeasureSpace (EnergySpace N × EnergySpace N) := ⟨μ.prod ν⟩
  haveI : IsProbabilityMeasure (volume : Measure (EnergySpace N × EnergySpace N)) := by
    change IsProbabilityMeasure (μ.prod ν)
    infer_instance
  have hfst : HasLaw (Prod.fst : EnergySpace N × EnergySpace N → EnergySpace N) μ volume :=
    measurePreserving_fst.hasLaw
  have hsnd : HasLaw (Prod.snd : EnergySpace N × EnergySpace N → EnergySpace N) ν volume :=
    measurePreserving_snd.hasLaw
  have hmμ : (∫ ω : EnergySpace N × EnergySpace N, ω.1) = 0 := by
    simpa using (hfst.integral_comp aestronglyMeasurable_id).trans hμ0
  have hmν : (∫ ω : EnergySpace N × EnergySpace N, ω.2) = 0 := by
    simpa using (hsnd.integral_comp aestronglyMeasurable_id).trans hν0
  have hiμ (σ τ : Config N) :
      (∫ ω : EnergySpace N × EnergySpace N, ω.1 σ * ω.1 τ) = ∫ x, x σ * x τ ∂μ := by
    simpa only [Function.comp_def] using! hfst.integral_comp
      (f := fun x : EnergySpace N => x σ * x τ) (by fun_prop)
  have hiν (σ τ : Config N) :
      (∫ ω : EnergySpace N × EnergySpace N, ω.2 σ * ω.2 τ) = ∫ x, x σ * x τ ∂ν := by
    simpa only [Function.comp_def] using! hsnd.integral_comp
      (f := fun x : EnergySpace N => x σ * x τ) (by fun_prop)
  have hh := independent_gaussianFreeEnergy_comparison Prod.fst Prod.snd
    measurable_fst measurable_snd hfst.hasGaussianLaw hsnd.hasGaussianLaw hmμ hmν
    (indepFun_prod (μ := μ) (ν := ν) measurable_id measurable_id)
    (by intro σ; rw [hiμ, hiν]; exact hdiag σ)
    (by intro σ τ; rw [hiμ, hiν]; exact hcov σ τ) field
  have hFcts : Continuous (fun x : EnergySpace N => free_energy_density (N := N) (x + field)) :=
    (contDiff_free_energy_density (N := N)).continuous.comp (continuous_id.add continuous_const)
  have hiFμ := hfst.integral_comp hFcts.aestronglyMeasurable
  have hiFν := hsnd.integral_comp hFcts.aestronglyMeasurable
  simp only [Function.comp_def] at hiFμ hiFν
  change (∫ ω : EnergySpace N × EnergySpace N, free_energy_density (N := N) (ω.2 + field)) ≤
    ∫ ω : EnergySpace N × EnergySpace N, free_energy_density (N := N) (ω.1 + field) at hh
  rw [hiFμ, hiFν] at hh
  exact hh

end FourPapersCommon
