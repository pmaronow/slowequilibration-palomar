module
public import FourPapersCommon.GaussianFreeEnergyIBP
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-! A trigonometric smart path has bounded derivatives even at its endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass Filter
open scoped BigOperators Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianSmartPath (A B : E →L[ℝ] EnergySpace N) (t : ℝ) : E →L[ℝ] EnergySpace N :=
  Real.cos t • A + Real.sin t • B

def gaussianSmartPathDeriv (A B : E →L[ℝ] EnergySpace N) (t : ℝ) : E →L[ℝ] EnergySpace N :=
  -Real.sin t • A + Real.cos t • B

theorem hasDerivAt_gaussianSmartPath (A B : E →L[ℝ] EnergySpace N) (t : ℝ) :
    HasDerivAt (gaussianSmartPath A B) (gaussianSmartPathDeriv A B t) t := by
  exact ((Real.hasDerivAt_cos t).smul_const A).add ((Real.hasDerivAt_sin t).smul_const B)

theorem norm_gaussianSmartPathDeriv_le (A B : E →L[ℝ] EnergySpace N) (t : ℝ) :
    ‖gaussianSmartPathDeriv A B t‖ ≤ ‖A‖ + ‖B‖ := by
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  exact add_le_add
    (by simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg A))
    (by simpa using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (norm_nonneg B))

theorem hasDerivAt_integral_gaussianSmartPath {g : Ω → E} (hg : Integrable g)
    (A B : E →L[ℝ] EnergySpace N) (field : EnergySpace N) (t : ℝ) :
    HasDerivAt
      (fun s => ∫ ω, free_energy_density (N := N) (gaussianSmartPath A B s (g ω) + field))
      (∫ ω, fderiv ℝ (free_energy_density (N := N))
        (gaussianSmartPath A B t (g ω) + field) (gaussianSmartPathDeriv A B t (g ω))) t := by
  let F : ℝ → Ω → ℝ := fun s ω =>
    free_energy_density (N := N) (gaussianSmartPath A B s (g ω) + field)
  let F' : ℝ → Ω → ℝ := fun s ω => fderiv ℝ (free_energy_density (N := N))
    (gaussianSmartPath A B s (g ω) + field) (gaussianSmartPathDeriv A B s (g ω))
  let bound : Ω → ℝ := fun ω => (1 / (N : ℝ)) * (‖A‖ + ‖B‖) * ‖g ω‖
  have hgrad : ContDiff ℝ 1 (fderiv ℝ (free_energy_density (N := N))) :=
    (contDiff_free_energy_density (N := N)).fderiv_right
      (m := (1 : WithTop ℕ∞)) (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume := by
    apply Eventually.of_forall
    intro s
    exact (integrable_gaussianFreeEnergy_affine hg (gaussianSmartPath A B s) field).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' t) volume := by
    have hc : ContDiff ℝ 1 (fun x : E => fderiv ℝ (free_energy_density (N := N))
        (gaussianSmartPath A B t x + field) (gaussianSmartPathDeriv A B t x)) :=
      (hgrad.comp ((gaussianSmartPath A B t).contDiff.add contDiff_const)).clm_apply
        (gaussianSmartPathDeriv A B t).contDiff
    exact hc.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hb : ∀ᵐ ω, ∀ s ∈ Set.univ, ‖F' s ω‖ ≤ bound ω := by
    filter_upwards with ω
    intro s _
    rw [Real.norm_eq_abs]
    apply (abs_gaussianFreeEnergy_firstVariation_le _ _).trans
    calc
      (1 / (N : ℝ)) * ‖gaussianSmartPathDeriv A B s (g ω)‖ ≤
          (1 / (N : ℝ)) * (‖gaussianSmartPathDeriv A B s‖ * ‖g ω‖) := by
        gcongr
        exact (gaussianSmartPathDeriv A B s).le_opNorm (g ω)
      _ ≤ bound ω := by
        dsimp [bound]
        rw [mul_assoc]
        gcongr
        exact norm_gaussianSmartPathDeriv_le A B s
  have hd : ∀ᵐ ω, ∀ s ∈ Set.univ, HasDerivAt (fun r => F r ω) (F' s ω) s := by
    filter_upwards with ω
    intro s _
    have hp := ((hasDerivAt_gaussianSmartPath A B s).clm_apply
      (hasDerivAt_const s (g ω))).add_const field
    have hF : HasFDerivAt (free_energy_density (N := N))
        (fderiv ℝ (free_energy_density (N := N)) (gaussianSmartPath A B s (g ω) + field))
        (gaussianSmartPath A B s (g ω) + field) :=
      ((contDiff_free_energy_density (N := N)).differentiable
        (by simp)).differentiableAt.hasFDerivAt
    simpa [F, F', Function.comp_def] using! hF.comp_hasDerivAt s hp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (by simp) hmeas (integrable_gaussianFreeEnergy_affine hg (gaussianSmartPath A B t) field)
    hmeas' hb (hg.norm.const_mul ((1 / (N : ℝ)) * (‖A‖ + ‖B‖))) hd).2

end FourPapersCommon
