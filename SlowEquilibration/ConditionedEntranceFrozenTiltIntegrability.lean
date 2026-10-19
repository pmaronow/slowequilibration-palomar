-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceNormalizedTiltIntegrable
public import SlowEquilibration.SphericalGibbs
public import SlowEquilibration.SphericalWeightedCrossAbsorption

/-! Any integrable spin observable remains integrable after multiplication
by a continuous axis–spin factor under the genuine globally tilted source
law. The compact sphere supports supply the needed finite multiplier bound. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem frozen_integrable_mul_under_normalizedTilt
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (w g : Vector N × Vector N → ℝ)
    (hw : Continuous w) (hg : Continuous g)
    {M : ℝ} (hM : 0 < M)
    (Γ : Vector N → ℝ)
    (hΓ : Integrable Γ (gibbsLaw N β H)) :
    Integrable (fun z => g z * Γ z.2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) := by
  let π := gibbsLaw N β H
  let θ := sphereLaw N
  let : IsProbabilityMeasure θ := sphereLaw_probability N
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH
  apply (integrable_normalizedTilt_iff (θ.prod π) w _ hw.measurable hM).2
  have hs : ∀ᵐ z : Vector N × Vector N ∂θ.prod π,
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [gibbsLaw_support hN β H] with x hx
    exact ⟨hu,hx⟩
  let a : Vector N × Vector N → ℝ := fun z => Real.exp (w z) * g z
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      (hw.rexp.mul hg).continuousOn
  have hb : ∀ᵐ z ∂θ.prod π, ‖a z‖ ≤ C := by
    filter_upwards [hs] with z hz
    apply hC
    constructor
    · simp only [mem_closedBall,dist_zero_right]
      rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
    · simp only [mem_closedBall,dist_zero_right]
      rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]
  have hi : Integrable (fun z => a z * Γ z.2) (θ.prod π) :=
    (hΓ.comp_snd θ).bdd_mul (hw.rexp.mul hg).aestronglyMeasurable hb
  exact hi.congr (Filter.Eventually.of_forall (fun z => by
    change a z * Γ z.2 = Real.exp (w z) * (g z * Γ z.2)
    ring))

/-- Both physical defect square integrands are L¹ under the global tilt
for any single frozen-axis completed reference representative. -/
theorem frozen_reference_defect_moments_integrable
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (w : Vector N × Vector N → ℝ) (hw : Continuous w)
    {M : ℝ} (hM : 0 < M)
    (F : Vector N × Vector N → ℝ)
    (GF : (Fin N × Fin N) → Vector N × Vector N → ℝ)
    (hFrozenF : ∀ u v x, F (u,x) = F (v,x))
    (hFrozenGF : ∀ ij u v x, GF ij (u,x) = GF ij (v,x))
    (F₀ : sphericalSobolevGraph hN β H hH)
    (hF : (fun x => F (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.fst)
    (hGF : ∀ ij, (fun x => GF ij (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.snd ij)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β H, 1 ≤ F₀.val.fst x)
    (hFint : Integrable (fun x => F (0,x)) (gibbsLaw N β H)) :
    Integrable (fun z => (tiltDefect w z)^2 * (F z-1))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) ∧
    Integrable (fun z => (tiltDefect w z)^2 *
      (∑ ij : Fin N × Fin N, (GF ij z)^2 / F z))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) := by
  let π := gibbsLaw N β H
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH
  let g : Vector N × Vector N → ℝ := fun z => (tiltDefect w z)^2
  have hg : Continuous g := by
    unfold g tiltDefect
    fun_prop
  let Γ₀ : Vector N → ℝ := fun x => F (0,x)-1
  have hΓ₀ : Integrable Γ₀ π := hFint.sub (integrable_const 1)
  have hI₀ := frozen_integrable_mul_under_normalizedTilt hN β H hH w g hw hg
    hM Γ₀ hΓ₀
  have hIe₀ : (fun z : Vector N × Vector N => g z * Γ₀ z.2) =
      (fun z => (tiltDefect w z)^2 * (F z-1)) := by
    funext z
    dsimp only [g,Γ₀]
    rw [hFrozenF z.1 0 z.2]
  have hCoordAe (ij : Fin N × Fin N) :
      (fun x => (GF ij (0,x))^2 / F (0,x)) =ᵐ[π]
        (fun x => (F₀.val.snd ij x)^2 * (F₀.val.fst x)⁻¹) := by
    filter_upwards [hF,hGF ij] with x hf hg
    simp only [hf,hg,div_eq_mul_inv]
  have hCoordInt (ij : Fin N × Fin N) :
      Integrable (fun x => (GF ij (0,x))^2 / F (0,x)) π :=
    (sphericalFisher_coordinate_integrable hN β H hH F₀ hFlo ij).congr
      (hCoordAe ij).symm
  let Γ₁ : Vector N → ℝ := fun x =>
    ∑ ij : Fin N × Fin N, (GF ij (0,x))^2 / F (0,x)
  have hΓ₁ : Integrable Γ₁ π :=
    integrable_finsetSum Finset.univ (fun ij _ => hCoordInt ij)
  have hI₁ := frozen_integrable_mul_under_normalizedTilt hN β H hH w g hw hg
    hM Γ₁ hΓ₁
  have hIe₁ : (fun z : Vector N × Vector N => g z * Γ₁ z.2) =
      (fun z => (tiltDefect w z)^2 *
        (∑ ij : Fin N × Fin N, (GF ij z)^2 / F z)) := by
    funext z
    dsimp only [g,Γ₁]
    congr 1
    apply Finset.sum_congr rfl
    intro ij _
    rw [hFrozenF z.1 0 z.2,hFrozenGF ij z.1 0 z.2]
  exact ⟨hIe₀ ▸ hI₀, hIe₁ ▸ hI₁⟩

end SlowEquilibration.ConditionedEntrance
