-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureUniformFiring

/-! The literal proper-pure cutoff cap hit, averaged over its true uniform
initial spin, is bounded by its physical killed resolvent. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open PhysicalHitting FeynmanKac
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem regular_pure_uniform_cap_hit_le_physical_resolvent {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q B α β : ℝ)
    (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (e : ℝ) (he : |e| ≤ B)
    (u : Vector N) (hu : OnSphere u) (θ : ℝ≥0) (hθ : 0 < θ) (H : ℝ≥0) :
    let T := pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ
    let D := SmoothKilledGeneral.FieldData.ofPure hN p hp c hc Q J u e α χ hχ
    exposureFactor (θ : ℝ) H T *
      (pureSourceCapHitProbability p hp c hc Q α χ hχ β H (J,(u,(e,0))) -
        (gridSize H T : ℝ)*
          (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T : ℝ))))) ≤
      ∫ x, SmoothKilledGeneral.rateLaplace D β (capKilling α u)
        (capKilling_contDiff α u).continuous (capKilling_nonneg α u) θ
        (SmoothKilledGeneral.killingVector D β (capKilling α u)
          (capKilling_contDiff α u).continuous) x ∂sphereLaw N := by
  dsimp only
  let T := pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ
  let D := SmoothKilledGeneral.FieldData.ofPure hN p hp c hc Q J u e α χ hχ
  let σ := sphereLaw N
  let P := VectorBrownian.law N
  let κ := capKilling α u
  let X := fieldUniformProcess D β
  let F : Vector N × VectorBrownian.Space N → ℝ :=
    finiteDiscountedMass κ X (θ : ℝ) (H+T)
  let G : Vector N → ℝ := fun x => ∫ ω, F (x,ω) ∂P
  let hit : Vector N → ℝ :=
    fun x => pureAxisCapHitProbability p hp c hc Q J β α χ hχ e H u x
  let error : ℝ := (gridSize H T : ℝ)*
    (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T : ℝ))))
  let factor := exposureFactor (θ : ℝ) H T
  let : IsProbabilityMeasure σ := sphereLaw_probability N
  have hX := fieldUniformProcess_measurable D β
  have hFsm : StronglyMeasurable F :=
    finiteDiscountedMass_stronglyMeasurable κ
      (capKilling_contDiff α u).continuous.measurable X hX (θ : ℝ) (H+T)
  have hFi : Integrable F (σ.prod P) :=
    Integrable.of_bound hFsm.aestronglyMeasurable ((H+T : ℝ≥0) : ℝ)
      (.of_forall (finiteDiscountedMass_norm_le κ (capKilling_nonneg α u)
        (capKilling_le_one hα u) X θ.coe_nonneg (H+T)))
  have hGi : Integrable G σ := hFi.integral_prod_left
  have hhsm : StronglyMeasurable hit :=
    ((pureAxisCapHitProbability_measurable p hp c hc Q J β α χ hχ e H).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable
  have hhi : Integrable hit σ := by
    apply Integrable.of_bound hhsm.aestronglyMeasurable 1
    exact .of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg
        (pureAxisCapHitProbability_mem_unit p hp c hc Q J β α χ hχ e H u x).1]
      exact (pureAxisCapHitProbability_mem_unit p hp c hc Q J β α χ hχ e H u x).2
  have hLi : Integrable (fun x => factor*(hit x-error)) σ :=
    (hhi.sub (integrable_const error)).const_mul factor
  have hPoint : ∀ᵐ x ∂σ, factor*(hit x-error) ≤ G x := by
    filter_upwards [sphereLaw_support hN] with x hx
    exact regular_pure_axis_cap_hit_exposure hN p hp c hc Q B α β hB hα hβ
      χ hχ J hJ e he u x hu ((onSphere_iff_norm_sq x).mpr hx)
      (θ : ℝ) θ.coe_nonneg H
  have hMean := integral_mono_ae hLi hGi hPoint
  have hLeft : (∫ x, factor*(hit x-error) ∂σ) =
      factor*((∫ x, hit x ∂σ)-error) := by
    rw [integral_const_mul,integral_sub hhi (integrable_const error)]
    simp
  rw [hLeft] at hMean
  have hLaplace := field_uniform_finiteDiscountedMass_le_rateLaplace D β κ
    (capKilling_contDiff α u).continuous (capKilling_nonneg α u)
    (capKilling_le_one hα u) θ hθ (H+T)
  rw [pureSourceCapHitProbability_eq_axisIntegral p hp c hc Q J β α χ hχ e H u]
  exact hMean.trans hLaplace

end SlowEquilibration.ConditionedEntrance
