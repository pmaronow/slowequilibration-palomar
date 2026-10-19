-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureUniformCapHitResolvent
public import SlowEquilibration.ConditionedEntrancePureUniformResolventTransferAny

/-! The actual pure cap exposure is integrated over its uniform axis and spin,
using the same measurable killed resolvent as the energy calculation. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral PhysicalHitting
open SphericalAging HardSphereDynamics SphericalOverlapExponential
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_joint_uniform_cap_hit_le_physical_resolvent
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (Q B α β : ℝ) (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (θ : ℝ≥0) (hθ : 0 < θ)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (e : ℝ) (he : |e| ≤ B)
    (U : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (hUsm : StronglyMeasurable U)
    (hPhysical : ∀ u : Vector N, OnSphere u →
      let D := FieldData.ofPure hN d hd c hc Q J u e α χ hχ
      (fun x => U ((J,(u,(e,0))),x)) =ᵐ[gibbsLaw N β D.hamiltonian]
        rateLaplace D β (capKilling α u) (capKilling_contDiff α u).continuous
          (capKilling_nonneg α u) θ
          (killingVector D β (capKilling α u) (capKilling_contDiff α u).continuous))
    (H : ℝ≥0) :
    let T := pureSourceShortCell d hd c hc Q B α β hB hα hβ χ hχ
    exposureFactor (θ : ℝ) H T *
      ((∫ u, pureSourceCapHitProbability d hd c hc Q α χ hχ β H (J,(u,(e,0)))
        ∂sphereLaw N) - (gridSize H T : ℝ)*
          (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T : ℝ))))) ≤
      ∫ u, ∫ x, U ((J,(u,(e,0))),x) ∂sphereLaw N ∂sphereLaw N := by
  dsimp only
  let σ := sphereLaw N
  let T := pureSourceShortCell d hd c hc Q B α β hB hα hβ χ hχ
  let Ua : Vector N × Vector N → ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
  let hit : Vector N → ℝ := fun u =>
    pureSourceCapHitProbability d hd c hc Q α χ hχ β H (J,(u,(e,0)))
  let error : ℝ := (gridSize H T : ℝ)*
    (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T : ℝ))))
  let factor := exposureFactor (θ : ℝ) H T
  let : IsProbabilityMeasure σ := sphereLaw_probability N
  have hUaSm : StronglyMeasurable Ua := hUsm.comp_measurable (by fun_prop)
  have hUnit (u : Vector N) (hu : OnSphere u) :
      ∀ᵐ x ∂σ, 0 ≤ Ua (u,x) ∧ Ua (u,x) ≤ 1 := by
    let D := FieldData.ofPure hN d hd c hc Q J u e α χ hχ
    have hκ1 : ∀ x, ‖capKilling α u x‖ ≤ (1 : ℝ≥0) := by
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (capKilling_nonneg α u x)]
      exact capKilling_le_one hα u x
    have hac : σ ≪ gibbsLaw N β D.hamiltonian :=
      sphereLaw_absolutelyContinuous_gibbsLaw hN β D.hamiltonian
        D.hamiltonian_contDiff.continuous
    have heq := (hPhysical u hu).filter_mono hac.ae_le
    have hb := (rateLaplace_killing_unit_interval D β (capKilling α u)
      (capKilling_contDiff α u).continuous (capKilling_nonneg α u) 1 hκ1 θ hθ).filter_mono hac.ae_le
    filter_upwards [heq,hb] with x hx hb
    change Ua (u,x) = _ at hx
    rw [hx]
    exact hb
  have hUaUnit : ∀ᵐ z ∂σ.prod σ, 0 ≤ Ua z ∧ Ua z ≤ 1 := by
    apply (Measure.ae_prod_iff_ae_ae (by
      exact (measurableSet_le measurable_const hUaSm.measurable).inter
        (measurableSet_le hUaSm.measurable measurable_const))).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    exact hUnit u ((onSphere_iff_norm_sq u).mpr hu)
  have hUai : Integrable Ua (σ.prod σ) :=
    Integrable.of_bound hUaSm.aestronglyMeasurable 1 (hUaUnit.mono fun z hz => by
      rw [Real.norm_eq_abs,abs_of_nonneg hz.1]; exact hz.2)
  have hhi : Integrable hit σ := by
    apply Integrable.of_bound
      ((pureSourceCapHitProbability_measurable d hd c hc Q α χ hχ β H).comp
        (by fun_prop)).aestronglyMeasurable 1
    exact .of_forall fun u => by
      change ‖pureSourceCapHitProbability d hd c hc Q α χ hχ β H
        (J,(u,(e,0)))‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs,abs_of_nonneg
        (pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β H (J,(u,(e,0)))).1]
      exact (pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β H (J,(u,(e,0)))).2
  have hp : ∀ᵐ u ∂σ, factor*(hit u-error) ≤ ∫ x, Ua (u,x) ∂σ := by
    filter_upwards [sphereLaw_support hN] with u hu
    have hu' : OnSphere u := (onSphere_iff_norm_sq u).mpr hu
    let D := FieldData.ofPure hN d hd c hc Q J u e α χ hχ
    have hac : σ ≪ gibbsLaw N β D.hamiltonian :=
      sphereLaw_absolutelyContinuous_gibbsLaw hN β D.hamiltonian
        D.hamiltonian_contDiff.continuous
    have heq := (hPhysical u hu').filter_mono hac.ae_le
    have hh := regular_pure_uniform_cap_hit_le_physical_resolvent hN d hd c hc
      Q B α β hB hα hβ χ hχ J hJ e he u hu' θ hθ H
    calc
      _ ≤ _ := hh
      _ = ∫ x, Ua (u,x) ∂σ := integral_congr_ae heq.symm
  have hi := integral_mono_ae ((hhi.sub (integrable_const error)).const_mul factor)
    hUai.integral_prod_left hp
  change (∫ u, factor*(hit u-error) ∂σ) ≤ ∫ u, ∫ x, Ua (u,x) ∂σ ∂σ at hi
  rw [integral_const_mul,integral_sub hhi (integrable_const error)] at hi
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hi

end SlowEquilibration.ConditionedEntrance
