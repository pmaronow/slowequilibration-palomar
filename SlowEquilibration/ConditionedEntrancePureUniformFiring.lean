-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureRegularCapHitExposure
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralUniformStart
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Uniform-start physical firing mass for every constructed C² field,
including the proper-pure cutoff, dominated by its actual killed resolvent. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalAging HardSphereDynamics SphericalDynamics FeynmanKac
open scoped NNReal ENNReal InnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def fieldUniformProcess (D : SmoothKilledGeneral.FieldData N) (β : ℝ) (t : ℝ≥0)
    (q : Vector N × VectorBrownian.Space N) : Vector N :=
  SmoothKilledGeneral.process D β q.1 t q.2

theorem fieldUniformProcess_measurable (D : SmoothKilledGeneral.FieldData N) (β : ℝ) :
    Measurable (Function.uncurry (fieldUniformProcess D β)) := by
  have hm : Measurable (fun q : ℝ≥0 × (Vector N × VectorBrownian.Space N) =>
      (q.2.1,(q.1,q.2.2))) := by fun_prop
  exact (flow_measurable _ _).comp hm

theorem fieldUniformKilledExpectation_eq (D : SmoothKilledGeneral.FieldData N) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1)
    (t : ℝ≥0) :
    killedExpectation ((sphereLaw N).prod (VectorBrownian.law N)) κ (fieldUniformProcess D β) t κ =
      ∫ x,SmoothKilledGeneral.expectation D β κ t κ x ∂sphereLaw N := by
  let X := fieldUniformProcess D β
  have hm := fieldUniformProcess_measurable D β
  have hs := survival_stronglyMeasurable κ hκ.measurable X hm t
  have hk : StronglyMeasurable (fun q : Vector N × VectorBrownian.Space N => κ (X t q)) :=
    (hκ.measurable.comp (hm.comp (measurable_const.prodMk measurable_id))).stronglyMeasurable
  have hi : Integrable (fun q => survival κ X t q * κ (X t q))
      ((sphereLaw N).prod (VectorBrownian.law N)) := by
    apply Integrable.of_bound (hs.mul hk).aestronglyMeasurable 1
    exact .of_forall fun q => by
      change ‖survival κ X t q * κ (X t q)‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (survival_nonneg κ X t q) (hκ0 _))]
      exact (mul_le_of_le_one_left (hκ0 _) (survival_le_one κ hκ0 X t q)).trans (hκ1 _)
  exact integral_prod _ hi

theorem field_uniform_finiteDiscountedMass_expectation_eq (D : SmoothKilledGeneral.FieldData N)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ≥0) :
    (∫ x,∫ omega,finiteDiscountedMass κ (SmoothKilledGeneral.process D β x) θ L omega
      ∂VectorBrownian.law N ∂sphereLaw N) =
      ∫ t in (0 : ℝ)..(L : ℝ),Real.exp (-θ * t) *
        (∫ x,SmoothKilledGeneral.expectation D β κ t.toNNReal κ x ∂sphereLaw N) := by
  let X := fieldUniformProcess D β
  have hm := fieldUniformProcess_measurable D β
  have hi : Integrable (finiteDiscountedMass κ X θ L)
      ((sphereLaw N).prod (VectorBrownian.law N)) :=
    Integrable.of_bound (finiteDiscountedMass_stronglyMeasurable κ hκ.measurable X hm θ L).aestronglyMeasurable
      (L : ℝ) (.of_forall (finiteDiscountedMass_norm_le κ hκ0 hκ1 X hθ L))
  calc
    _ = ∫ q,finiteDiscountedMass κ X θ L q ∂((sphereLaw N).prod (VectorBrownian.law N)) :=
      (integral_prod _ hi).symm
    _ = ∫ t in (0 : ℝ)..(L : ℝ),Real.exp (-θ * t) *
        killedExpectation ((sphereLaw N).prod (VectorBrownian.law N)) κ X t.toNNReal κ :=
      finiteDiscountedMass_expectation_eq _ κ hκ.measurable hκ0 hκ1 X hm hθ L
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change Real.exp (-θ * t) * killedExpectation ((sphereLaw N).prod (VectorBrownian.law N))
        κ (fieldUniformProcess D β) t.toNNReal κ = _
      rw [fieldUniformKilledExpectation_eq D β κ hκ hκ0 hκ1]

theorem field_uniform_finiteDiscountedMass_le_rateLaplace (D : SmoothKilledGeneral.FieldData N)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1) (θ : ℝ≥0) (hθ : 0 < θ) (L : ℝ≥0) :
    (∫ x,∫ omega,finiteDiscountedMass κ (SmoothKilledGeneral.process D β x) (θ : ℝ) L omega
      ∂VectorBrownian.law N ∂sphereLaw N) ≤
      ∫ x,SmoothKilledGeneral.rateLaplace D β κ hκ hκ0 θ (SmoothKilledGeneral.killingVector D β κ hκ) x ∂sphereLaw N := by
  let P := (sphereLaw N).prod (VectorBrownian.law N)
  let X := fieldUniformProcess D β
  let g : ℝ → ℝ := fun t => Real.exp (-(θ : ℝ) * t) * killedExpectation P κ X t.toNNReal κ
  have hm := fieldUniformProcess_measurable D β
  have hnorm (y : Vector N) : ‖κ y‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 y)]
    exact hκ1 y
  have hE (t : ℝ≥0) : ‖killedExpectation P κ X t κ‖ ≤ 1 :=
    killedExpectation_norm_le P κ hκ0 X t κ 1 (.of_forall fun _ => hnorm _)
  have hE0 (t : ℝ≥0) : 0 ≤ killedExpectation P κ X t κ :=
    integral_nonneg (fun q => mul_nonneg (survival_nonneg κ X t q) (hκ0 _))
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.exp_pos _).le (hE0 _)
  have hpair : Measurable (fun q : ℝ × (Vector N × VectorBrownian.Space N) => (q.1.toNNReal,q.2)) := by fun_prop
  have hs := (survival_joint_stronglyMeasurable κ hκ.measurable X hm).comp_measurable hpair
  have hk := (((hκ.measurable.comp hm).comp hpair).stronglyMeasurable)
  have hEg : StronglyMeasurable (fun t : ℝ => killedExpectation P κ X t.toNNReal κ) :=
    (hs.mul hk).integral_prod_right' (ν := P)
  have hg : StronglyMeasurable g :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).stronglyMeasurable.mul hEg
  have hgi : IntegrableOn g (Ioi (0 : ℝ)) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos (show 0 < (θ : ℝ) from hθ)) 0).mono' hg.aestronglyMeasurable
    exact .of_forall fun t => by
      dsimp [g]
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      have hEb : |killedExpectation P κ X t.toNNReal κ| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using hE t.toNNReal
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hEb (Real.exp_pos _).le
  rw [field_uniform_finiteDiscountedMass_expectation_eq D β κ hκ hκ0 hκ1 θ.coe_nonneg L,
    SmoothKilledGeneral.rateLaplace_killing_uniform_integral D β κ hκ hκ0 θ hθ,
    intervalIntegral.integral_of_le L.coe_nonneg]
  simp_rw [← fieldUniformKilledExpectation_eq D β κ hκ hκ0 hκ1]
  exact setIntegral_mono_set hgi (.of_forall hg0) (.of_forall fun _ ht => ht.1)

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
