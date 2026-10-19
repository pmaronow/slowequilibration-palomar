-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOverlapExponentialGridGeometry
public import SlowEquilibration.ConditionedEntranceHazardExposure
public import Mathlib.MeasureTheory.Integral.Prod

/-! Measurable actual bounded-hazard firing mass. Joint occupation and
survival measurability are derived from literal parameter integrals. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory ProbabilityTheory Set Filter
open FeynmanKac
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]

theorem occupation_joint_stronglyMeasurable (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) :
    StronglyMeasurable (fun q : ℝ≥0 × Ω => occupation κ X q.1 q.2) := by
  let A : Set ((ℝ≥0 × Ω) × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)}
  let W : (ℝ≥0 × Ω) × ℝ → ℝ := A.indicator (fun p => κ (X p.2.toNNReal p.1.2))
  have hm : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => (p.2.toNNReal,p.1.2)) := by fun_prop
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (show Measurable (fun p : (ℝ≥0 × Ω) × ℝ => (p.1.1 : ℝ)) from by fun_prop))
  have hW : StronglyMeasurable W := ((hκ.comp hX).comp hm).stronglyMeasurable.indicator hA
  have hI := hW.integral_prod_right' (ν := (volume : Measure ℝ))
  convert hI using 1
  funext q
  unfold occupation
  rw [intervalIntegral.integral_of_le q.1.coe_nonneg ]
  have he : (fun t => W (q,t)) = (Ioc (0 : ℝ) (q.1 : ℝ)).indicator (fun t => κ (X t.toNNReal q.2)) := by
    funext t
    dsimp only [W]
    by_cases ht : t ∈ Ioc (0 : ℝ) (q.1 : ℝ)
    · rw [indicator_of_mem (show (q,t) ∈ A from ht),indicator_of_mem ht]
    · rw [indicator_of_notMem (show (q,t) ∉ A from fun h => ht h),indicator_of_notMem ht]
  rw [he,integral_indicator measurableSet_Ioc]

theorem survival_joint_stronglyMeasurable (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) :
    StronglyMeasurable (fun q : ℝ≥0 × Ω => survival κ X q.1 q.2) :=
  Real.continuous_exp.comp_stronglyMeasurable (occupation_joint_stronglyMeasurable κ hκ X hX).neg

def finiteDiscountedMass (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (θ : ℝ) (L : ℝ≥0) (omega : Ω) : ℝ :=
  ∫ t in (0 : ℝ)..(L : ℝ),Real.exp (-θ * t) * κ (X t.toNNReal omega) * survival κ X t.toNNReal omega

theorem finiteDiscountedMass_stronglyMeasurable (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) (θ : ℝ) (L : ℝ≥0) :
    StronglyMeasurable (finiteDiscountedMass κ X θ L) := by
  have hm : Measurable (fun q : Ω × ℝ => (q.2.toNNReal,q.1)) := by fun_prop
  have hterm : StronglyMeasurable (fun q : Ω × ℝ =>
      Real.exp (-θ * q.2) * κ (X q.2.toNNReal q.1) * survival κ X q.2.toNNReal q.1) :=
    (((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).stronglyMeasurable).mul
      (((hκ.comp hX).comp hm).stronglyMeasurable)).mul
      ((survival_joint_stronglyMeasurable κ hκ X hX).comp_measurable hm)
  have hI := hterm.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (L : ℝ)))
  convert hI using 1
  funext omega
  unfold finiteDiscountedMass
  rw [intervalIntegral.integral_of_le L.coe_nonneg ]

omit [MeasurableSpace E] [MeasurableSpace Ω] in
theorem finiteDiscountedMass_nonneg (κ : E → ℝ) (hκ0 : ∀ y,0 ≤ κ y)
    (X : ℝ≥0 → Ω → E) (θ : ℝ) (L : ℝ≥0) (omega : Ω) : 0 ≤ finiteDiscountedMass κ X θ L omega :=
  intervalIntegral.integral_nonneg L.coe_nonneg (fun _t _ =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (hκ0 _)) (survival_nonneg κ X _ omega))

omit [MeasurableSpace E] [MeasurableSpace Ω] in
theorem finiteDiscountedMass_norm_le (κ : E → ℝ) (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1)
    (X : ℝ≥0 → Ω → E) {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ≥0) (omega : Ω) :
    ‖finiteDiscountedMass κ X θ L omega‖ ≤ (L : ℝ) := by
  have hb (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) (L : ℝ)) :
      ‖Real.exp (-θ * t) * κ (X t.toNNReal omega) * survival κ X t.toNNReal omega‖ ≤ (1 : ℝ) := by
    have ht0 : 0 ≤ t := (show t ∈ Icc (0 : ℝ) (L : ℝ) from by simpa only [uIcc_of_le L.coe_nonneg] using ht).1
    have he : Real.exp (-θ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hs := survival_le_one κ hκ0 X t.toNNReal omega
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (hκ0 _)) (survival_nonneg κ X _ omega))]
    exact (mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (hκ0 _)) hs).trans
      ((mul_le_of_le_one_left (hκ0 _) he).trans (hκ1 _))
  simpa only [finiteDiscountedMass,sub_zero,abs_of_nonneg L.coe_nonneg,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hb t (uIoc_subset_uIcc ht))

omit [MeasurableSpace E] [MeasurableSpace Ω] in
lemma finiteDiscountedMass_eq_hazard (κ : E → ℝ) (X : ℝ≥0 → Ω → E)
    (θ : ℝ) (L : ℝ≥0) (omega : Ω) :
    finiteDiscountedMass κ X θ L omega = ∫ t in (0 : ℝ)..(L : ℝ),
      Real.exp (-θ * t) * κ (X t.toNNReal omega) * hazardSurvival (fun r => κ (X r.toNNReal omega)) t := by
  unfold finiteDiscountedMass
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := (show t ∈ Icc (0 : ℝ) (L : ℝ) from by simpa only [uIcc_of_le L.coe_nonneg] using ht).1
  unfold survival occupation hazardSurvival integratedHazard
  dsimp only
  rw [Real.coe_toNNReal t ht0]

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
