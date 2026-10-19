-- SPDX-License-Identifier: Apache-2.0
module
public import SphericalAging.HamiltonianPicardDependence

/-! Stability of the genuine Brownian Picard solution under drift changes.
Only the reference drift's Lipschitz constant enters the comparison constant.
The approximating drift may have an arbitrary finite Lipschitz constant. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PicardDriftStability
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open PredictableItoTime PredictableDriftTime PicardDependence HamiltonianPicardDependence
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- A changed drift is exactly a source defect in the reference Picard equation. -/
theorem sourceClass_eq_defect_source (D : BrownianDriver N P F) {Kb Kc Ks : ℝ≥0}
    {b c : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hc : ∀ i,LipschitzWith Kc (c i))
    (hs : ∀ i j,LipschitzWith Ks (sigma i j)) (T : ℝ≥0)
    (A : PredictableStateL2 N F P) :
    sourceClass D hc hs T A = sourceClass D hb hs T
      (A + (finiteDriftPicardMap hc T (sourceClass D hc hs T A) -
        finiteDriftPicardMap hb T (sourceClass D hc hs T A))) := by
  apply (GlobalSDE.exists_unique_picard_fixedPoint D hb hs T _).choose_spec.2
  have h := sourceClass_fixedPoint D hc hs T A
  convert h using 1 <;> abel

/-- The true solution difference is controlled by its actual drift defect.
The constant is uniform over all approximating drift Lipschitz constants. -/
theorem sourceClass_drift_defect_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) : ∃ K : ℝ≥0, ∀ {Kc : ℝ≥0} {c : Fin N → State N → ℝ}
      (hc : ∀ i,LipschitzWith Kc (c i)) (A : PredictableStateL2 N F P),
      ‖sourceClass D hc hs T A-sourceClass D hb hs T A‖ ≤ (K : ℝ) *
        ‖finiteDriftPicardMap hc T (sourceClass D hc hs T A) -
          finiteDriftPicardMap hb T (sourceClass D hc hs T A)‖ := by
  obtain ⟨K,hK⟩ := sourceClass_lipschitz D hb hs T
  refine ⟨K,fun hc A => ?_⟩
  have h := hK.dist_le_mul
    (A + (finiteDriftPicardMap hc T (sourceClass D hc hs T A) -
      finiteDriftPicardMap hb T (sourceClass D hc hs T A))) A
  rw [← sourceClass_eq_defect_source D hb hc hs T A] at h
  simpa only [dist_eq_norm,add_sub_cancel_left] using h

/-- A coefficient defect only needs to be small along the actual comparison
class. This allows sphere-local estimates even when ambient cutoffs differ. -/
theorem coefficient_sub_norm_bound_on_class {Kb Kc : ℝ≥0} {b c : State N → ℝ}
    (hb : LipschitzWith Kb b) (hc : LipschitzWith Kc c)
    (U : PredictableStateL2 N F P) (T : ℝ≥0) (δ : ℝ) (hδ : 0≤δ)
    (hcb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1∈Ioc 0 T → ‖c ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q)-
        b ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q)‖≤δ) :
    ‖predictableCoefficient hc U T-predictableCoefficient hb U T‖ ≤
      δ*(initialScale (P := P) T : ℝ) := by
  let W := (memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) δ
    (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).toLp
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => δ))
  have hw : ‖W‖=δ*(initialScale (P := P) T : ℝ) := norm_indicator_toLp T δ hδ
  rw [← hw]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [predictableCoefficient_coeFn hc U T,predictableCoefficient_coeFn hb U T,
    Lp.coeFn_sub (predictableCoefficient hc U T : TimeProcessL2 P)
      (predictableCoefficient hb U T),hcb,
    (memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
      (measurableSet_Ioc.prod MeasurableSet.univ) δ
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).coeFn_toLp]
    with q hcq hbq hsub hcbq hwq
  change ‖((predictableCoefficient hc U T : TimeProcessL2 P)-
    (predictableCoefficient hb U T : TimeProcessL2 P)) q‖≤‖(W : ℝ≥0×Ω→ℝ) q‖
  rw [hsub]
  simp only [Pi.sub_apply,hcq,hbq]
  change (W : ℝ≥0×Ω→ℝ) q=_ at hwq
  rw [hwq]
  by_cases hqt : q.1∈Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hqt,mem_univ _⟩)]
    simpa only [hqt,ite_true,Real.norm_of_nonneg hδ] using hcbq hqt
  · rw [indicator_of_notMem (show q∉Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from fun h => hqt h.1)]
    simp only [hqt,ite_false,sub_self,norm_zero,le_refl]

theorem finiteDrift_sub_norm_bound_on_class {Kb Kc : ℝ≥0}
    {b c : Fin N → State N → ℝ} (hb : ∀ i,LipschitzWith Kb (b i))
    (hc : ∀ i,LipschitzWith Kc (c i)) (U : PredictableStateL2 N F P)
    (T : ℝ≥0) (δ : ℝ) (hδ : 0≤δ)
    (hcb : ∀ i,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1∈Ioc 0 T → ‖c i ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q)-
        b i ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q)‖≤δ) :
    ‖finiteDriftPicardMap hc T U-finiteDriftPicardMap hb T U‖ ≤
      (N : ℝ)*T*δ*(initialScale (P := P) T : ℝ) := by
  unfold finiteDriftPicardMap driftCoefficientMap
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,‖scalarToStatePredictable i (driftVolterra T (predictableCoefficient (hc i) U T))-
      scalarToStatePredictable i (driftVolterra T (predictableCoefficient (hb i) U T))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N,(T : ℝ)*(δ*(initialScale (P := P) T : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarToStatePredictable_sub,← driftVolterra_sub]
      exact (norm_scalarToStatePredictable_le i _).trans ((norm_driftVolterra_le T _).trans
        (mul_le_mul_of_nonneg_left
          (coefficient_sub_norm_bound_on_class (hb i) (hc i) U T δ hδ (hcb i)) T.coe_nonneg))
    _ = _ := by simp; ring

theorem sourceClass_drift_bound_on_class (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) : ∃ K : ℝ≥0, ∀ {Kc : ℝ≥0} {c : Fin N → State N → ℝ}
      (hc : ∀ i,LipschitzWith Kc (c i)) (A : PredictableStateL2 N F P)
      (δ : ℝ) (hδ : 0≤δ)
      (hcb : ∀ i,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
        q.1∈Ioc 0 T → ‖c i ((sourceClass D hc hs T A : Lp (State N) 2
          (nonnegativeLebesgueMeasure.prod P)) q)-b i ((sourceClass D hc hs T A :
            Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q)‖≤δ),
      ‖sourceClass D hc hs T A-sourceClass D hb hs T A‖ ≤ (K : ℝ)*δ := by
  obtain ⟨K,hK⟩ := sourceClass_drift_defect_bound D hb hs T
  refine ⟨K*N*T*initialScale (P := P) T,fun hc A δ hδ hcb => ?_⟩
  exact (hK hc A).trans ((mul_le_mul_of_nonneg_left
    (finiteDrift_sub_norm_bound_on_class hb hc _ T δ hδ hcb) K.coe_nonneg).trans_eq
      (by simp only [NNReal.coe_mul,NNReal.coe_natCast]; ring))

/-- Uniform drift approximation implies uniform convergence of the actual
finite-horizon predictable solution classes, for every source. -/
theorem sourceClass_uniform_drift_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) : ∃ K : ℝ≥0, ∀ {Kc : ℝ≥0} {c : Fin N → State N → ℝ}
      (hc : ∀ i,LipschitzWith Kc (c i)) (δ : ℝ) (hδ : 0≤δ)
      (hcb : ∀ i x,‖c i x-b i x‖≤δ) (A : PredictableStateL2 N F P),
      ‖sourceClass D hc hs T A-sourceClass D hb hs T A‖ ≤ (K : ℝ)*δ := by
  obtain ⟨K,hK⟩ := sourceClass_drift_defect_bound D hb hs T
  refine ⟨K*N*T*initialScale (P := P) T,fun hc δ hδ hcb A => ?_⟩
  calc
    _ ≤ (K : ℝ)*‖finiteDriftPicardMap hc T (sourceClass D hc hs T A)-
        finiteDriftPicardMap hb T (sourceClass D hc hs T A)‖ := hK hc A
    _ ≤ (K : ℝ)*((N : ℝ)*T*δ*(initialScale (P := P) T : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (finiteDrift_coefficient_family_sub_le hc hb _ T δ hδ hcb) K.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_natCast]; ring

/-- In particular the canonical actual deterministic-initial Picard classes
converge under uniform drift convergence, without a common approximant bound. -/
theorem horizonClass_tendsto_of_uniform_drift (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (c : ℕ → Fin N → State N → ℝ) (Kc : ℕ → ℝ≥0)
    (hc : ∀ k i,LipschitzWith (Kc k) (c k i)) (δ : ℕ → ℝ)
    (hδ : ∀ k,0≤δ k) (hcb : ∀ k i x,‖c k i x-b i x‖≤δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : State N) (T : ℝ≥0) :
    Tendsto (fun k => GlobalSDE.horizonClass D (hc k) hs x T) atTop
      (𝓝 (GlobalSDE.horizonClass D hb hs x T)) := by
  obtain ⟨K,hK⟩ := sourceClass_uniform_drift_bound D hb hs T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) (fun k => hK (hc k) (δ k) (hδ k) (hcb k) _)
  simpa only [mul_zero] using hlim.const_mul (K : ℝ)

end SlowEquilibration.PicardDriftStability
