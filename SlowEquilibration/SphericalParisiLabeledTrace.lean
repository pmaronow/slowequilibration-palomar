-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledThreeBlock
public import SlowEquilibration.SphericalParisiLabeledBregman
public import SlowEquilibration.GaussianSpinKernels

@[expose] public section

/-! Actual finite spherical spin-label Gibbs trace bounds. The remaining
negative-overlap contribution is the literal product Gibbs probability,
not a supplied overlap assumption. All feature measurability and boundedness
are derived from the true compact unit sphere and finite label space. -/

namespace SlowEquilibration.SphericalParisiLabeledTrace
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledBregman GaussianCompactFeatureComparison
open GaussianThreeBlockComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
private theorem tagged_continuous {N k : ℕ} :
    Continuous (fun z : UnitSphere N × Fin k => taggedVector z.2 z.1.val) := by
  apply continuous_prod_of_discrete_right.mpr
  intro a
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i.1=a
  · simp only [hi,ite_true]
    exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i.2).comp continuous_subtype_val
  · simp only [hi,ite_false]
    exact continuous_const

omit [DecidableEq σ] in
theorem actual_originalFeature_continuous {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (Δ : ℝ) :
    Continuous (originalFeature (N := N) (k := k) d c Δ) := by
  classical
  unfold originalFeature
  apply sumJoin.continuous.comp
  refine ((FiniteTensorMixtureMaximum.feature_continuous d c).comp
    (continuous_subtype_val.comp continuous_fst)).prodMk ?_
  exact (continuous_of_discreteTopology (f := fun a : Fin k =>
    (Real.sqrt (N : ℝ)*Real.sqrt Δ) • EuclideanSpace.single a (1 : ℝ))).comp continuous_snd

omit [DecidableEq σ] in
theorem actual_trialFeature_continuous {N k : ℕ} (a b : ℝ) :
    Continuous (trialFeature (N := N) (k := k) a b) := by
  unfold trialFeature
  exact sumJoin.continuous.comp
    (((continuous_subtype_val.comp continuous_fst).const_smul
      (Real.sqrt (N : ℝ)*Real.sqrt a)).prodMk
      (tagged_continuous.const_smul (Real.sqrt (N : ℝ)*Real.sqrt b)))

omit [DecidableEq σ] in
theorem actual_threeFeature_continuous {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) :
    Continuous (threeFeature (N := N) (k := k) d c β q0 q1 v x) := by
  unfold threeFeature
  exact sumJoin.continuous.comp ((sumJoin.continuous.comp
    (((actual_originalFeature_continuous d c _).const_smul β).prodMk
      ((actual_trialFeature_continuous _ _).const_smul β))).prodMk
        ((SphericalPositivePerturbation.feature_continuous _).comp
          (continuous_subtype_val.comp continuous_fst)))

omit [DecidableEq σ] in
theorem actual_threeLinear_continuous {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) :
    Continuous (threeLinear (N := N) (k := k) d c β q0 q1 v x) :=
  (innerSL ℝ).continuous.comp (actual_threeFeature_continuous d c β q0 q1 v x)

omit [DecidableEq σ] in
/-- Every actual bank is bounded on the literal compact sphere-label space;
no finite-state replacement or externally supplied feature bound is used. -/
theorem actual_threeLinear_bounded {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : UnitSphere N × Fin k,‖threeLinear d c β q0 q1 v x z‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (actual_threeLinear_continuous (N := N) (k := k) d c β q0 q1 v x).continuousOn
  exact ⟨max C 0,le_max_right _ _,fun z => (hC z (mem_univ z)).trans (le_max_left _ _)⟩

def negativePairSet (N k : ℕ) (ε : ℝ) : Set ((UnitSphere N × Fin k) × (UnitSphere N × Fin k)) :=
  {z | inner ℝ z.1.1.val z.2.1.val ≤ -ε}

theorem negativePairSet_measurable (N k : ℕ) (ε : ℝ) :
    MeasurableSet (negativePairSet N k ε) := by
  apply measurableSet_le _ measurable_const
  fun_prop

/-- The all-parity error is paid only on the actual negative-overlap event. -/
theorem actual_three_signedKernel_error_bound {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    (β v : ℝ) {q0 q1 ε : ℝ} (hq0 : 0 ≤ q0) (hqq : q0 ≤ q1) (hε : 0 ≤ ε)
    (x : Fin K → ℝ) (z w : UnitSphere N × Fin k) :
    signedKernel (threeLinear d c β q0 q1 v x) threeLabel z w ≤
      (N : ℝ)*β^2*(theta d c q0+covarianceBudget c*ε)+
        ((N : ℝ)*β^2*covarianceBudget c)*
          (negativePairSet N k ε).indicator (fun _ => (1 : ℝ)) (z,w) := by
  rw [actual_three_signedKernel d c hc hd β v hq0 hqq x z w]
  have hr : |inner ℝ z.1.val w.1.val| ≤ 1 := by
    simpa only [unit_norm,mul_one] using abs_real_inner_le_norm z.1.val w.1.val
  have hq : 0 ≤ (if z.2=w.2 then q1 else q0) := by
    by_cases hz : z.2=w.2
    · rw [ite_eq_left hz]
      exact hq0.trans hqq
    · rw [ite_eq_right hz]
      exact hq0
  have hb := negative_bregmanGap_indicator_bound d c hc hd hr hq hε
  have hcoef : 0 ≤ (N : ℝ)*β^2 := mul_nonneg (Nat.cast_nonneg N) (sq_nonneg β)
  have H := mul_le_mul_of_nonneg_left hb hcoef
  have he : (negativePairSet N k ε).indicator (fun _ => (1 : ℝ)) (z,w)=
      if inner ℝ z.1.val w.1.val ≤ -ε then 1 else 0 := rfl
  rw [he]
  nlinarith [H]

def actualNegativePairMass {N k K : ℕ} (ν : Measure (UnitSphere N × Fin k))
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v : ℝ) (x : Fin K → ℝ)
    (θ : ℝ) (g : EuclideanSpace ℝ (ThreeCoordinate N k K d)) (ε : ℝ) : ℝ :=
  let G := gibbsMeasure ν (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) g
  (G.prod G).real (negativePairSet N k ε)

/-- Literal finite signed covariance trace with its true product Gibbs mass.
The statement uses the actual interpolated law at every rotation parameter. -/
theorem actual_three_signedTrace_lower {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    (β v : ℝ) {q0 q1 ε : ℝ} (hq0 : 0 ≤ q0) (hqq : q0 ≤ q1) (hε : 0 ≤ ε)
    (x : Fin K → ℝ) (θ : ℝ) (g : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    (N : ℝ)*β^2*(-bregmanGap d c 1 q1-covarianceBudget c*ε-
      covarianceBudget c*actualNegativePairMass ν d c β q0 q1 v x θ g ε) ≤
      ∑ i,covarianceSign threeLabel i*variance (coordinateObservable
        (threeLinear d c β q0 q1 v x) i)
        (gibbsMeasure ν (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) g) := by
  let L := threeLinear (N := N) (k := k) d c β q0 q1 v x
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v x
  have hL : Measurable L := (actual_threeLinear_continuous d c β q0 q1 v x).measurable
  have hb : ∀ᵐ z ∂ν,‖L z‖ ≤ C := .of_forall hbound
  let G := gibbsMeasure ν (rotatedLinear L threeLabel θ) g
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν _
    (rotatedLinear_measurable L hL threeLabel θ) (rotatedLinear_bound ν L hC hb threeLabel θ) g
  let S := negativePairSet N k ε
  let I : (UnitSphere N × Fin k) × (UnitSphere N × Fin k) → ℝ := S.indicator (fun _ => 1)
  have hI : Integrable I (G.prod G) := by
    apply Integrable.of_bound ((measurable_const.indicator (negativePairSet_measurable N k ε)).aestronglyMeasurable) 1
    exact .of_forall fun z => by
      change ‖S.indicator (fun _ => (1 : ℝ)) z‖ ≤ 1
      by_cases hz : z ∈ S
      · rw [indicator_of_mem hz]
        norm_num
      · rw [indicator_of_notMem hz]
        norm_num
  have hdiag : (∫ z,signedKernel L threeLabel z z ∂G)=
      (N : ℝ)*β^2*(theta d c q0-bregmanGap d c 1 q1) := by
    simp only [L,actual_three_signedKernel_diagonal d c hc hd β v hq0 hqq x]
    simp only [integral_const,probReal_univ,one_smul]
  have hp : (∫ z,signedKernel L threeLabel z.1 z.2 ∂G.prod G) ≤
      (N : ℝ)*β^2*(theta d c q0+covarianceBudget c*ε)+
        ((N : ℝ)*β^2*covarianceBudget c)*(G.prod G).real S := by
    have H := integral_mono (signedKernel_pair_integrable ν L hL hC hb threeLabel θ g)
      ((integrable_const _).add (hI.const_mul _))
      (fun z => actual_three_signedKernel_error_bound d c hc hd β v hq0 hqq hε x z.1 z.2)
    rw [integral_add' (integrable_const _) (hI.const_mul _),
      integral_const_mul ((N : ℝ)*β^2*covarianceBudget c) I] at H
    have hIeq : (∫ z,I z ∂G.prod G)=(G.prod G).real S :=
      integral_indicator_one (negativePairSet_measurable N k ε)
    rw [hIeq] at H
    simpa only [integral_const,probReal_univ,one_smul] using H
  rw [signedVarianceTrace_eq_kernels ν L hL hC hb threeLabel θ g,hdiag]
  change (N : ℝ)*β^2*(-bregmanGap d c 1 q1-covarianceBudget c*ε-
    covarianceBudget c*(G.prod G).real S) ≤ _
  nlinarith [hp]

end
end SlowEquilibration.SphericalParisiLabeledTrace
