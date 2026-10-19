-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledOriginalEndpoint
public import SlowEquilibration.SphericalParisiCommonGaussianTrial

@[expose] public section

/-! Actual finite spherical linear-trial endpoint is bounded by its real
Gaussian common/fresh row norm partition. The probability measure on the
physical unit sphere is arbitrary, and the label law is genuinely uniform. -/

namespace SlowEquilibration.SphericalParisiLabeledTrialEndpoint
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock SphericalParisiLabeledTrace
open SphericalParisiLabeledOriginalEndpoint SphericalParisiGaussianREMJensen SphericalParisiCommonGaussianTrial
open GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem join_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u u' : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    inner ℝ (sumJoin (u,w)) (sumJoin (u',w'))=inner ℝ u u'+inner ℝ w w' := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

/-- A labeled row is literally the matching iid Gaussian coordinates. -/
theorem actual_tagged_row_inner {N k : ℕ} (i : Fin k) (z : Vector N)
    (g : EuclideanSpace ℝ (Fin k × Fin N)) :
    inner ℝ (taggedVector i z) g=inner ℝ z (gaussianRow N k i g) := by
  simp [taggedVector,PiLp.inner_apply,Fintype.sum_prod_type,RCLike.inner_apply,conj_trivial,
    gaussianRow,projectGaussian,mul_ite]

/-- Literal common and fresh linear field split on each actual unit spin. -/
theorem actual_trialFeature_value_split {N k : ℕ} (a0 a : ℝ)
    (z : UnitSphere N × Fin k) (g0 : EuclideanSpace ℝ (Fin N))
    (g : EuclideanSpace ℝ (Fin k × Fin N)) :
    inner ℝ (trialFeature a0 a z) (sumJoin (g0,g))=
      Real.sqrt (N : ℝ)*inner ℝ z.1.val
        (Real.sqrt a0 • g0+Real.sqrt a • gaussianRow N k z.2 g) := by
  rw [trialFeature,join_inner,real_inner_smul_left,real_inner_smul_left,actual_tagged_row_inner,
    inner_add_right,real_inner_smul_right,real_inner_smul_right]
  ring

def trialLinear {N k : ℕ} (β a0 a : ℝ) (z : UnitSphere N × Fin k) :
    EuclideanSpace ℝ (TrialCoordinate N k) →L[ℝ] ℝ := innerSL ℝ (β • trialFeature a0 a z)

theorem trialLinear_continuous {N k : ℕ} (β a0 a : ℝ) :
    Continuous (trialLinear (N := N) (k := k) β a0 a) :=
  (innerSL ℝ).continuous.comp ((actual_trialFeature_continuous a0 a).const_smul β)

theorem trialLinear_bounded {N k : ℕ} (β a0 a : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : UnitSphere N × Fin k,‖trialLinear β a0 a z‖ ≤ C := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (trialLinear_continuous (N := N) (k := k) β a0 a).continuousOn
  exact ⟨max B 0,le_max_right _ _,fun z => (hB z (mem_univ z)).trans (le_max_left _ _)⟩

/-- The actual spin integral is bounded by maximizing its actual linear
field separately in each Gaussian label row. -/
theorem actual_trial_log_partition_le_norm_rows {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (a0 a : ℝ) (g0 : EuclideanSpace ℝ (Fin N)) (g : EuclideanSpace ℝ (Fin k × Fin N)) :
    logPartition (μ.prod (labelLaw k)) (trialLinear β a0 a) (sumJoin (g0,g)) ≤
      commonRowLogAverage a0 a (β*Real.sqrt (N : ℝ)) (g0,g) := by
  let ν := μ.prod (labelLaw k)
  let L := trialLinear (N := N) (k := k) β a0 a
  obtain ⟨C,_hC,hbound⟩ := trialLinear_bounded (N := N) (k := k) β a0 a
  have hL : Measurable L := (trialLinear_continuous β a0 a).measurable
  have hb : ∀ᵐ z ∂ν,‖L z‖ ≤ C := .of_forall hbound
  have hi := weight_integrable ν (fun _ => 1) L measurable_const hL (C := 1)
    (hb.mono fun z hz => ⟨by norm_num,hz⟩) (sumJoin (g0,g))
  let F := fun z : UnitSphere N × Fin k =>
    Real.exp ((β*Real.sqrt (N : ℝ))*‖Real.sqrt a0 • g0+Real.sqrt a • gaussianRow N k z.2 g‖)
  have hiF : Integrable F ν := (Integrable.of_finite (f := fun i : Fin k =>
    Real.exp ((β*Real.sqrt (N : ℝ))*‖Real.sqrt a0 • g0+Real.sqrt a • gaussianRow N k i g‖))).comp_snd μ
  have hdom (z : UnitSphere N × Fin k) : weight (fun _ => 1) L (sumJoin (g0,g)) z ≤ F z := by
    simp only [weight,one_mul,L,trialLinear,innerSL_apply_apply,real_inner_smul_left,
      actual_trialFeature_value_split]
    apply Real.exp_le_exp.mpr
    have H := (le_abs_self (inner ℝ z.1.val
      (Real.sqrt a0 • g0+Real.sqrt a • gaussianRow N k z.2 g))).trans
      (abs_real_inner_le_norm _ _)
    rw [unit_norm,one_mul] at H
    have hc : 0 ≤ β*Real.sqrt (N : ℝ) := mul_nonneg hβ (Real.sqrt_nonneg _)
    convert mul_le_mul_of_nonneg_left H hc using 1
    ring
  have H := integral_mono hi hiF hdom
  have hZ := moment_one_pos ν L hL hb (sumJoin (g0,g))
  have hl := Real.log_le_log hZ H
  change logPartition ν L (sumJoin (g0,g)) ≤ _ at hl
  apply hl.trans_eq
  unfold F
  change Real.log (∫ z : UnitSphere N × Fin k,
    Real.exp ((β*Real.sqrt (N : ℝ))*‖Real.sqrt a0 • g0+Real.sqrt a • gaussianRow N k z.2 g‖)
      ∂μ.prod (labelLaw k))=_
  rw [integral_fun_snd (fun i : Fin k =>
    Real.exp ((β*Real.sqrt (N : ℝ))*‖Real.sqrt a0 • g0+Real.sqrt a • gaussianRow N k i g‖)),labelLaw_integral]
  simp only [probReal_univ,one_smul,commonRowLogAverage,actualGaussianNormLogAverage,logAverageExp]

end
end SlowEquilibration.SphericalParisiLabeledTrialEndpoint
