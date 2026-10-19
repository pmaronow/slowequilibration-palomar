module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.CompactParametricIntegral
public import SlowEquilibration.SphericalReversibility

@[expose] public section

/-!
# Genuine finite-time C² Poisson primitives of the physical mixed semigroup

The primitive is the literal finite-time integral of the actual SDE
expectation. Its C² regularity and exact derivative jets follow from the
already proved joint stochastic-flow jets and dominated differentiation.
-/

namespace SlowEquilibration.SphericalPoissonPrimitive
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics SphericalAging.MultivariateTaylor
open scoped InnerProductSpace Topology ContDiff

variable {N : ℕ}

/-- The literal finite-time Poisson primitive of the actual mixed SDE. -/
def primitive (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : Vector N → ℝ) (T : ℝ) (x : Vector N) : ℝ :=
  ∫ t in Icc 0 T, Real.exp (-t) * realExpectation μ J β f t x

/-- Actual first spatial jets of the real-time physical expectation are
jointly continuous, by the true stochastic-flow jet provider. -/
lemma realExpectation_fderiv_joint_continuous (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun q : ℝ × Vector N => fderiv ℝ (realExpectation μ J β f q.1) q.2) := by
  have hmap : Continuous (fun q : ℝ × Vector N => (q.1.toNNReal, q.2)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  exact (mixedExpectation_regular μ J β hf hfc).2.2.1.comp hmap

lemma realExpectation_hessian_joint_continuous (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (fun q : ℝ × Vector N =>
      fderiv ℝ (fderiv ℝ (realExpectation μ J β f q.1)) q.2) := by
  have hmap : Continuous (fun q : ℝ × Vector N => (q.1.toNNReal, q.2)) :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  exact (mixedExpectation_regular μ J β hf hfc).2.2.2.comp hmap

private def weightedValue (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : Vector N → ℝ) (t : ℝ) (x : Vector N) : ℝ := Real.exp (-t) * realExpectation μ J β f t x

private def weightedFirst (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : Vector N → ℝ) (t : ℝ) (x : Vector N) : Vector N →L[ℝ] ℝ :=
  Real.exp (-t) • fderiv ℝ (realExpectation μ J β f t) x

private def weightedSecond (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : Vector N → ℝ) (t : ℝ) (x : Vector N) : Vector N →L[ℝ] Vector N →L[ℝ] ℝ :=
  Real.exp (-t) • fderiv ℝ (fderiv ℝ (realExpectation μ J β f t)) x

private lemma weightedValue_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (Function.uncurry (weightedValue μ J β f)) :=
  (Real.continuous_exp.comp continuous_fst.neg).mul (realExpectation_joint_continuous μ J β hf hfc)

private lemma weightedFirst_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (Function.uncurry (weightedFirst μ J β f)) :=
  (Real.continuous_exp.comp continuous_fst.neg).smul (realExpectation_fderiv_joint_continuous μ J β hf hfc)

private lemma weightedSecond_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (Function.uncurry (weightedSecond μ J β f)) :=
  (Real.continuous_exp.comp continuous_fst.neg).smul (realExpectation_hessian_joint_continuous μ J β hf hfc)

private lemma weightedValue_hasFDerivAt (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) (x : Vector N) :
    HasFDerivAt (weightedValue μ J β f t) (weightedFirst μ J β f t x) x :=
  (((realExpectation_contDiff μ J β hf hfc t).differentiable (by norm_num) x).hasFDerivAt).const_mul _

private lemma weightedFirst_hasFDerivAt (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t : ℝ) (x : Vector N) :
    HasFDerivAt (weightedFirst μ J β f t) (weightedSecond μ J β f t x) x := by
  have hh : ContDiff ℝ 1 (fderiv ℝ (realExpectation μ J β f t)) :=
    (realExpectation_contDiff μ J β hf hfc t).fderiv_right (by norm_num)
  exact ((hh.differentiable (by norm_num) x).hasFDerivAt).const_smul (Real.exp (-t))

/-- The literal physical finite-time primitive is genuinely C² in every
ambient point, without elliptic regularity or any integral regularity premise. -/
theorem primitive_contDiff (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (T : ℝ) :
    ContDiff ℝ 2 (primitive μ J β f T) := by
  let ν : Measure ℝ := volume.restrict (Icc 0 T)
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (measure_Icc_lt_top.ne)
  exact CompactParametricIntegral.contDiff_two_integral ν (Icc 0 T) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (weightedValue μ J β f) (weightedFirst μ J β f) (weightedSecond μ J β f)
    (weightedValue_continuous μ J β hf hfc) (weightedFirst_continuous μ J β hf hfc)
    (weightedSecond_continuous μ J β hf hfc)
    (fun t _ x => weightedValue_hasFDerivAt μ J β hf hfc t x)
    (fun t _ x => weightedFirst_hasFDerivAt μ J β hf hfc t x)

/-- Exact first jet of the literal physical primitive. -/
theorem primitive_fderiv (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (T : ℝ)
    (x : Vector N) :
    fderiv ℝ (primitive μ J β f T) x =
      ∫ t in Icc 0 T, Real.exp (-t) • fderiv ℝ (realExpectation μ J β f t) x := by
  let ν : Measure ℝ := volume.restrict (Icc 0 T)
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (measure_Icc_lt_top.ne)
  exact (CompactParametricIntegral.hasFDerivAt_integral ν (Icc 0 T) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) (weightedValue μ J β f) (weightedFirst μ J β f)
    (weightedValue_continuous μ J β hf hfc) (weightedFirst_continuous μ J β hf hfc)
    (fun t _ x => weightedValue_hasFDerivAt μ J β hf hfc t x) x).fderiv

/-- Exact second jet of the literal physical primitive. -/
theorem primitive_hessian (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (T : ℝ)
    (x : Vector N) :
    fderiv ℝ (fderiv ℝ (primitive μ J β f T)) x =
      ∫ t in Icc 0 T, Real.exp (-t) • fderiv ℝ (fderiv ℝ (realExpectation μ J β f t)) x := by
  have he : fderiv ℝ (primitive μ J β f T) = fun z =>
      ∫ t in Icc 0 T, Real.exp (-t) • fderiv ℝ (realExpectation μ J β f t) z :=
    funext (primitive_fderiv μ J β hf hfc T)
  rw [he]
  let ν : Measure ℝ := volume.restrict (Icc 0 T)
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (measure_Icc_lt_top.ne)
  exact (CompactParametricIntegral.hasFDerivAt_integral ν (Icc 0 T) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) (weightedFirst μ J β f) (weightedSecond μ J β f)
    (weightedFirst_continuous μ J β hf hfc) (weightedSecond_continuous μ J β hf hfc)
    (fun t _ x => weightedFirst_hasFDerivAt μ J β hf hfc t x) x).fderiv

end
end SlowEquilibration.SphericalPoissonPrimitive
