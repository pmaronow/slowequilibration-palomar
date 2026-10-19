module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalPoissonPrimitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

/-! # The actual finite-time physical Poisson forcing equation -/

namespace SlowEquilibration.SphericalPoissonPrimitive
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics SphericalAging.MultivariateTaylor
open scoped InnerProductSpace Topology ContDiff BigOperators

variable {N : ℕ}
abbrev Jet (N : ℕ) := (Vector N →L[ℝ] ℝ) × (Vector N →L[ℝ] Vector N →L[ℝ] ℝ)

/-- Actual physical second-order coefficients define a genuine continuous
linear functional on the literal first and Hessian jets. -/
def coefficientJet (b : Vector N) (σ : Fin N → Vector N) : Jet N →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.fst ℝ _ _) +
    (1 / 2 : ℝ) • ∑ j : Fin N,
      ((ContinuousLinearMap.apply ℝ ℝ (σ j)).comp
        (ContinuousLinearMap.apply ℝ (Vector N →L[ℝ] ℝ) (σ j))).comp
          (ContinuousLinearMap.snd ℝ _ _)

lemma coefficientJet_apply (b : Vector N) (σ : Fin N → Vector N) (z : Jet N) :
    coefficientJet b σ z = z.1 b + (1 / 2 : ℝ) * ∑ j : Fin N, z.2 (σ j) (σ j) := by
  simp [coefficientJet]

/-- Literal actual mixed SDE generator functional. -/
def mixedJet (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) :
    Jet N →L[ℝ] ℝ := coefficientJet (drift β (mixedGradient μ J) x) (noiseColumn x)

lemma mixedGenerator_as_jet (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : Vector N → ℝ) (x : Vector N) :
    mixedGenerator μ J β f x = mixedJet μ J β x
      (fderiv ℝ f x, fderiv ℝ (fderiv ℝ f) x) := by
  rw [mixedJet, coefficientJet_apply]
  rfl

/-- The literal actual second-order generator commutes with the finite-time
primitive. The interchange follows from actual C² integral jets and a true
continuous linear jet functional. -/
theorem primitive_generator (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (T : ℝ)
    (x : Vector N) :
    mixedGenerator μ J β (primitive μ J β f T) x =
      ∫ t in Icc 0 T, Real.exp (-t) * mixedGenerator μ J β (realExpectation μ J β f t) x := by
  let ν : Measure ℝ := volume.restrict (Icc 0 T)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (measure_Icc_lt_top.ne)
  let D : ℝ → Vector N → Vector N →L[ℝ] ℝ := fun t y =>
    Real.exp (-t) • fderiv ℝ (realExpectation μ J β f t) y
  let H₂ : ℝ → Vector N → Vector N →L[ℝ] Vector N →L[ℝ] ℝ := fun t y =>
    Real.exp (-t) • fderiv ℝ (fderiv ℝ (realExpectation μ J β f t)) y
  have hD : Continuous (Function.uncurry D) :=
    (Real.continuous_exp.comp continuous_fst.neg).smul
      (realExpectation_fderiv_joint_continuous μ J β hf hfc)
  have hH : Continuous (Function.uncurry H₂) :=
    (Real.continuous_exp.comp continuous_fst.neg).smul
      (realExpectation_hessian_joint_continuous μ J β hf hfc)
  have hiD := CompactParametricIntegral.integrable_section ν (Icc 0 T) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) D hD x
  have hiH := CompactParametricIntegral.integrable_section ν (Icc 0 T) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) H₂ hH x
  let b := drift β (mixedGradient μ J) x
  let σ := noiseColumn x
  have hiB : Integrable (fun t => D t x b) ν :=
    (ContinuousLinearMap.apply ℝ ℝ b).integrable_comp hiD
  have hiHj (j : Fin N) : Integrable (fun t => H₂ t x (σ j)) ν :=
    CompactParametricIntegral.integrable_section ν (Icc 0 T) isCompact_Icc
      (ae_restrict_mem measurableSet_Icc) (fun t y => H₂ t y (σ j))
      (hH.clm_apply continuous_const) x
  have hiS (j : Fin N) : Integrable (fun t => H₂ t x (σ j) (σ j)) ν :=
    CompactParametricIntegral.integrable_section ν (Icc 0 T) isCompact_Icc
      (ae_restrict_mem measurableSet_Icc) (fun t y => H₂ t y (σ j) (σ j))
      ((hH.clm_apply continuous_const).clm_apply continuous_const) x

  rw [mixedGenerator_as_jet, primitive_fderiv μ J β hf hfc, primitive_hessian μ J β hf hfc,
    mixedJet, coefficientJet_apply]
  change (∫ t, D t x ∂ν) b + (1 / 2 : ℝ) * ∑ j : Fin N,
    (∫ t, H₂ t x ∂ν) (σ j) (σ j) = _
  rw [ContinuousLinearMap.integral_apply hiD]
  simp_rw [ContinuousLinearMap.integral_apply hiH]
  simp_rw [ContinuousLinearMap.integral_apply (hiHj _)]
  rw [← integral_finsetSum Finset.univ (fun j _ => hiS j), ← integral_const_mul,
    ← integral_add hiB ((integrable_finsetSum Finset.univ (fun j _ => hiS j)).const_mul _)]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [D, H₂, smul_apply, smul_eq_mul, mixedGenerator_as_jet,
    mixedJet, coefficientJet_apply]
  rw [← Finset.mul_sum]
  ring

/-- The genuine C² physical finite-time primitive has the exact forcing
`f−exp(−T)P_Tf` on the true sphere. This is an actual backward-equation and
ordinary fundamental-theorem calculation, with no generator-core premise. -/
theorem primitive_forcing (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {T : ℝ} (hT : 0 < T)
    (x : Vector N) (hx : OnSphere x) :
    primitive μ J β f T x - mixedGenerator μ J β (primitive μ J β f T) x =
      f x - Real.exp (-T) * realExpectation μ J β f T x := by
  have hv : Continuous (fun t => realExpectation μ J β f t x) :=
    (realExpectation_joint_continuous μ J β hf hfc).comp (continuous_id.prodMk continuous_const)
  have hL : Continuous (fun t => mixedGenerator μ J β (realExpectation μ J β f t) x) :=
    (realExpectation_generator_joint_continuous μ J β hf hfc).comp
      (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun t => Real.exp (-t) * realExpectation μ J β f t x) :=
    (Real.continuous_exp.comp continuous_id.neg).mul hv
  have hLc : Continuous (fun t => Real.exp (-t) * mixedGenerator μ J β (realExpectation μ J β f t) x) :=
    (Real.continuous_exp.comp continuous_id.neg).mul hL
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun s => Real.exp (-s) * realExpectation μ J β f s x)
        (Real.exp (-t) * (mixedGenerator μ J β (realExpectation μ J β f t) x -
          realExpectation μ J β f t x)) t := by
    have hback : HasDerivAt (fun s => realExpectation μ J β f s x)
        (mixedGenerator μ J β (realExpectation μ J β f t) x) t :=
      mixedExpectation_backward hN μ J β x hx hf hfc t ht.1
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      convert! (((hasDerivAt_id t).neg).exp) using 1 <;> simp
    have hd := hexp.mul hback
    convert! hd using 1 <;> (try simp only [Pi.mul_apply]) <;> ring

  have hq : Continuous (fun t => Real.exp (-t) *
      (mixedGenerator μ J β (realExpectation μ J β f t) x - realExpectation μ J β f t x)) :=
    (Real.continuous_exp.comp continuous_id.neg).mul (hL.sub hv)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hc.continuousOn
    hder (hq.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc] at hFTC
  have hqeq : (fun t => Real.exp (-t) *
      (mixedGenerator μ J β (realExpectation μ J β f t) x - realExpectation μ J β f t x)) =
      (fun t => Real.exp (-t) * mixedGenerator μ J β (realExpectation μ J β f t) x -
        Real.exp (-t) * realExpectation μ J β f t x) := by funext t; ring
  rw [hqeq, integral_sub (hLc.continuousOn.integrableOn_compact isCompact_Icc)
    (hc.continuousOn.integrableOn_compact isCompact_Icc),
    ← primitive_generator μ J β hf hfc T x, show
      (∫ t in Icc 0 T, Real.exp (-t) * realExpectation μ J β f t x) = primitive μ J β f T x from rfl,
    realExpectation_zero, neg_zero, Real.exp_zero, one_mul] at hFTC
  linarith

end
end SlowEquilibration.SphericalPoissonPrimitive
