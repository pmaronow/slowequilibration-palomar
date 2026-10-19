-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledKernelSemigroup
public import SlowEquilibration.SphericalL2Semigroup

/-! Genuine L² operators of finite subprobability kernels with a
subinvariant reference measure. This is the functional-analytic
construction needed by the actual physical bounded killing kernels. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.KilledL2
open SphericalAging
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [MeasurableSpace E]
  (π : Measure E) [IsProbabilityMeasure π] (K : Kernel E E) [IsFiniteKernel K]
  (hmass : ∀ x, K x univ ≤ 1) (hsub : K ∘ₘ π ≤ π)

def average (f : E → ℝ) (x : E) : ℝ := ∫ y, f y ∂K x

omit [IsProbabilityMeasure π] [IsFiniteKernel K] in
theorem average_integrable {f : E → ℝ} (hf : Integrable f (K ∘ₘ π)) :
    Integrable (average K f) π := by
  rw [Measure.comp_eq_comp_const_apply] at hf
  exact hf.integral_comp

omit [IsProbabilityMeasure π] [IsFiniteKernel K] in
theorem integral_average {f : E → ℝ} (hf : Integrable f (K ∘ₘ π)) :
    (∫ x, average K f x ∂π) = ∫ y, f y ∂(K ∘ₘ π) := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  exact (Kernel.integral_comp hf).symm

include hsub in
omit [IsProbabilityMeasure π] [IsFiniteKernel K] in
theorem ae_average_congr {f g : E → ℝ} (hfg : f =ᵐ[π] g) :
    average K f =ᵐ[π] average K g := by
  have h : f =ᵐ[K ∘ₘ π] g := (ae_mono hsub) hfg
  exact (Measure.ae_ae_of_ae_comp h).mono (fun _ hx => integral_congr_ae hx)

include hmass hsub

omit [IsProbabilityMeasure π] in
theorem average_square_le (U : Lp ℝ 2 π) :
    ∀ᵐ x ∂π, average K U x ^ 2 ≤ ∫ y, U y ^ 2 ∂K x := by
  have hi : Integrable (fun y => U y ^ 2) (K ∘ₘ π) :=
    (Lp.memLp U).integrable_sq.mono_measure hsub
  have hslice := (Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi
  filter_upwards [hslice.1] with x hx
  have hm : MemLp (U : E → ℝ) 2 (K x) :=
    (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable U).aestronglyMeasurable).mpr hx
  have h := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq (K x) U hm
  have hμ : (K x).real univ ≤ 1 := by
    simpa only [Measure.real_def,ENNReal.toReal_one] using
      ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hmass x)
  exact h.trans (mul_le_of_le_one_left (integral_nonneg (fun _ => sq_nonneg _)) hμ)

omit [IsProbabilityMeasure π] in
theorem average_memLp (U : Lp ℝ 2 π) : MemLp (average K U) 2 π := by
  have hi : Integrable (fun y => U y ^ 2) (K ∘ₘ π) :=
    (Lp.memLp U).integrable_sq.mono_measure hsub
  have hq : Integrable (fun x => ∫ y, U y ^ 2 ∂K x) π := average_integrable π K hi
  apply (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable U).integral_kernel.aestronglyMeasurable).mpr
  apply hq.mono' ((Lp.stronglyMeasurable U).integral_kernel.pow 2).aestronglyMeasurable
  filter_upwards [average_square_le π K hmass hsub U] with x hx
  change ‖average K U x ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hx

def vector (U : Lp ℝ 2 π) : Lp ℝ 2 π :=
  (average_memLp π K hmass hsub U).toLp (average K U)

omit [IsProbabilityMeasure π] in
theorem vector_ae (U : Lp ℝ 2 π) : vector π K hmass hsub U =ᵐ[π] average K U :=
  (average_memLp π K hmass hsub U).coeFn_toLp

omit [IsProbabilityMeasure π] in
theorem vector_square_norm (U : Lp ℝ 2 π) :
    ‖vector π K hmass hsub U‖ ^ 2 = ∫ x, average K U x ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vector_ae π K hmass hsub U] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial,← pow_two]

omit [IsProbabilityMeasure π] in
theorem vector_norm_le (U : Lp ℝ 2 π) : ‖vector π K hmass hsub U‖ ≤ ‖U‖ := by
  have hi : Integrable (fun y => U y ^ 2) (K ∘ₘ π) :=
    (Lp.memLp U).integrable_sq.mono_measure hsub
  have hsq : ‖vector π K hmass hsub U‖ ^ 2 ≤ ‖U‖ ^ 2 := by
    rw [vector_square_norm]
    calc
      _ ≤ ∫ x, ∫ y, U y ^ 2 ∂K x ∂π := integral_mono_ae
        (average_memLp π K hmass hsub U).integrable_sq (average_integrable π K hi)
        (average_square_le π K hmass hsub U)
      _ = ∫ y, U y ^ 2 ∂(K ∘ₘ π) := integral_average π K hi
      _ ≤ ∫ y, U y ^ 2 ∂π := integral_mono_measure hsub
        (.of_forall (fun y => sq_nonneg (U y))) (Lp.memLp U).integrable_sq
      _ = ‖U‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq,L2.inner_def]
        congr 1
        funext y
        simp only [RCLike.inner_apply,conj_trivial,pow_two]
  nlinarith [norm_nonneg (vector π K hmass hsub U),norm_nonneg U]

theorem vector_add (U V : Lp ℝ 2 π) :
    vector π K hmass hsub (U+V) = vector π K hmass hsub U + vector π K hmass hsub V := by
  have hiU : Integrable (U : E → ℝ) (K ∘ₘ π) :=
    ((Lp.memLp U).integrable (by norm_num)).mono_measure hsub
  have hiV : Integrable (V : E → ℝ) (K ∘ₘ π) :=
    ((Lp.memLp V).integrable (by norm_num)).mono_measure hsub
  have hcoef := Measure.ae_ae_of_ae_comp (show (U+V : Lp ℝ 2 π) =ᵐ[K ∘ₘ π]
      (fun y => U y+V y) from (ae_mono hsub) (Lp.coeFn_add U V))
  apply Lp.ext
  filter_upwards [vector_ae π K hmass hsub (U+V),vector_ae π K hmass hsub U,
    vector_ae π K hmass hsub V,Lp.coeFn_add (vector π K hmass hsub U) (vector π K hmass hsub V),
    hcoef,(Measure.integrable_comp_iff hiU.aestronglyMeasurable).mp hiU |>.1,
    (Measure.integrable_comp_iff hiV.aestronglyMeasurable).mp hiV |>.1]
    with x hUV hU hV he hc hiU hiV
  rw [hUV,he]
  simp only [Pi.add_apply]
  rw [hU,hV]
  exact (integral_congr_ae hc).trans (integral_add hiU hiV)

omit [IsProbabilityMeasure π] in
theorem vector_smul (c : ℝ) (U : Lp ℝ 2 π) :
    vector π K hmass hsub (c • U) = c • vector π K hmass hsub U := by
  have hcoef := Measure.ae_ae_of_ae_comp (show (c • U : Lp ℝ 2 π) =ᵐ[K ∘ₘ π]
      (fun y => c • U y) from (ae_mono hsub) (Lp.coeFn_smul c U))
  apply Lp.ext
  filter_upwards [vector_ae π K hmass hsub (c • U),vector_ae π K hmass hsub U,
    Lp.coeFn_smul c (vector π K hmass hsub U),hcoef] with x hcU hU he hc
  rw [hcU,he]
  simp only [Pi.smul_apply]
  rw [hU]
  exact (integral_congr_ae hc).trans (integral_smul c (fun y => U y))

/-- The bounded operator is constructed from the genuine subprobability
integral, with its norm bound derived by Jensen and subinvariance. -/
def operator : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  LinearMap.mkContinuous
    { toFun := vector π K hmass hsub
      map_add' := vector_add π K hmass hsub
      map_smul' := vector_smul π K hmass hsub }
    1 (fun U => by
      change ‖vector π K hmass hsub U‖ ≤ 1*‖U‖
      rw [one_mul]
      exact vector_norm_le π K hmass hsub U)

theorem operator_ae (U : Lp ℝ 2 π) : operator π K hmass hsub U =ᵐ[π] average K U := by
  change vector π K hmass hsub U =ᵐ[π] average K U
  exact vector_ae π K hmass hsub U

theorem operator_norm_le : ‖operator π K hmass hsub‖ ≤ 1 :=
  (operator π K hmass hsub).opNorm_le_bound zero_le_one
    (fun U => by
      change ‖vector π K hmass hsub U‖ ≤ 1*‖U‖
      rw [one_mul]
      exact vector_norm_le π K hmass hsub U)

end SlowEquilibration.ConditionedEntrance.KilledL2
