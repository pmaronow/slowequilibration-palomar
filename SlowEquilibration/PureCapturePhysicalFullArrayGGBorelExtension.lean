-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullArrayGGWeakLimit
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Bounded Borel GG observables on genuine physical full-array weak limits.
The weighted-integral uniqueness argument works for any pair of finite laws;
the physical specialization combines it with the bounded-continuous GG identity. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFullArrayGGBorelExtension

open MeasureTheory TopologicalSpace Filter
open scoped BoundedContinuousFunction Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

theorem weighted_integral_eq_of_bounded_continuous
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (p : Y → X) (hp : Measurable p)
    (a : Y → ℝ) (ha : Measurable a)
    (b : X → ℝ) (hb : Measurable b)
    (C : ℝ) (hC : 0 ≤ C)
    (haC : ∀ y, |a y| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hcont : ∀ g : X →ᵇ ℝ,
      (∫ y, g (p y) * a y ∂ν) = (∫ x, g x * b x ∂μ))
    (f : X → ℝ) (hf : Measurable f)
    (hfi : Integrable f (μ + ν.map p)) :
    (∫ y, f (p y) * a y ∂ν) = (∫ x, f x * b x ∂μ) := by
  let τ := μ + ν.map p
  haveI : IsFiniteMeasure (ν.map p) := ν.isFiniteMeasure_map p
  haveI : IsFiniteMeasure τ := by dsimp [τ]; infer_instance
  have hμf : Integrable f μ := hfi.mono_measure (Measure.le_add_right le_rfl)
  have hνmapf : Integrable f (ν.map p) :=
    hfi.mono_measure (Measure.le_add_left le_rfl)
  have hνf : Integrable (f ∘ p) ν := hνmapf.comp_measurable hp
  have hνfa : Integrable (fun y => f (p y) * a y) ν :=
    hνf.mul_bdd ha.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using haC y)
  have hμfb : Integrable (fun x => f x * b x) μ :=
    hμf.mul_bdd hb.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbC x)
  let d : ℝ := (∫ y, f (p y) * a y ∂ν) - (∫ x, f x * b x ∂μ)
  have hd : |d| ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
    have hsmall : 0 < ε / (2 * (C + 1)) := by positivity
    obtain ⟨g, hgerr, _⟩ :=
      hfi.exists_boundedContinuous_integral_sub_le hsmall
    have hμg : Integrable (fun x => g x) μ :=
      BoundedContinuousFunction.integrable μ g
    have hνmapg : Integrable (fun x => g x) (ν.map p) :=
      BoundedContinuousFunction.integrable (ν.map p) g
    have hνg : Integrable (fun y => g (p y)) ν :=
      hνmapg.comp_measurable hp
    have hνga : Integrable (fun y => g (p y) * a y) ν :=
      hνg.mul_bdd ha.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using haC y)
    have hμgb : Integrable (fun x => g x * b x) μ :=
      hμg.mul_bdd hb.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbC x)
    let e : X → ℝ := fun x => f x - g x
    have he : Measurable e := hf.sub g.continuous.measurable
    have hτe : Integrable e τ := hfi.sub (BoundedContinuousFunction.integrable τ g)
    have hμe : Integrable e μ := hτe.mono_measure (Measure.le_add_right le_rfl)
    have hνmape : Integrable e (ν.map p) :=
      hτe.mono_measure (Measure.le_add_left le_rfl)
    have hνe : Integrable (e ∘ p) ν := hνmape.comp_measurable hp
    have hνea : Integrable (fun y => e (p y) * a y) ν :=
      hνe.mul_bdd ha.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using haC y)
    have hμeb : Integrable (fun x => e x * b x) μ :=
      hμe.mul_bdd hb.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbC x)
    have hνdiff : (∫ y, f (p y) * a y ∂ν) -
        (∫ y, g (p y) * a y ∂ν) =
        ∫ y, e (p y) * a y ∂ν := by
      rw [← integral_sub hνfa hνga]
      congr 1
      funext y
      simp [e, sub_mul]
    have hμdiff : (∫ x, f x * b x ∂μ) -
        (∫ x, g x * b x ∂μ) =
        ∫ x, e x * b x ∂μ := by
      rw [← integral_sub hμfb hμgb]
      congr 1
      funext x
      simp [e, sub_mul]
    have hdeq : d = (∫ y, e (p y) * a y ∂ν) -
        (∫ x, e x * b x ∂μ) := by
      dsimp [d]
      rw [← hνdiff, ← hμdiff, hcont g]
      ring
    have hτnorm : Integrable (fun x => ‖e x‖) τ := hτe.norm
    have hμnorm : Integrable (fun x => ‖e x‖) μ :=
      hτnorm.mono_measure (Measure.le_add_right le_rfl)
    have hνmapnorm : Integrable (fun x => ‖e x‖) (ν.map p) :=
      hτnorm.mono_measure (Measure.le_add_left le_rfl)
    have hνnorm : Integrable (fun y => ‖e (p y)‖) ν :=
      hνmapnorm.comp_measurable hp
    have hνnormC : Integrable (fun y => C * ‖e (p y)‖) ν :=
      hνnorm.const_mul C
    have hμnormC : Integrable (fun x => C * ‖e x‖) μ :=
      hμnorm.const_mul C
    have hνerr : |∫ y, e (p y) * a y ∂ν| ≤ C *
        (∫ x, ‖e x‖ ∂τ) := by
      calc
        _ ≤ ∫ y, |e (p y) * a y| ∂ν := abs_integral_le_integral_abs
        _ ≤ ∫ y, C * ‖e (p y)‖ ∂ν := by
          apply integral_mono hνea.norm hνnormC
          intro y
          change ‖e (p y) * a y‖ ≤ C * ‖e (p y)‖
          rw [norm_mul]
          simpa only [Real.norm_eq_abs, mul_comm] using
            mul_le_mul_of_nonneg_left (haC y) (norm_nonneg (e (p y)))
        _ = C * ∫ x, ‖e x‖ ∂(ν.map p) := by
          rw [integral_const_mul]
          exact congrArg (C * ·)
            (integral_map_of_stronglyMeasurable hp he.norm.stronglyMeasurable).symm
        _ ≤ C * ∫ x, ‖e x‖ ∂τ := by
          exact mul_le_mul_of_nonneg_left
            (integral_mono_measure (Measure.le_add_left le_rfl)
              (Filter.Eventually.of_forall fun x => norm_nonneg _) hτnorm) hC
    have hμerr : |∫ x, e x * b x ∂μ| ≤ C *
        (∫ x, ‖e x‖ ∂τ) := by
      calc
        _ ≤ ∫ x, |e x * b x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ x, C * ‖e x‖ ∂μ := by
          apply integral_mono hμeb.norm hμnormC
          intro x
          change ‖e x * b x‖ ≤ C * ‖e x‖
          rw [norm_mul]
          simpa only [Real.norm_eq_abs, mul_comm] using
            mul_le_mul_of_nonneg_left (hbC x) (norm_nonneg (e x))
        _ = C * ∫ x, ‖e x‖ ∂μ := integral_const_mul ..
        _ ≤ C * ∫ x, ‖e x‖ ∂τ := by
          exact mul_le_mul_of_nonneg_left
            (integral_mono_measure (Measure.le_add_right le_rfl)
              (Filter.Eventually.of_forall fun x => norm_nonneg _) hτnorm) hC
    rw [hdeq]
    calc
      |(∫ y, e (p y) * a y ∂ν) - (∫ x, e x * b x ∂μ)| ≤
          |∫ y, e (p y) * a y ∂ν| + |∫ x, e x * b x ∂μ| := abs_sub ..
      _ ≤ 2 * C * (∫ x, ‖e x‖ ∂τ) := by linarith
      _ ≤ 2 * C * (ε / (2 * (C + 1))) := by
        have hh : (∫ x, ‖e x‖ ∂τ) ≤ ε / (2 * (C + 1)) := hgerr
        nlinarith [hC]
      _ ≤ 0 + ε := by
        have hden : 0 < 2 * (C + 1) := by positivity
        field_simp
        nlinarith [hC]
  have hdz : d = 0 := abs_eq_zero.mp (le_antisymm hd (abs_nonneg d))
  exact sub_eq_zero.mp hdz

open SlowEquilibration SphericalModel SphericalForm
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalFullArrayGGTransfer
open SlowEquilibration.PureCapturePhysicalFullArrayGGWeakLimit
open SlowEquilibration.PureCapturePhysicalAsymptoticFullLift

theorem fullArrayCovarianceGGDefect_const_mul
    (μ : FiniteMixture) (m : ℕ) (x : FullOverlapLawArray)
    (g : FullOverlapCoordinates (m+1) → ℝ) (t : ℝ) :
    fullArrayCovarianceGGDefect μ m (fun c => t * g c) x =
      t * fullArrayCovarianceGGDefect μ m g x := by
  unfold fullArrayCovarianceGGDefect
  simp only [mul_assoc, integral_const_mul]
  rw [← Finset.mul_sum]
  ring

theorem fullArrayCovarianceGGDefect_zero_bcf
    (μ : FiniteMixture) (m : ℕ) (x : FullOverlapLawArray)
    (hzero : ∀ g : FullOverlapCoordinates (m+1) → ℝ,
      Continuous g → (∀ c, |g c| ≤ 1) →
      fullArrayCovarianceGGDefect μ m g x = 0)
    (g : FullOverlapCoordinates (m+1) →ᵇ ℝ) :
    fullArrayCovarianceGGDefect μ m g x = 0 := by
  let M : ℝ := max 1 ‖g‖
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left ..)
  let t : ℝ := M⁻¹
  have ht : 0 < t := inv_pos.mpr hM
  have hcont : Continuous (fun c => t * g c) :=
    continuous_const.mul g.continuous
  have hbound (c : FullOverlapCoordinates (m+1)) : |t * g c| ≤ 1 := by
    rw [abs_mul, abs_of_pos ht]
    have hgc : |g c| ≤ M :=
      (show |g c| ≤ ‖g‖ by
        simpa [Real.norm_eq_abs] using g.norm_coe_le_norm c).trans (le_max_right ..)
    calc
      t * |g c| ≤ t * M := mul_le_mul_of_nonneg_left hgc ht.le
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have h := hzero (fun c => t * g c) hcont hbound
  rw [fullArrayCovarianceGGDefect_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left ht.ne'

def ggPairMean (μ : FiniteMixture) (x : FullOverlapLawArray) : ℝ :=
  ∫ c : FullOverlapCoordinates 2, clippedArrayCovariance μ 0 1 c
    ∂(x 2 : Measure (FullOverlapCoordinates 2))

def ggOldWeight (μ : FiniteMixture) (m : ℕ) (x : FullOverlapLawArray)
    (c : FullOverlapCoordinates (m+1)) : ℝ :=
  (ggPairMean μ x + ∑ j : Fin m, clippedArrayCovariance μ 0 j.succ c) /
    ((m : ℝ)+1)

theorem ggOldWeight_continuous (μ : FiniteMixture) (m : ℕ)
    (x : FullOverlapLawArray) : Continuous (ggOldWeight μ m x) := by
  unfold ggOldWeight
  apply Continuous.div_const
  exact continuous_const.add
    (continuous_finsetSum Finset.univ fun j _ => clippedArrayCovariance_continuous μ 0 j.succ)

theorem ggOldWeight_abs_le (μ : FiniteMixture) (m : ℕ)
    (x : FullOverlapLawArray) (c : FullOverlapCoordinates (m+1)) :
    |ggOldWeight μ m x c| ≤
      |ggPairMean μ x| + ((m : ℝ)+1)*μ.xi 1 + 1 := by
  have hxi : 0 ≤ μ.xi 1 := μ.xi_pos (by norm_num) |>.le
  have hsum : |∑ j : Fin m, clippedArrayCovariance μ 0 j.succ c| ≤
      (m : ℝ)*μ.xi 1 := by
    calc
      _ ≤ ∑ j : Fin m, |clippedArrayCovariance μ 0 j.succ c| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _j : Fin m, μ.xi 1 :=
        Finset.sum_le_sum fun j _ => clippedArrayCovariance_abs_le μ 0 j.succ c
      _ = (m : ℝ)*μ.xi 1 := by simp
  have hden : 1 ≤ (m : ℝ)+1 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnum : 0 ≤ |ggPairMean μ x| + (m : ℝ)*μ.xi 1 :=
    add_nonneg (abs_nonneg _) (mul_nonneg (by positivity) hxi)
  unfold ggOldWeight
  rw [abs_div, abs_of_pos (by positivity : 0 < (m : ℝ)+1)]
  calc
    |ggPairMean μ x + ∑ j : Fin m, clippedArrayCovariance μ 0 j.succ c| /
        ((m : ℝ)+1) ≤
      (|ggPairMean μ x| + (m : ℝ)*μ.xi 1) / ((m : ℝ)+1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (abs_add_le ..).trans (add_le_add (le_refl _) hsum)
    _ ≤ |ggPairMean μ x| + (m : ℝ)*μ.xi 1 :=
      div_le_self hnum hden
    _ ≤ |ggPairMean μ x| + ((m : ℝ)+1)*μ.xi 1 + 1 := by
      nlinarith

theorem ggFresh_abs_le (μ : FiniteMixture) (m : ℕ)
    (x : FullOverlapLawArray) (c : FullOverlapCoordinates (m+2)) :
    |clippedArrayCovariance μ 0 (Fin.last (m+1)) c| ≤
      |ggPairMean μ x| + ((m : ℝ)+1)*μ.xi 1 + 1 := by
  have hxi : 0 ≤ μ.xi 1 := μ.xi_pos (by norm_num) |>.le
  exact (clippedArrayCovariance_abs_le μ 0 (Fin.last (m+1)) c).trans (by nlinarith [abs_nonneg (ggPairMean μ x)])

theorem ggOldWeight_integral (μ : FiniteMixture) (m : ℕ)
    (x : FullOverlapLawArray)
    (g : FullOverlapCoordinates (m+1) → ℝ)
    (hg : Integrable g (x (m+1) : Measure (FullOverlapCoordinates (m+1)))) :
    (∫ c, g c * ggOldWeight μ m x c
      ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) =
    (∫ c, g c ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) *
      ggPairMean μ x / ((m : ℝ)+1) +
    (∑ j : Fin m, ∫ c, g c * clippedArrayCovariance μ 0 j.succ c
      ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) /
      ((m : ℝ)+1) := by
  let ν : Measure (FullOverlapCoordinates (m+1)) := x (m+1)
  haveI : IsFiniteMeasure ν := inferInstance
  have hcov (j : Fin m) : Integrable
      (fun c : FullOverlapCoordinates (m+1) =>
        g c * clippedArrayCovariance μ 0 j.succ c) ν :=
    hg.mul_bdd (clippedArrayCovariance_continuous μ 0 j.succ).measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun c => by
        simpa [Real.norm_eq_abs] using clippedArrayCovariance_abs_le μ 0 j.succ c)
  have hsum : Integrable (fun c : FullOverlapCoordinates (m+1) =>
      ∑ j : Fin m, g c * clippedArrayCovariance μ 0 j.succ c) ν :=
    integrable_finsetSum _ (fun j _ => hcov j)
  have hmean : Integrable (fun c : FullOverlapCoordinates (m+1) =>
      g c * ggPairMean μ x) ν := hg.mul_const _
  calc
    (∫ c, g c * ggOldWeight μ m x c ∂ν) =
      (∫ c, (g c * ggPairMean μ x +
        ∑ j : Fin m, g c * clippedArrayCovariance μ 0 j.succ c) /
          ((m : ℝ)+1) ∂ν) := by
            congr 1
            funext c
            simp only [ggOldWeight]
            rw [← mul_div_assoc, mul_add, Finset.mul_sum]
    _ = (∫ c, g c * ggPairMean μ x ∂ν) / ((m : ℝ)+1) +
      (∫ c, ∑ j : Fin m, g c * clippedArrayCovariance μ 0 j.succ c ∂ν) /
          ((m : ℝ)+1) := by
            rw [integral_div]
            rw [integral_add hmean hsum]
            ring
    _ = (∫ c, g c ∂ν) * ggPairMean μ x / ((m : ℝ)+1) +
      (∑ j : Fin m, ∫ c, g c * clippedArrayCovariance μ 0 j.succ c ∂ν) /
          ((m : ℝ)+1) := by
            rw [integral_mul_const, integral_finsetSum]
            intro i _
            exact hcov i

theorem fullArrayCovarianceGGDefect_zero_borel
    (μ : FiniteMixture) (m : ℕ) (x : FullOverlapLawArray)
    (hzero : ∀ g : FullOverlapCoordinates (m+1) → ℝ,
      Continuous g → (∀ c, |g c| ≤ 1) →
      fullArrayCovarianceGGDefect μ m g x = 0)
    (f : FullOverlapCoordinates (m+1) → ℝ)
    (hf : Measurable f) (hfb : ∀ c, |f c| ≤ 1) :
    fullArrayCovarianceGGDefect μ m f x = 0 := by
  let A := FullOverlapCoordinates (m+1)
  let B := FullOverlapCoordinates (m+2)
  let ν : Measure A := x (m+1)
  let ρ : Measure B := x (m+2)
  let p : B → A := fullOverlapPrefix
  let a : B → ℝ := clippedArrayCovariance μ 0 (Fin.last (m+1))
  let b : A → ℝ := ggOldWeight μ m x
  let C : ℝ := |ggPairMean μ x| + ((m : ℝ)+1)*μ.xi 1 + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    have hxi : 0 ≤ μ.xi 1 := (μ.xi_pos (by norm_num)).le
    positivity
  have hcont (g : A →ᵇ ℝ) :
      (∫ c, g (p c) * a c ∂ρ) = (∫ c, g c * b c ∂ν) := by
    have hGG := fullArrayCovarianceGGDefect_zero_bcf μ m x hzero g
    have hOld := ggOldWeight_integral μ m x g
      (BoundedContinuousFunction.integrable ν g)
    unfold fullArrayCovarianceGGDefect at hGG
    dsimp [ν, ρ, p, a, b] at *
    simp only [ggPairMean] at hOld
    linarith
  haveI : IsFiniteMeasure (ρ.map p) := ρ.isFiniteMeasure_map p
  haveI : IsFiniteMeasure (ν + ρ.map p) := inferInstance
  have hfi : Integrable f (ν + ρ.map p) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun c => by
        simpa [Real.norm_eq_abs] using hfb c)
  have hweighted := weighted_integral_eq_of_bounded_continuous
    ν ρ p fullOverlapPrefix_continuous.measurable a
    (clippedArrayCovariance_continuous μ 0 (Fin.last (m+1))).measurable
    b (ggOldWeight_continuous μ m x).measurable C hC
    (ggFresh_abs_le μ m x) (ggOldWeight_abs_le μ m x) hcont f hf hfi
  have hνf : Integrable f ν := hfi.mono_measure (Measure.le_add_right le_rfl)
  have hOld := ggOldWeight_integral μ m x f hνf
  unfold fullArrayCovarianceGGDefect
  dsimp [ν, ρ, p, a, b] at hweighted hOld
  simp only [ggPairMean] at hOld
  linarith

/-- The true sublinear physical energy budget enforces GG for every bounded
Borel observable of a finite overlap array on every physical weak limit. -/
theorem fullArrayCovarianceGGDefect_eq_zero_borel_of_sublinear_budget
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (f : FullOverlapCoordinates (m+1) → ℝ)
    (hf : Measurable f) (hfb : ∀ c, |f c| ≤ 1)
    (hbudget : Tendsto (fun n : ℕ =>
      (GaussianPerturbationDeviation.meanThermalDeviation
          (PureCapturePhysicalShellGG.shellLaw (n+2))
          (PureCapturePhysicalShellGG.shellLinear (mixtureCoefficients μ))
          (fun _ => true) β +
        GaussianPerturbationIntegrated.energyFluctuation
          (PureCapturePhysicalShellGG.shellLaw (n+2))
          (PureCapturePhysicalShellGG.shellLinear (mixtureCoefficients μ))
          (fun _ => true) β) / ((n+2 : ℕ) : ℝ)) atTop (𝓝 0))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    fullArrayCovarianceGGDefect μ m f x = 0 := by
  apply fullArrayCovarianceGGDefect_zero_borel μ m x _ f hf hfb
  intro g hg hgb
  exact fullArrayCovarianceGGDefect_eq_zero_of_sublinear_budget
    μ hβ m g hg hgb hbudget hx

end SlowEquilibration.PureCapturePhysicalFullArrayGGBorelExtension
