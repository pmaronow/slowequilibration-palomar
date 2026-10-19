-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetBounds

/-! Sharp absolute-supremum comparison obtained by adjoining the genuine zero
observable. This avoids any loss from combining the two signs in the metric. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianSharpAbsoluteMaximum
open MeasureTheory Set
open scoped RealInnerProductSpace
open GaussianCompactMaximum GaussianCompactFeatureComparison PureTensorJetBounds
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι κ V : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [TopologicalSpace V] [CompactSpace V] [Nonempty V]

def withZero (a : V → EuclideanSpace ℝ ι) : Unit ⊕ V → EuclideanSpace ℝ ι :=
  Sum.elim (fun _ => 0) a

theorem withZero_continuous (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Continuous (withZero a) := continuous_sumElim.mpr ⟨continuous_const, ha⟩

def positiveSupremum (a : V → EuclideanSpace ℝ ι) (g : EuclideanSpace ℝ ι) : ℝ :=
  ⨆ v : Unit ⊕ V, inner ℝ (withZero a v) g

theorem positiveSupremum_integrable (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Integrable (positiveSupremum a) (SYK.standardGaussianMeasureOnEuclidean ι) :=
  supremum_integrable_of_continuous (fun v => innerSL ℝ (withZero a v))
    ((innerSL ℝ).continuous.comp (withZero_continuous a ha))

theorem le_positiveSupremum (a : V → EuclideanSpace ℝ ι) (ha : Continuous a)
    (g : EuclideanSpace ℝ ι) (v : Unit ⊕ V) :
    inner ℝ (withZero a v) g ≤ positiveSupremum a g := by
  obtain ⟨K, _, hK⟩ := exists_feature_bound (fun v => innerSL ℝ (withZero a v))
    ((innerSL ℝ).continuous.comp (withZero_continuous a ha))
  exact le_field_supremum _ hK g v

theorem positiveSupremum_nonneg (a : V → EuclideanSpace ℝ ι) (ha : Continuous a)
    (g : EuclideanSpace ℝ ι) : 0 ≤ positiveSupremum a g := by
  simpa [withZero] using le_positiveSupremum a ha g (.inl ())

theorem expected_positiveSupremum_le (a : V → EuclideanSpace ℝ ι)
    (z : V → EuclideanSpace ℝ κ) (ha : Continuous a) (hz : Continuous z)
    {L : ℝ} (hL : 0 ≤ L) (haL : ∀ v, ‖a v‖ ≤ L) (hz1 : ∀ v, ‖z v‖ = 1)
    (hinc : ∀ v w, ‖a v-a w‖ ≤ L*‖z v-z w‖) :
    (∫ g, positiveSupremum a g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      L * Real.sqrt (Fintype.card κ) := by
  let b : V → EuclideanSpace ℝ κ := fun v => L • z v
  have hb : Continuous b := hz.const_smul L
  have hcomp := expected_supremum_comparison_of_increment_norm
    (withZero a) (withZero b) (withZero_continuous a ha) (withZero_continuous b hb)
    (fun v w => by
      cases v with
      | inl v =>
        cases w with
        | inl w => simp [withZero]
        | inr w => simpa [withZero,b,norm_smul,abs_of_nonneg hL,hz1] using haL w
      | inr v =>
        cases w with
        | inl w => simpa [withZero,b,norm_smul,abs_of_nonneg hL,hz1] using haL v
        | inr w => simpa [withZero,b,← smul_sub,norm_smul,abs_of_nonneg hL] using hinc v w)
  have henv (g : EuclideanSpace ℝ κ) : positiveSupremum b g ≤ L*‖g‖ := by
    apply ciSup_le
    intro v
    cases v with
    | inl v => simpa [withZero] using mul_nonneg hL (norm_nonneg g)
    | inr v =>
      exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (by simp [withZero,b,norm_smul,abs_of_nonneg hL,hz1]))
  have hh := integral_mono (positiveSupremum_integrable b hb)
    (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul L) henv
  rw [integral_const_mul] at hh
  exact hcomp.trans (hh.trans (mul_le_mul_of_nonneg_left
    (GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card κ) hL))

/-- The exact factor two in the manuscript comparison bound. -/
theorem expected_absoluteSupremum_le_twice (a : V → EuclideanSpace ℝ ι)
    (z : V → EuclideanSpace ℝ κ) (ha : Continuous a) (hz : Continuous z)
    {L : ℝ} (hL : 0 ≤ L) (haL : ∀ v, ‖a v‖ ≤ L) (hz1 : ∀ v, ‖z v‖ = 1)
    (hinc : ∀ v w, ‖a v-a w‖ ≤ L*‖z v-z w‖) :
    (∫ g, absoluteSupremum a g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      2 * L * Real.sqrt (Fintype.card κ) := by
  have hneg : Continuous (fun v => -a v) := ha.neg
  have hh (g : EuclideanSpace ℝ ι) : absoluteSupremum a g ≤
      positiveSupremum a g + positiveSupremum (fun v => -a v) g := by
    apply ciSup_le
    intro v
    rcases v with ⟨s,v⟩
    cases s
    · have ht := le_positiveSupremum (fun v => -a v) hneg g (.inr v)
      have hn := positiveSupremum_nonneg a ha g
      simpa only [withZero,Sum.elim_inr,signedFeature,sign,Bool.false_eq_true,ite_false,
        neg_one_smul] using ht.trans (le_add_of_nonneg_left hn)
    · have ht := le_positiveSupremum a ha g (.inr v)
      have hn := positiveSupremum_nonneg (fun v => -a v) hneg g
      simpa only [withZero,Sum.elim_inr,signedFeature,sign,ite_true,one_smul]
        using ht.trans (le_add_of_nonneg_right hn)
  have hi := integral_mono (absoluteSupremum_integrable a ha)
    ((positiveSupremum_integrable a ha).add (positiveSupremum_integrable _ hneg)) hh
  simp only [Pi.add_apply] at hi
  rw [integral_add (positiveSupremum_integrable a ha) (positiveSupremum_integrable _ hneg)] at hi
  have hp := expected_positiveSupremum_le a z ha hz hL haL hz1 hinc
  have hm := expected_positiveSupremum_le (fun v => -a v) z hneg hz hL
    (by simpa using haL) hz1 (by intro v w; rw [neg_sub_neg, norm_sub_rev]; exact hinc v w)
  linarith

end SlowEquilibration.GaussianSharpAbsoluteMaximum
