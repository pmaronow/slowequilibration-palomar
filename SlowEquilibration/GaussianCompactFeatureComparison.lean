-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCompactMaximum
public import Mathlib.Probability.ProductMeasure

/-!
# Compact Gaussian comparison on independent coefficient spaces

The two actual coefficient spaces are joined by their genuine product Gaussian
law. Their increment norm comparison is exactly the signed covariance
comparison required by compact Sudakov--Fernique.
-/

@[expose] public section

namespace SlowEquilibration.GaussianCompactFeatureComparison

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open GaussianSpinComparison GaussianSpinInterpolation GaussianCompactMaximum
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Actual split into the two disjoint original Gaussian coefficient blocks. -/
def sumSplit : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ]
    EuclideanSpace ℝ ι × EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (WithLp.toLp 2 (fun i => w (.inl i)),
        WithLp.toLp 2 (fun j => w (.inr j)))
      map_add' := by intro w z; ext i <;> rfl
      map_smul' := by intro a w; ext i <;> rfl }

/-- Actual coordinate joining map used by the comparison features. -/
def sumJoin : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →L[ℝ]
    EuclideanSpace ℝ (ι ⊕ κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (Sum.elim p.1 p.2)
      map_add' := by intro p q; ext (i | j) <;> rfl
      map_smul' := by intro a p; ext (i | j) <;> rfl }

/-- The true joined standard Gaussian splits into independent standard
Gaussians on the original coefficient spaces. -/
theorem sumSplit_gaussian_map :
    (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)).map (sumSplit (ι := ι) (κ := κ)) =
      (SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean κ) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  have he := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => gaussianReal 0 1)
  have hs : sumSplit ∘ (WithLp.toLp 2 : (ι ⊕ κ → ℝ) → EuclideanSpace ℝ (ι ⊕ κ)) =
      (Prod.map (WithLp.toLp 2) (WithLp.toLp 2)) ∘ e := rfl
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map sumSplit.continuous.measurable (by fun_prop), hs,
    ← Measure.map_map (by fun_prop) e.measurable, he.map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

def blockLabel : ι ⊕ κ → Bool := Sum.elim (fun _ => true) (fun _ => false)

def combinedLinear (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] ℝ :=
  innerSL ℝ (sumJoin (a v, b v))

theorem combinedLinear_apply (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) (w : EuclideanSpace ℝ (ι ⊕ κ)) :
    combinedLinear a b v w = inner ℝ (a v) (sumSplit w).1 + inner ℝ (b v) (sumSplit w).2 := by
  simp only [combinedLinear, innerSL_apply_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  rfl

@[simp] theorem combinedLinear_coordinate (a : V → EuclideanSpace ℝ ι)
    (b : V → EuclideanSpace ℝ κ) (v : V) (i : ι ⊕ κ) :
    coordinateObservable (combinedLinear a b) i v = Sum.elim (a v) (b v) i := by
  simp only [coordinateObservable, combinedLinear, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rfl

theorem combined_signedKernel (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v u : V) :
    signedKernel (combinedLinear a b) blockLabel v u =
      inner ℝ (b v) (b u) - inner ℝ (a v) (a u) := by
  simp only [signedKernel, combinedLinear_coordinate, Fintype.sum_sum_type,
    covarianceSign, blockLabel, Sum.elim_inl, Sum.elim_inr, Bool.true_eq_false,
    Bool.false_eq_true, ite_true, ite_false, neg_one_mul, one_mul, Finset.sum_neg_distrib,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [mul_comm, sub_eq_add_neg, add_comm]

theorem combined_increment_nonnegative (a : V → EuclideanSpace ℝ ι)
    (b : V → EuclideanSpace ℝ κ)
    (hinc : ∀ v u, ‖a v - a u‖ ≤ ‖b v - b u‖) (v u : V) :
    0 ≤ signedKernel (combinedLinear a b) blockLabel v v +
      signedKernel (combinedLinear a b) blockLabel u u -
        2 * signedKernel (combinedLinear a b) blockLabel v u := by
  rw [combined_signedKernel, combined_signedKernel, combined_signedKernel,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hinc v u)
  rw [norm_sub_sq_real, norm_sub_sq_real] at hs
  linarith

theorem combined_rotation_zero (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) (w : EuclideanSpace ℝ (ι ⊕ κ)) :
    combinedLinear a b v (rotation blockLabel 0 w) = inner ℝ (a v) (sumSplit w).1 := by
  rw [combinedLinear_apply]
  have h1 : (sumSplit (rotation blockLabel 0 w)).1 = (sumSplit w).1 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  have h2 : (sumSplit (rotation blockLabel 0 w)).2 = 0 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  rw [h1, h2, inner_zero_right, add_zero]

theorem combined_rotation_pi_div_two (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (v : V) (w : EuclideanSpace ℝ (ι ⊕ κ)) :
    combinedLinear a b v (rotation blockLabel (Real.pi / 2) w) = inner ℝ (b v) (sumSplit w).2 := by
  rw [combinedLinear_apply]
  have h1 : (sumSplit (rotation blockLabel (Real.pi / 2) w)).1 = 0 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  have h2 : (sumSplit (rotation blockLabel (Real.pi / 2) w)).2 = (sumSplit w).2 := by
    ext i
    simp [sumSplit, rotation_apply, rotationCoefficient, blockLabel]
  rw [h1, h2, inner_zero_right, zero_add]

variable [TopologicalSpace V] [CompactSpace V] [Nonempty V]

/-- Sudakov--Fernique for two genuine Gaussian feature fields on independent
coefficient spaces, stated solely through the true feature increment norms. -/
theorem expected_supremum_comparison_of_increment_norm
    (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (ha : Continuous a) (hb : Continuous b)
    (hinc : ∀ v u, ‖a v - a u‖ ≤ ‖b v - b u‖) :
    (∫ g, (⨆ v, inner ℝ (a v) g) ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      ∫ g, (⨆ v, inner ℝ (b v) g) ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  have hL : Continuous (combinedLinear a b) :=
    (innerSL ℝ).continuous.comp (sumJoin.continuous.comp (ha.prodMk hb))
  have hc := expected_supremum_comparison (combinedLinear a b) hL blockLabel
    (combined_increment_nonnegative a b hinc)
  simp only [combined_rotation_zero, combined_rotation_pi_div_two] at hc
  have hsplit : MeasurePreserving (sumSplit (ι := ι) (κ := κ))
      (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ))
      ((SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean κ)) :=
    ⟨sumSplit.continuous.measurable, sumSplit_gaussian_map⟩
  have hfst := measurePreserving_fst.comp hsplit
  have hsnd := measurePreserving_snd.comp hsplit
  have hAf := (innerSL ℝ).continuous.comp ha
  have hBf := (innerSL ℝ).continuous.comp hb
  obtain ⟨Ka, _, hba⟩ := exists_feature_bound (fun v => innerSL ℝ (a v)) hAf
  obtain ⟨Kb, _, hbb⟩ := exists_feature_bound (fun v => innerSL ℝ (b v)) hBf
  have hAc := (field_supremum_lipschitz (fun v => innerSL ℝ (a v)) hba).continuous
  have hBc := (field_supremum_lipschitz (fun v => innerSL ℝ (b v)) hbb).continuous
  have hla : HasLaw (fun w => (sumSplit (ι := ι) (κ := κ) w).1)
      (SYK.standardGaussianMeasureOnEuclidean ι) (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)) :=
    ⟨hfst.measurable.aemeasurable, hfst.map_eq⟩
  have hlb : HasLaw (fun w => (sumSplit (ι := ι) (κ := κ) w).2)
      (SYK.standardGaussianMeasureOnEuclidean κ) (SYK.standardGaussianMeasureOnEuclidean (ι ⊕ κ)) :=
    ⟨hsnd.measurable.aemeasurable, hsnd.map_eq⟩
  have hea := hla.integral_comp hAc.aestronglyMeasurable
  have heb := hlb.integral_comp hBc.aestronglyMeasurable
  simp only [Function.comp_def, innerSL_apply_apply] at hea heb
  rwa [hea, heb] at hc

end
end SlowEquilibration.GaussianCompactFeatureComparison
