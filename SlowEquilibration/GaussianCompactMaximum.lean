-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiniteMaximum
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compact-index Gaussian supremum comparison

The compact feature image has deterministic finite operator-norm nets. Actual
Gaussian suprema are Lipschitz functions of the Gaussian input and have an
integrable Gaussian norm envelope. The finite Sudakov--Fernique comparison
therefore passes to the genuine compact supremum with a proved net error.
-/

@[expose] public section

namespace SlowEquilibration.GaussianCompactMaximum

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open GaussianSpinComparison GaussianSpinInterpolation GaussianFiniteMaximum
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Nonempty V]

theorem field_bddAbove (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    BddAbove (range (fun v => L v w)) := by
  refine ⟨K * ‖w‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (le_abs_self _).trans ((L v).le_opNorm w |>.trans
    (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg w)))

/-- Every actual field value lies below the genuine compact supremum. -/
theorem le_field_supremum (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) (v : V) :
    L v w ≤ ⨆ u, L u w := le_ciSup (field_bddAbove L hb w) v

/-- The true supremum has the actual uniform Gaussian norm envelope. -/
theorem norm_field_supremum_le (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (w : EuclideanSpace ℝ ι) :
    ‖⨆ v, L v w‖ ≤ K * ‖w‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · let v : V := Classical.choice inferInstance
    have h := (L v).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg w))
    exact (neg_le_of_abs_le h).trans (le_field_supremum L hb w v)
  · exact ciSup_le fun v => (le_abs_self _).trans ((L v).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg w)))

/-- The actual supremum is Lipschitz in all original Gaussian coordinates. -/
theorem field_supremum_lipschitz (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) :
    LipschitzWith (Real.toNNReal K) (fun w => ⨆ v, L v w) := by
  apply LipschitzWith.of_le_add_mul' K
  intro w z
  apply ciSup_le
  intro v
  have hdiff : L v w - L v z ≤ K * dist w z := by
    rw [← map_sub, dist_eq_norm]
    exact (le_abs_self _).trans ((L v).le_opNorm (w - z) |>.trans
      (mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _)))
  have hz := le_field_supremum L hb z v
  linarith

/-- Integrability of the genuine rotated supremum, with no countability
restriction on the index type. -/
theorem supremum_rotated_integrable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v, ‖L v‖ ≤ K) (label : ι → Bool) (θ : ℝ) :
    Integrable (fun w => ⨆ v, L v (rotation label θ w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc := (field_supremum_lipschitz L hb).continuous.comp (rotation label θ).continuous
  apply (gaussian_norm_integrable.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => (norm_field_supremum_le L hb _).trans
    (mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) hK)

/-- A deterministic finite feature net approximates every actual field
supremum with its exact operator-norm error bound. -/
theorem finite_net_supremum_bounds (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ v, ‖L v‖ ≤ K) (s : Finset V) [Nonempty s]
    {ε : ℝ} (hnet : ∀ v, ∃ u ∈ s, ‖L v - L u‖ ≤ ε) (w : EuclideanSpace ℝ ι) :
    maximum (fun u : s => L u w) ≤ (⨆ v, L v w) ∧
      (⨆ v, L v w) ≤ maximum (fun u : s => L u w) + ε * ‖w‖ := by
  constructor
  · exact maximum_le _ fun u => le_field_supremum L hb w u
  · apply ciSup_le
    intro v
    obtain ⟨u, hu, hdist⟩ := hnet v
    have hdiff : L v w - L u w ≤ ε * ‖w‖ := by
      change (L v - L u) w ≤ _
      exact (le_abs_self _).trans ((L v - L u).le_opNorm w |>.trans
        (mul_le_mul_of_nonneg_right hdist (norm_nonneg w)))
    have hmax := le_maximum (fun a : s => L a w) ⟨u, hu⟩
    linarith

variable [TopologicalSpace V] [CompactSpace V]

/-- Compact continuity supplies the uniform operator bound used by the
actual Gaussian envelope. -/
theorem exists_feature_bound (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖L v‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_range hL.norm).bddAbove
  have hb : ∀ v, ‖L v‖ ≤ K := fun v => hK (mem_range_self v)
  exact ⟨K, (norm_nonneg (L (Classical.choice inferInstance))).trans
    (hb (Classical.choice inferInstance)), hb⟩

/-- A finite set of actual indices approximates the entire feature map in
operator norm. This net is deterministic, independent of the disorder. -/
theorem exists_finite_feature_net (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Continuous L) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v, ∃ u ∈ s, ‖L v - L u‖ < ε := by
  classical
  let U : V → Set V := fun u => {v | ‖L v - L u‖ < ε}
  have hU : ∀ u, IsOpen (U u) := fun u =>
    isOpen_lt (hL.sub continuous_const).norm continuous_const
  have hcover : univ ⊆ ⋃ u, U u := by
    intro v _
    exact mem_iUnion.mpr ⟨v, by simpa [U] using hε⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hnet : ∀ v, ∃ u ∈ s, ‖L v - L u‖ < ε := by
    intro v
    simpa only [mem_iUnion, U, mem_setOf_eq, exists_prop] using hs (mem_univ v)
  refine ⟨s, ?_, hnet⟩
  obtain ⟨u, hu, _⟩ := hnet (Classical.choice inferInstance)
  exact ⟨u, hu⟩

/-- Continuity on a compact index space gives an integrable actual Gaussian
supremum at every rotation. -/
theorem supremum_rotated_integrable_of_continuous
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L)
    (label : ι → Bool) (θ : ℝ) :
    Integrable (fun w => ⨆ v, L v (rotation label θ w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨K, hK, hb⟩ := exists_feature_bound L hL
  exact supremum_rotated_integrable L hK hb label θ

/-- Compact-index Sudakov--Fernique for the actual Gaussian fields. The
covariance hypothesis compares actual increments and does not impose constant
pointwise variance or assume the desired supremum comparison. -/
theorem expected_supremum_comparison
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Continuous L)
    (label : ι → Bool)
    (hinc : ∀ v u, 0 ≤ signedKernel L label v v + signedKernel L label u u -
      2 * signedKernel L label v u) :
    (∫ w, (⨆ v, L v (rotation label 0 w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    ∫ w, (⨆ v, L v (rotation label (Real.pi / 2) w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  classical
  obtain ⟨K, hK, hb⟩ := exists_feature_bound L hL
  have hi (θ : ℝ) := supremum_rotated_integrable L hK hb label θ
  let M : ℝ := ∫ w : EuclideanSpace ℝ ι, ‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / (M + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hεeq : ε * (M + 1) = δ := by
    exact div_mul_cancel₀ _ (by linarith)
  obtain ⟨s, hs, hnet⟩ := exists_finite_feature_net L hL hε
  obtain ⟨v₀, hv₀⟩ := hs
  letI : Nonempty s := ⟨⟨v₀, hv₀⟩⟩
  letI : MeasurableSpace s := ⊤
  letI : MeasurableSingletonClass s := ⟨fun _ => trivial⟩
  have hnet' : ∀ v, ∃ u ∈ s, ‖L v - L u‖ ≤ ε := by
    intro v
    obtain ⟨u, hu, hdist⟩ := hnet v
    exact ⟨u, hu, hdist.le⟩
  have hiF (θ : ℝ) := maximum_rotated_integrable (fun u : s => L u)
    hK (fun u => hb u) label θ
  have hcomp := expected_maximum_comparison (fun u : s => L u) label
    (fun v u => hinc v u)
  have hup := integral_mono (hi 0)
    ((hiF 0).fun_add (gaussian_norm_integrable.const_mul ε)) (fun w => by
      have h := (finite_net_supremum_bounds L hb s hnet' (rotation label 0 w)).2
      exact h.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (rotation_norm_le label 0 w) hε.le)))
  rw [integral_add (hiF 0) (gaussian_norm_integrable.const_mul ε), integral_const_mul] at hup
  have hlo := integral_mono (hiF (Real.pi / 2)) (hi (Real.pi / 2))
    (fun w => (finite_net_supremum_bounds L hb s hnet' (rotation label (Real.pi / 2) w)).1)
  change _ ≤ _ + ε * M at hup
  nlinarith

end
end SlowEquilibration.GaussianCompactMaximum
