-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Support

/-! A jointly continuous scalar family with one compact support varies
continuously in the actual uniform norm of bounded continuous functions. -/
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace SlowEquilibration.CompactSupportedCoefficientFamily
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {Θ X : Type*} [TopologicalSpace Θ] [TopologicalSpace X]

def boundedFamily (K : Set X) (hK : IsCompact K) (F : Θ × X → ℝ) (hF : Continuous F)
    (hSupp : ∀ p,Function.support (fun x => F (p,x)) ⊆ K) (p : Θ) : X →ᵇ ℝ := by
  let hf : Continuous (fun x => F (p,x)) := hF.comp (continuous_const.prodMk continuous_id)
  let hb := hK.exists_bound_of_continuousOn hf.continuousOn
  exact BoundedContinuousFunction.ofNormedAddCommGroup _ hf (max hb.choose 0) (fun x => by
    by_cases hx : x∈K
    · exact (hb.choose_spec x hx).trans (le_max_left _ _)
    · have hz : F (p,x)=0 := by
        by_contra hne
        exact hx (hSupp p hne)
      rw [hz,norm_zero]
      exact le_max_right _ _)

theorem boundedFamily_apply (K : Set X) (hK : IsCompact K) (F : Θ × X → ℝ)
    (hF : Continuous F) (hSupp : ∀ p,Function.support (fun x => F (p,x)) ⊆ K)
    (p : Θ) (x : X) : boundedFamily K hK F hF hSupp p x=F (p,x) := rfl

/-- Actual uniform-norm parameter continuity is derived from joint
continuity on the fixed compact support, with zero off that support. -/
theorem boundedFamily_continuous (K : Set X) (hK : IsCompact K) (F : Θ × X → ℝ)
    (hF : Continuous F) (hSupp : ∀ p,Function.support (fun x => F (p,x)) ⊆ K) :
    Continuous (boundedFamily K hK F hF hSupp) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : Θ → C(K,ℝ) := fun p => ⟨fun x => F (p,x.val),
    hF.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hC : Continuous C := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hnorm (p q : Θ) : ‖boundedFamily K hK F hF hSupp p-boundedFamily K hK F hF hSupp q‖ ≤ ‖C p-C q‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    by_cases hx : x∈K
    · exact (C p-C q).norm_coe_le_norm ⟨x,hx⟩
    · have hp : F (p,x)=0 := by
        by_contra hne
        exact hx (hSupp p hne)
      have hq : F (q,x)=0 := by
        by_contra hne
        exact hx (hSupp q hne)
      simp only [BoundedContinuousFunction.sub_apply,boundedFamily_apply,hp,hq,sub_self,norm_zero]
      exact norm_nonneg _
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun q => ‖C q-C p‖) (𝓝 p) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using ((hC.tendsto p).sub_const (C p)).norm
  exact squeeze_zero (fun q => norm_nonneg _) (fun q => hnorm q p) hz

end SlowEquilibration.CompactSupportedCoefficientFamily
