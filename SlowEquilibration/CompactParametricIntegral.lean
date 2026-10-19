module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

/-! # Genuine C² parameter integrals over compact time supports -/

namespace SlowEquilibration.CompactParametricIntegral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

lemma integrable_section (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : Set ℝ) (hK : IsCompact K) (hμ : ∀ᵐ t ∂μ, t ∈ K)
    (F : ℝ → E → G) (hF : Continuous (Function.uncurry F)) (x : E) :
    Integrable (fun t => F t x) μ := by
  have hc : Continuous (fun t => F t x) := hF.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  apply (integrable_const C).mono' hc.aestronglyMeasurable
  exact hμ.mono (fun t ht => hC t ht)

/-- Compact-support parameter integration commutes with the actual first
Frechet derivative, proved by the dominated Bochner derivative theorem. -/
theorem hasFDerivAt_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : Set ℝ) (hK : IsCompact K) (hμ : ∀ᵐ t ∂μ, t ∈ K)
    (F : ℝ → E → G) (D : ℝ → E → E →L[ℝ] G)
    (hF : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ t ∈ K, ∀ x, HasFDerivAt (F t) (D t x) x) (x : E) :
    HasFDerivAt (fun z => ∫ t, F t z ∂μ) (∫ t, D t x ∂μ) x := by
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn hD.continuousOn
  have hs : closedBall x 1 ∈ 𝓝 x := closedBall_mem_nhds x (by norm_num)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z t => F t z) (F' := fun z t => D t z) (s := closedBall x 1)
    (bound := fun _ => B) hs
    (Eventually.of_forall (fun z => (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable))
    (integrable_section μ K hK hμ F hF x)
    ((hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (hμ.mono (fun t ht z hz => hB (t, z) ⟨ht, hz⟩)) (integrable_const B)
  exact hμ.mono (fun t ht z _ => hd t ht z)

/-- Actual averaged first-derivative jets are continuous; compactness gives
an integrable uniform bound on every spatial neighborhood. -/
theorem continuous_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : Set ℝ) (hK : IsCompact K) (hμ : ∀ᵐ t ∂μ, t ∈ K)
    (F : ℝ → E → G) (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => ∫ t, F t x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn hF.continuousOn
  apply continuousAt_of_dominated (F := fun z t => F t z) (bound := fun _ => B)
    (Eventually.of_forall (fun z => (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable))
    _ (integrable_const B)
    (Eventually.of_forall (fun t => (hF.comp (continuous_const.prodMk continuous_id)).continuousAt))
  filter_upwards [closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with z hz
  exact hμ.mono (fun t ht => hB (t, z) ⟨ht, hz⟩)

/-- Genuine C¹ regularity of compact-time integration follows from actual
joint value/derivative continuity and actual derivative equations. -/
theorem contDiff_one_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : Set ℝ) (hK : IsCompact K) (hμ : ∀ᵐ t ∂μ, t ∈ K)
    (F : ℝ → E → G) (D : ℝ → E → E →L[ℝ] G)
    (hF : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ t ∈ K, ∀ x, HasFDerivAt (F t) (D t x) x) :
    ContDiff ℝ 1 (fun z => ∫ t, F t z ∂μ) := by
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => ∫ t, D t x ∂μ,
    continuous_integral μ K hK hμ D hD, ?_⟩
  exact hasFDerivAt_integral μ K hK hμ F D hF hD hd

/-- Genuine C² regularity of the compact-time primitive, with both actual
Frechet derivative equations supplied by the already proved C² family. -/
theorem contDiff_two_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (K : Set ℝ) (hK : IsCompact K) (hμ : ∀ᵐ t ∂μ, t ∈ K)
    (F : ℝ → E → G) (D : ℝ → E → E →L[ℝ] G)
    (D₂ : ℝ → E → E →L[ℝ] E →L[ℝ] G)
    (hF : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hD₂ : Continuous (Function.uncurry D₂))
    (hd : ∀ t ∈ K, ∀ x, HasFDerivAt (F t) (D t x) x)
    (hd₂ : ∀ t ∈ K, ∀ x, HasFDerivAt (D t) (D₂ t x) x) :
    ContDiff ℝ 2 (fun z => ∫ t, F t z ∂μ) := by
  refine (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr ⟨fun x => ∫ t, D t x ∂μ, ?_, ?_⟩
  · exact contDiff_one_integral μ K hK hμ D D₂ hD hD₂ hd₂
  · exact hasFDerivAt_integral μ K hK hμ F D hF hD hd

end
end SlowEquilibration.CompactParametricIntegral
