module
-- SPDX-License-Identifier: Apache-2.0

public import QuantitativePaper.SmoothIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

/-! # Genuine smooth compact-parameter integration -/

namespace SlowEquilibration.CompactParameterSmoothIntegral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

variable {A E G : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Actual partial spatial iterated jets of a jointly smooth family are
jointly smooth. This is a chain rule and currying argument. -/
theorem partialJets_contDiff (F : A → E → G) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun q : A × E => iteratedFDeriv ℝ j (F q.1) q.2) := by
  induction j with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry] using
      ((continuousMultilinearCurryFin0 ℝ E G).symm.contDiff.comp hF)
  | succ j ih =>
    let D : A → E → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) G :=
      fun a x => iteratedFDeriv ℝ j (F a) x
    have hD : ContDiff ℝ ∞ (Function.uncurry D) := ih
    have hmap : ContDiff ℝ ∞ (fun q : (A × E) × E => (q.1.1, q.2)) :=
      (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
    have hfamily : ContDiff ℝ ∞ (Function.uncurry (fun q : A × E => D q.1)) :=
      hD.comp hmap
    have hd : ContDiff ℝ ∞ (fun q : A × E => fderiv ℝ (D q.1) q.2) :=
      hfamily.fderiv contDiff_snd (by simp)
    simpa only [D, iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Function.uncurry] using
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) G).symm.contDiff.comp hd)

/-- Integration of a true jointly smooth family with compact parameter
support is smooth. Actual jets are bounded on compact spatial neighborhoods,
and the dominated higher derivative theorem supplies the conclusion. -/
theorem contDiff_integral (μ : Measure A) [IsFiniteMeasure μ]
    (F : A → E → G) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (K : Set A) (hK : IsCompact K) (hzero : ∀ a ∉ K, ∀ x, F a x = 0) :
    ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  rw [contDiff_infty]
  intro N
  apply QuantitativePaper.contDiff_integral_of_dominated_derivatives N μ (fun x a => F a x)
  · intro a
    exact ((hF.comp (contDiff_const.prodMk contDiff_id))).of_le (by simp)
  · intro j hj x
    exact ((partialJets_contDiff F hF j).continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro x
    choose C hC using fun j : ℕ => (hK.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
      (partialJets_contDiff F hF j).continuous.continuousOn
    refine ⟨closedBall x 1, closedBall_mem_nhds x (by norm_num),
      fun j _ => max (C j) 0, fun j _ => integrable_const _, ?_⟩
    intro j hj y hy a
    by_cases ha : a ∈ K
    · exact (hC j (a,y) ⟨ha,hy⟩).trans (le_max_left _ _)
    · have he : F a = fun _ => (0 : G) := funext (hzero a ha)
      rw [he]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using (le_max_right (C j) 0)

end
end SlowEquilibration.CompactParameterSmoothIntegral
