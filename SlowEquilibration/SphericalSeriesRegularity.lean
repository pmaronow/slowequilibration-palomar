-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalIntrinsicExtension
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Uniform summable jets on the closed physical ball give genuine intrinsic
regularity of the literal sphere series, including the boundary of that ball. -/

@[expose] public section
namespace SlowEquilibration.SphericalSeriesRegularity

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A derivative series extends to the boundary of a positive-radius closed
ball: uniform convergence supplies continuous boundary values of both jets. -/
theorem hasFDerivWithinAt_tsum_closedBall
    (f : ℕ → E → F) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (c : E) {r : ℝ} (hr : 0 < r) (u v : ℕ → ℝ)
    (hu : Summable u) (hv : Summable v)
    (hb : ∀ i x, x ∈ closedBall c r → ‖f i x‖ ≤ u i)
    (hdb : ∀ i x, x ∈ closedBall c r → ‖fderiv ℝ (f i) x‖ ≤ v i)
    (x : E) (hx : x ∈ closedBall c r) :
    HasFDerivWithinAt (fun y => ∑' i, f i y)
      (∑' i, fderiv ℝ (f i) x) (closedBall c r) x := by
  have hc : ContinuousOn (fun y => ∑' i, f i y) (closedBall c r) :=
    continuousOn_tsum (fun i => (hf i).continuous.continuousOn) hu hb
  have hdc : ContinuousOn (fun y => ∑' i, fderiv ℝ (f i) y) (closedBall c r) :=
    continuousOn_tsum (fun i => ((hf i).continuous_fderiv one_ne_zero).continuousOn) hv hdb
  have hinside (y : E) (hy : y ∈ ball c r) :
      HasFDerivAt (fun z => ∑' i, f i z) (∑' i, fderiv ℝ (f i) y) y := by
    exact hasFDerivAt_tsum_of_isPreconnected hv isOpen_ball
      (convex_ball c r).isPreconnected
      (fun i z _ => (hf i).differentiable_one.differentiableAt.hasFDerivAt)
      (fun i z hz => hdb i z (ball_subset_closedBall hz))
      (mem_ball_self hr)
      (Summable.of_norm_bounded hu (fun i => hb i c (mem_closedBall_self hr.le))) hy
  have hlim : Tendsto (fun y => fderiv ℝ (fun z => ∑' i, f i z) y)
      (𝓝[ball c r] x) (𝓝 (∑' i, fderiv ℝ (f i) x)) := by
    have he : (fun y => ∑' i, fderiv ℝ (f i) y) =ᶠ[𝓝[ball c r] x]
        (fun y => fderiv ℝ (fun z => ∑' i, f i z) y) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hinside y hy).fderiv.symm
    exact ((hdc x hx).mono ball_subset_closedBall).congr' he
  have hext := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hinside y hy).differentiableAt.differentiableWithinAt)
    (convex_ball c r) isOpen_ball
    (fun y hy => (hc y (by simpa only [closure_ball c hr.ne'] using hy)).mono
      ball_subset_closedBall) hlim
  simpa only [closure_ball c hr.ne'] using hext

/-- A globally specified derivative on a set gives the next order of within-set
regularity without assuming that the set is open. -/
theorem contDiffOn_succ_of_hasFDerivWithinAt {m : ℕ} {s : Set E}
    {f : E → F} {g : E → E →L[ℝ] F}
    (hg : ContDiffOn ℝ m g s) (hf : ∀ x ∈ s, HasFDerivWithinAt f (g x) s x) :
    ContDiffOn ℝ (m + 1) f s := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (by simp : (m : ℕ∞ω) ≠ ∞)).mpr
  intro x hx
  refine ⟨s, ?_, ?_, g, hf, hg⟩
  · simpa only [insert_eq_of_mem hx] using (self_mem_nhdsWithin : s ∈ 𝓝[s] x)
  · simp

/-- The literal sum is `C²` on the whole closed ball, including its boundary.
All three assumptions are actual summable uniform bounds on its genuine jets. -/
theorem contDiffOn_tsum_two_closedBall
    (f : ℕ → E → F) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (c : E) {r : ℝ} (hr : 0 < r) (b : Fin 3 → ℕ → ℝ)
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ (j : Fin 3) i x, x ∈ closedBall c r →
      ‖iteratedFDeriv ℝ j.val (f i) x‖ ≤ b j i) :
    ContDiffOn ℝ 2 (fun x => ∑' i, f i x) (closedBall c r) := by
  have hb0 (i : ℕ) (x : E) (hx : x ∈ closedBall c r) : ‖f i x‖ ≤ b 0 i := by
    simpa only [Fin.val_zero, norm_iteratedFDeriv_zero] using hbound 0 i x hx
  have hb1 (i : ℕ) (x : E) (hx : x ∈ closedBall c r) :
      ‖fderiv ℝ (f i) x‖ ≤ b 1 i := by
    simpa only [Fin.val_one, norm_iteratedFDeriv_one] using hbound 1 i x hx
  have hb2 (i : ℕ) (x : E) (hx : x ∈ closedBall c r) :
      ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ b 2 i := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hbound 2 i x hx
  have hfd (i : ℕ) : ContDiff ℝ 1 (fderiv ℝ (f i)) :=
    (hf i).fderiv_right (by norm_num)
  have hd0 := hasFDerivWithinAt_tsum_closedBall f (fun i => (hf i).of_le (by norm_num))
    c hr (b 0) (b 1) (hb 0) (hb 1) hb0 hb1
  have hd1 := hasFDerivWithinAt_tsum_closedBall (fun i => fderiv ℝ (f i)) hfd
    c hr (b 1) (b 2) (hb 1) (hb 2) hb1 hb2
  have hc2 : ContinuousOn (fun x => ∑' i, fderiv ℝ (fderiv ℝ (f i)) x)
      (closedBall c r) := continuousOn_tsum
    (fun i => ((hfd i).continuous_fderiv one_ne_zero).continuousOn) (hb 2) hb2
  have hg : ContDiffOn ℝ 1 (fun x => ∑' i, fderiv ℝ (f i) x) (closedBall c r) :=
    contDiffOn_succ_of_hasFDerivWithinAt (m := 0) (contDiffOn_zero.mpr hc2) hd1
  exact contDiffOn_succ_of_hasFDerivWithinAt (m := 1) hg hd0

open SphericalIntrinsicExtension

/-- Summable actual ambient jets on the closed physical ball prove intrinsic
`C²` regularity of the literal pointwise series on the true round sphere. -/
theorem intrinsicContDiff_tsum_two (n : ℕ)
    (f : ℕ → SphericalModel.Vector (n + 1) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (b : Fin 3 → ℕ → ℝ)
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ (j : Fin 3) i x, ‖x‖ ≤ Real.sqrt (n + 1 : ℕ) →
      ‖iteratedFDeriv ℝ j.val (f i) x‖ ≤ b j i) :
    IntrinsicContDiff n 2 (fun x : RoundSphere n => ∑' i, f i x.val) := by
  let : Fact (Module.finrank ℝ (SphericalModel.Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hc := contDiffOn_tsum_two_closedBall f hf (0 : SphericalModel.Vector (n + 1))
    (r := Real.sqrt (n + 1 : ℕ)) (by positivity) b hb
    (fun j i x hx => hbound j i x (by simpa only [mem_closedBall, dist_zero_right] using hx))
  have hs : ContDiff ℝ 2 (fun x : SphericalModel.Vector (n + 1) =>
      Real.sqrt (n + 1 : ℕ) • x) := by fun_prop
  have hi : ContMDiff (𝓡 n) 𝓘(ℝ, SphericalModel.Vector (n + 1)) 2
      (fun u : SphericalIntrinsicExtension.UnitSphere n =>
        Real.sqrt (n + 1 : ℕ) • (u : SphericalModel.Vector (n + 1))) :=
    hs.contMDiff.comp (contMDiff_coe_sphere (n := n))
  have hmaps (u : SphericalIntrinsicExtension.UnitSphere n) :
      Real.sqrt (n + 1 : ℕ) • (u : SphericalModel.Vector (n + 1)) ∈
        closedBall (0 : SphericalModel.Vector (n + 1)) (Real.sqrt (n + 1 : ℕ)) := by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      mem_sphere_zero_iff_norm.mp u.property, mul_one, le_refl]
  exact hc.contMDiffOn.comp_contMDiff hi hmaps

/-- The canonical radial cutoff representative of the actual sphere series is
globally `C²`; the extension is constructed by the existing intrinsic API. -/
theorem ambientExtension_tsum_contDiff_two (n : ℕ)
    (f : ℕ → SphericalModel.Vector (n + 1) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (b : Fin 3 → ℕ → ℝ)
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ (j : Fin 3) i x, ‖x‖ ≤ Real.sqrt (n + 1 : ℕ) →
      ‖iteratedFDeriv ℝ j.val (f i) x‖ ≤ b j i) :
    ContDiff ℝ 2 (ambientExtension n (fun x : RoundSphere n => ∑' i, f i x.val)) :=
  ambientExtension_contDiff n 2 _ (intrinsicContDiff_tsum_two n f hf b hb hbound)

end
end SlowEquilibration.SphericalSeriesRegularity
