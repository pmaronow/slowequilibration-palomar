module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.CompactParameterSmoothIntegral
public import SlowEquilibration.SphericalEnergy
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-! # Genuine smooth integration against the actual spherical Gibbs law -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
open Set MeasureTheory Filter Metric
open SphericalModel
open scoped Topology ContDiff

variable {N : ℕ} {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Continuous vector-valued observables are genuinely Gibbs integrable,
using the actual compact support of the actual Gibbs probability law. -/
theorem integrable_gibbs_of_continuous_vector (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {f : Vector N → G} (hf : Continuous f) :
    Integrable f (gibbsLaw N β H) := by
  let := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ u ∂gibbsLaw N β H, u ∈ closedBall (0 : Vector N) (Real.sqrt N) :=
    (sphereLaw_mem_closedBall hN).filter_mono (gibbsLaw_absolutelyContinuous β H).ae_le
  have hi := hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N)) (μ := gibbsLaw N β H)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] using hi

/-- A jointly smooth ambient family integrates to an actual smooth ambient
observable under the actual Gibbs law. The genuine parameter cutoff is one
near its actual sphere support; all domination bounds are proved internally. -/
theorem gibbsIntegral_contDiff (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (F : Vector N → Vector N → G)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun x => ∫ u, F u x ∂gibbsLaw N β H) := by
  let := gibbsLaw_probability hN β hH
  let r : ℝ := (N:ℝ)+1
  have hr : 0 < r := by dsimp [r]; positivity
  let φ : ContDiffBump (0 : Vector N) := ⟨r, r+1, hr, by linarith⟩
  let Fc : Vector N → Vector N → G := fun u x => φ u • F u x
  have hFc : ContDiff ℝ ∞ (Function.uncurry Fc) :=
    (φ.contDiff.comp contDiff_fst).smul hF
  have hc := CompactParameterSmoothIntegral.contDiff_integral
    (gibbsLaw N β H) Fc hFc (closedBall (0 : Vector N) φ.rOut) (isCompact_closedBall _ _) (by
      intro u hu x
      have hdist : φ.rOut ≤ dist u (0 : Vector N) :=
        le_of_lt (lt_of_not_ge (by simpa only [mem_closedBall, dist_comm] using hu))
      have hz := φ.zero_of_le_dist hdist
      dsimp [Fc]
      rw [hz, zero_smul])
  have hφ : ∀ᵐ u ∂gibbsLaw N β H, φ u = 1 := by
    filter_upwards [gibbsLaw_support hN β H] with u hu
    have hnorm : ‖u‖ < r := by dsimp [r]; nlinarith [norm_nonneg u, Nat.cast_nonneg (α := ℝ) N]
    have hball : u ∈ ball (0 : Vector N) φ.rIn := by
      simpa only [mem_ball, dist_zero_right] using hnorm
    exact (φ.eventuallyEq_one_of_mem_ball hball).eq_of_nhds
  have he : (fun x => ∫ u, Fc u x ∂gibbsLaw N β H) =
      (fun x => ∫ u, F u x ∂gibbsLaw N β H) := by
    funext x
    apply integral_congr_ae
    filter_upwards [hφ] with u hu
    dsimp [Fc]
    rw [hu, one_smul]
  rw [he] at hc
  exact hc

/-- The first spatial derivative of a literal Gibbs parameter integral is
its literal integral derivative. Joint smoothness and actual compact Gibbs
support provide the required dominated bounds. -/
theorem gibbsIntegral_hasFDerivAt (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (F : Vector N → Vector N → G)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (x : Vector N) :
    HasFDerivAt (fun y => ∫ u, F u y ∂gibbsLaw N β H)
      (∫ u, fderiv ℝ (F u) x ∂gibbsLaw N β H) x := by
  let := gibbsLaw_probability hN β hH
  let D : Vector N → Vector N → Vector N →L[ℝ] G := fun u y => fderiv ℝ (F u) y
  have hmap : ContDiff ℝ ∞ (fun q : (Vector N × Vector N) × Vector N => (q.1.1,q.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have hD : Continuous (Function.uncurry D) :=
    ((hF.comp hmap).fderiv (n := ∞) contDiff_snd (by simp)).continuous
  have hs : ∀ᵐ u ∂gibbsLaw N β H, u ∈ closedBall (0 : Vector N) (Real.sqrt N) :=
    (sphereLaw_mem_closedBall hN).filter_mono (gibbsLaw_absolutelyContinuous β H).ae_le
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall x 1)).exists_bound_of_continuousOn hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y u => F u y) (F' := fun y u => D u y)
    (s := closedBall x 1) (bound := fun _ => C) (closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun y => (hF.continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable))
    (integrable_gibbs_of_continuous_vector hN β hH (hF.continuous.comp
      (continuous_id.prodMk continuous_const)))
    ((hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (hs.mono (fun u hu y hy => hC (u,y) ⟨hu,hy⟩)) (integrable_const C)
  apply ae_of_all
  intro u y hy
  exact (((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) y).hasFDerivAt

theorem gibbsIntegral_fderiv (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (F : Vector N → Vector N → G)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (x : Vector N) :
    fderiv ℝ (fun y => ∫ u, F u y ∂gibbsLaw N β H) x =
      ∫ u, fderiv ℝ (F u) x ∂gibbsLaw N β H :=
  (gibbsIntegral_hasFDerivAt hN β hH F hF x).fderiv

end
end SlowEquilibration.SphericalForm
