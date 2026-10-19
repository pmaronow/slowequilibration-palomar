-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinKernels

/-! Ordinary spin-law transport and equality for actual normalized
Gaussian Gibbs densities. These apply to nonatomic and singular laws. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianSpinInterpolation

open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V W H H' : Type*} [MeasurableSpace V] [MeasurableSpace W]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

/-- Actual field equality almost everywhere determines the normalized
Gibbs law, even if the fields use different coefficient spaces. -/
theorem gibbsMeasure_congr_field (ν : Measure V)
    (L : V → H →L[ℝ] ℝ) (w : H) (M : V → H' →L[ℝ] ℝ) (z : H')
    (heq : ∀ᵐ x ∂ν,L x w=M x z) : gibbsMeasure ν L w=gibbsMeasure ν M z := by
  have hm : moment ν (fun _ => 1) L w=moment ν (fun _ => 1) M z := by
    unfold moment
    apply integral_congr_ae
    exact heq.mono fun x hx => by simp only [weight,hx]
  unfold gibbsMeasure
  rw [hm]
  apply withDensity_congr_ae
  exact heq.mono fun x hx => by simp only [hx]

/-- The genuine partition integral commutes with ordinary measurable
pushforward of the underlying spin law. -/
theorem moment_map_one (ν : Measure V) (s : V → W) (hs : Measurable s)
    (L : W → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    moment (ν.map s) (fun _ => 1) L w=moment ν (fun _ => 1) (fun x => L (s x)) w := by
  have hf : Measurable (fun x => Real.exp (L x w)) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp
  unfold moment
  simp only [weight,one_mul]
  exact integral_map hs.aemeasurable hf.aestronglyMeasurable

/-- Exact transport of the ordinary product-normalized Gibbs density. -/
theorem gibbsMeasure_map (ν : Measure V) (s : V → W) (hs : Measurable s)
    (L : W → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    (gibbsMeasure ν (fun x => L (s x)) w).map s=gibbsMeasure (ν.map s) L w := by
  have hm := moment_map_one ν s hs L hL w
  have hd : Measurable (fun x => ENNReal.ofReal
      (Real.exp (L x w)/moment ν (fun _ => 1) (fun x => L (s x)) w)) :=
    (((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp.div_const _).ennreal_ofReal
  ext A hA
  rw [gibbsMeasure,gibbsMeasure,hm,Measure.map_apply hs hA,
    withDensity_apply _ (hs hA),withDensity_apply _ hA,setLIntegral_map hA hd hs]

/-- Actual equality of evaluated fields suffices for transport; neither
operator injectivity nor a replacement law is assumed. -/
theorem gibbsMeasure_map_of_field_eq (ν : Measure V) (s : V → W) (hs : Measurable s)
    (L : V → H →L[ℝ] ℝ) (w : H)
    (M : W → H' →L[ℝ] ℝ) (hM : Measurable M) (z : H')
    (heq : ∀ᵐ x ∂ν,L x w=M (s x) z) :
    (gibbsMeasure ν L w).map s=gibbsMeasure (ν.map s) M z := by
  rw [gibbsMeasure_congr_field ν L w (fun x => M (s x)) z heq]
  exact gibbsMeasure_map ν s hs M hM z

end SlowEquilibration.GaussianSpinInterpolation
