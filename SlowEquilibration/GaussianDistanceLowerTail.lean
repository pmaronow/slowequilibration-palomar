-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConstrainedConcentration
public import SlowEquilibration.GaussianNormConcentration
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-! Dimension-independent lower-tail envelopes from a genuine positive-mass
Gaussian set. The distance, its integrability and concentration are proved
from the actual Euclidean standard Gaussian measure. -/

noncomputable section
namespace SlowEquilibration.GaussianDistanceLowerTail
open MeasureTheory ProbabilityTheory Set Metric
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]
abbrev E := EuclideanSpace ℝ ι
abbrev law := SYK.standardGaussianMeasureOnEuclidean ι

/-- A positive Gaussian mass bounds the true mean distance to a set. -/
theorem mean_distance_le {G : Set (E (ι:=ι))} (_hG : MeasurableSet G)
    {c : ℝ} (hc : 0<c) (hmass : c ≤ (law (ι:=ι)).real G) :
    (∫x,infDist x G ∂law (ι:=ι)) ≤ Real.sqrt (-2*Real.log c) := by
  let D : E (ι:=ι) → ℝ := fun x => infDist x G
  have hLip : LipschitzWith ((1:ℝ).toNNReal) D := by
    simpa only [Real.toNNReal_one] using lipschitz_infDist_pt G
  have hi : Integrable D (law (ι:=ι)) :=
    SphericalModel.euclidean_lipschitz_integrable D 1 (by norm_num) hLip
  let m := ∫x,D x ∂law (ι:=ι)
  have hm0 : 0 ≤ m := integral_nonneg fun _ => infDist_nonneg
  have hnegLip : LipschitzWith ((1:ℝ).toNNReal) (fun x => -D x) := hLip.neg
  have htail := GaussianNormConcentration.centered_lipschitz_upper_tail
    (fun x : E (ι:=ι) => -D x) (show (0:ℝ) ≤ 1 by norm_num) hnegLip hm0
  rw [integral_neg] at htail
  have hsub : G⊆{x : E (ι:=ι) | -(∫y,D y ∂law (ι:=ι))+m ≤ -D x} := by
    intro x hx
    change -(∫y,D y ∂law (ι:=ι))+m ≤ -D x
    rw [show D x=0 from infDist_zero_of_mem hx]
    dsimp [m]
    linarith
  have hbound : c ≤ Real.exp (-m^2/2) := by
    have hh := hmass.trans ((measureReal_mono hsub).trans htail)
    simpa using hh
  have hlog := Real.log_le_log hc hbound
  rw [Real.log_exp] at hlog
  have hsq : m^2 ≤ -2*Real.log c := by linarith
  have hnonneg : 0 ≤ -2*Real.log c := (sq_nonneg m).trans hsq
  have hsqrt := Real.sq_sqrt hnonneg
  nlinarith [Real.sqrt_nonneg (-2*Real.log c)]

/-- True Gaussian enlargement bound, with a constant depending only on the
actual lower mass c and independent of the ambient dimension. -/
theorem distance_tail_le {G : Set (E (ι:=ι))} (hG : MeasurableSet G)
    {c : ℝ} (hc : 0<c) (hmass : c ≤ (law (ι:=ι)).real G)
    {s : ℝ} (hs : 0 ≤ s) :
    (law (ι:=ι)).real {x | Real.sqrt (-2*Real.log c)+s ≤ infDist x G} ≤ 
      Real.exp (-s^2/2) := by
  have hm := mean_distance_le hG hc hmass
  have hLip : LipschitzWith ((1:ℝ).toNNReal) (fun x : E (ι:=ι) => infDist x G) := by
    simpa only [Real.toNNReal_one] using lipschitz_infDist_pt G
  have htail := GaussianNormConcentration.centered_lipschitz_upper_tail
    (fun x : E (ι:=ι) => infDist x G) (show (0:ℝ) ≤ 1 by norm_num) hLip hs
  have hsub : {x : E (ι:=ι) | Real.sqrt (-2*Real.log c)+s ≤ infDist x G}⊆
      {x : E (ι:=ι) | (∫y,infDist y G ∂law (ι:=ι))+s ≤ infDist x G} := by
    intro x hx
    change Real.sqrt (-2*Real.log c)+s ≤ infDist x G at hx
    change (∫y,infDist y G ∂law (ι:=ι))+s ≤ infDist x G
    linarith
  exact (measureReal_mono hsub).trans (by simpa using htail)

/-- An affine lower support at every point of a positive-mass set yields a
literal lower-tail bound. This deterministic support inequality is later
derived from Jensen's inequality for the true truncated spherical Gibbs law. -/
theorem affine_envelope_lower_tail {G : Set (E (ι:=ι))} (hG : MeasurableSet G)
    {c K A s : ℝ} (hc : 0<c) (hK : 0<K)
    (hmass : c ≤ (law (ι:=ι)).real G) (hs : 0 ≤ s)
    (f : E (ι:=ι) → ℝ)
    (hEnvelope : ∀x,∀y∈G,A-K*dist x y ≤ f x) :
    (law (ι:=ι)).real {x | f x ≤ A-K*(Real.sqrt (-2*Real.log c)+s)} ≤ 
      Real.exp (-s^2/2) := by
  have hGpos : 0<(law (ι:=ι)).real G := hc.trans_le hmass
  have hGne : G.Nonempty := by
    by_contra h
    have he : G=∅ := not_nonempty_iff_eq_empty.mp h
    simp [he] at hGpos
  have hbound (x : E (ι:=ι)) : A-K*infDist x G ≤ f x := by
    have hi : (A-f x)/K ≤ infDist x G := (le_infDist hGne).mpr (by
      intro y hy
      apply (div_le_iff₀ hK).mpr
      have hh := hEnvelope x y hy
      linarith)
    have hh := (div_le_iff₀ hK).mp hi
    linarith
  have hsub : {x : E (ι:=ι) | f x ≤ A-K*(Real.sqrt (-2*Real.log c)+s)}⊆
      {x : E (ι:=ι) | Real.sqrt (-2*Real.log c)+s ≤ infDist x G} := by
    intro x hx
    change f x ≤ A-K*(Real.sqrt (-2*Real.log c)+s) at hx
    change Real.sqrt (-2*Real.log c)+s ≤ infDist x G
    have hh := hbound x
    nlinarith
  exact (measureReal_mono hsub).trans (distance_tail_le hG hc hmass hs)

end SlowEquilibration.GaussianDistanceLowerTail
