-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual positive-density upper tails: continuity, strict monotonicity
and unique tail-equals-one centering from a proved finite bracket. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

def tail (f : ℝ → ℝ) (h : ℝ) : ℝ := ∫ x in Ici h,f x

theorem tail_hasDerivAt {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f) (h : ℝ) :
    HasDerivAt (tail f) (-f h) h := by
  have he : tail f=(fun y : ℝ => tail f 0-∫ x in (0 : ℝ)..y,f x) := by
    funext y
    have hh := intervalIntegral.integral_Ici_sub_Ici' (hi.integrableOn (s := Ici 0))
      (hi.integrableOn (s := Ici y))
    change tail f 0-tail f y=∫ x in (0 : ℝ)..y,f x at hh
    linarith
  rw [he]
  have hI := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 h)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [zero_sub,Pi.sub_def] using (hasDerivAt_const h (tail f 0)).sub hI

theorem tail_continuous {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f) :
    Continuous (tail f) := continuous_iff_continuousAt.mpr (fun h => (tail_hasDerivAt hi hc h).continuousAt)

theorem tail_strictAnti {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ h : ℝ,0<f h) : StrictAnti (tail f) :=
  strictAnti_of_hasDerivAt_neg (tail_hasDerivAt hi hc) (fun h => neg_neg_of_pos (hp h))

/-- A finite bracket proves existence of the actual normalized centering;
positivity of the original density proves global uniqueness. -/
theorem exists_unique_normalized_center {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ h : ℝ,0<f h) {l r : ℝ} (hlr : l≤r)
    (hl : 1≤tail f l) (hr : tail f r≤1) : ∃! m : ℝ,tail f m=1 := by
  have hIVT := intermediate_value_Icc' hlr (tail_continuous hi hc).continuousOn
  obtain ⟨m,_hm,he⟩ := hIVT ⟨hr,hl⟩
  refine ⟨m,he,?_⟩
  intro y hy
  exact (tail_strictAnti hi hc hp).injective (hy.trans he.symm)

/-- The same finite bracket locates every normalized center. -/
theorem normalized_center_mem_Icc {f : ℝ → ℝ} (hi : Integrable f) (hc : Continuous f)
    (hp : ∀ h : ℝ,0<f h) {l r m : ℝ}
    (hl : 1≤tail f l) (hr : tail f r≤1) (hm : tail f m=1) : m∈Icc l r := by
  have hs := tail_strictAnti hi hc hp
  constructor
  · by_contra h
    have hh := hs (lt_of_not_ge h)
    rw [hm] at hh
    linarith
  · by_contra h
    have hh := hs (lt_of_not_ge h)
    rw [hm] at hh
    linarith
end SlowEquilibration.ExpectedTailCentering
