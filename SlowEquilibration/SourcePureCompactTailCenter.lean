-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedTailCentering
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Tail centering for a density supported on a pure-model mark interval. The
density may jump to zero at the two endpoints, as it does when the radial
mark is cut by the source's open interval `U`. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

/-- Absolute integrability alone makes a moving upper-tail integral
continuous, even when the density jumps at a mark-window endpoint. -/
theorem tail_continuous_of_integrable {f : ℝ → ℝ} (hi : Integrable f) :
    Continuous (tail f) := by
  have he : tail f=(fun y : ℝ => tail f 0-∫ x in (0 : ℝ)..y,f x) := by
    funext y
    have hh := intervalIntegral.integral_Ici_sub_Ici'
      (hi.integrableOn (s := Ici 0)) (hi.integrableOn (s := Ici y))
    change tail f 0-tail f y=∫ x in (0 : ℝ)..y,f x at hh
    linarith
  rw [he]
  exact continuous_const.sub (hi.continuous_primitive 0)

/-- The tail derivative at an interior point only needs continuity of the
density at that point. Global continuity is unnecessary for mark truncation. -/
theorem tail_hasDerivAt_of_continuousAt {f : ℝ → ℝ} (hi : Integrable f)
    {h : ℝ} (hc : ContinuousAt f h) : HasDerivAt (tail f) (-f h) h := by
  have he : tail f=(fun y : ℝ => tail f 0-∫ x in (0 : ℝ)..y,f x) := by
    funext y
    have hh := intervalIntegral.integral_Ici_sub_Ici'
      (hi.integrableOn (s := Ici 0)) (hi.integrableOn (s := Ici y))
    change tail f 0-tail f y=∫ x in (0 : ℝ)..y,f x at hh
    linarith
  rw [he]
  have hI := intervalIntegral.integral_hasDerivAt_right
    (hi.intervalIntegrable (a := 0) (b := h))
    hi.aestronglyMeasurable.stronglyMeasurableAtFilter hc
  simpa only [zero_sub,Pi.sub_def] using (hasDerivAt_const h (tail f 0)).sub hI

/-- On an open interval where an integrable density is positive and
continuous, its true upper tail is strictly decreasing. -/
theorem tail_strictAntiOn_interior {f : ℝ → ℝ} (hi : Integrable f)
    {l r : ℝ} (hc : ContinuousOn f (Ioo l r))
    (hp : ∀ h ∈ Ioo l r, 0 < f h) : StrictAntiOn (tail f) (Ioo l r) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo l r)
    (tail_continuous_of_integrable hi).continuousOn
  intro h hh
  have hh' : h ∈ Ioo l r := interior_subset hh
  have hCont : ContinuousAt f h :=
    (hc h hh').continuousAt (isOpen_Ioo.mem_nhds hh')
  rw [(tail_hasDerivAt_of_continuousAt hi hCont).deriv]
  exact neg_neg_of_pos (hp h hh')

theorem tail_antitone_of_nonneg {f : ℝ → ℝ} (hi : Integrable f)
    (hf : ∀ H : ℝ, 0 ≤ f H) : Antitone (tail f) := by
  intro a b hab
  unfold tail
  exact setIntegral_mono_set (hi.integrableOn (s := Ici a))
    (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall (fun x hx => hab.trans hx))

/-- A strict finite tail bracket gives a unique normalized center even when
the nonnegative density vanishes outside an open mark window. -/
theorem exists_unique_normalized_center_compact_support {f : ℝ → ℝ}
    (hi : Integrable f)
    {l r : ℝ} (hlr : l < r)
    (hc : ContinuousOn f (Ioo l r)) (hp : ∀ H ∈ Ioo l r, 0 < f H)
    (hl : 1 < tail f l) (hr : tail f r < 1) :
    ∃! m : ℝ, m ∈ Ioo l r ∧ tail f m=1 := by
  have hTailCont := tail_continuous_of_integrable hi
  have hIVT := intermediate_value_Icc' hlr.le hTailCont.continuousOn
  obtain ⟨m,hm,he⟩ := hIVT ⟨hr.le,hl.le⟩
  have hMem : m ∈ Ioo l r := by
    constructor
    · rcases hm.1.eq_or_lt with hEq | hLt
      · subst m
        linarith
      · exact hLt
    · rcases hm.2.eq_or_lt with hEq | hLt
      · subst m
        linarith
      · exact hLt
  have hAnti := tail_strictAntiOn_interior hi hc hp
  refine ⟨m,⟨hMem,he⟩,?_⟩
  intro y hy
  have hEq := hAnti.injOn hy.1 hMem (hy.2.trans he.symm)
  exact hEq

/-- With global nonnegativity, the unique interior center is the only root
on the whole real line, including both flat tails outside the mark support. -/
theorem exists_unique_normalized_center_compact_support_global {f : ℝ → ℝ}
    (hi : Integrable f) (hf : ∀ H : ℝ, 0 ≤ f H)
    {l r : ℝ} (hlr : l < r)
    (hc : ContinuousOn f (Ioo l r)) (hp : ∀ H ∈ Ioo l r, 0 < f H)
    (hl : 1 < tail f l) (hr : tail f r < 1) :
    ∃! m : ℝ, tail f m=1 ∧ m ∈ Ioo l r := by
  obtain ⟨m,⟨hm,hEq⟩,hu⟩ :=
    exists_unique_normalized_center_compact_support hi hlr hc hp hl hr
  have hAnti := tail_antitone_of_nonneg hi hf
  refine ⟨m,⟨hEq,hm⟩,?_⟩
  intro y hy
  have hyMem : y ∈ Ioo l r := by
    constructor
    · by_contra hNot
      have hle : y ≤ l := le_of_not_gt hNot
      have hh := hAnti hle
      rw [hy.1] at hh
      linarith
    · by_contra hNot
      have hle : r ≤ y := le_of_not_gt hNot
      have hh := hAnti hle
      rw [hy.1] at hh
      linarith
  exact hu y ⟨hyMem,hy.1⟩

end SlowEquilibration.ExpectedTailCentering
