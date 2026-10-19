-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SlowEquilibration.DoubleWellPositive

open Set

/-- The calculus argument below the contact in `prop:th-example`.
A twice-differentiable function vanishing together with its first derivative
at both endpoints is strictly positive inside, when its second derivative
has the prescribed positive-negative-positive sign pattern. -/
theorem positive_of_three_curvature_regions
    (f f1 f2 : ℝ → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f1 r) r)
    (hf1 : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 r) r)
    (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hd0 : f1 0 = 0) (hd1 : f1 1 = 0)
    (hpos : ∀ r ∈ Ioo (0:ℝ) a ∪ Ioo b 1, 0 < f2 r)
    (hneg : ∀ r ∈ Ioo a b, f2 r < 0) :
    ∀ r ∈ Ioo (0:ℝ) 1, 0 < f r := by
  have hfc : ContinuousOn f (Icc (0:ℝ) 1) := fun r hr =>
    (hf r hr).continuousAt.continuousWithinAt
  have hdc : ContinuousOn f1 (Icc (0:ℝ) 1) := fun r hr =>
    (hf1 r hr).continuousAt.continuousWithinAt
  have hmonoL : StrictMonoOn f1 (Icc (0:ℝ) a) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hdc.mono (by intro r hr; constructor <;> linarith [hr.1,hr.2]))
    intro r hr
    rw [interior_Icc] at hr
    rw [(hf1 r (by constructor <;> linarith [hr.1,hr.2])).deriv]
    exact hpos r (Or.inl hr)
  have hantiM : StrictAntiOn f1 (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (hdc.mono (by intro r hr; constructor <;> linarith [hr.1,hr.2]))
    intro r hr
    rw [interior_Icc] at hr
    rw [(hf1 r (by constructor <;> linarith [hr.1,hr.2])).deriv]
    exact hneg r hr
  have hmonoR : StrictMonoOn f1 (Icc b (1:ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hdc.mono (by intro r hr; constructor <;> linarith [hr.1,hr.2]))
    intro r hr
    rw [interior_Icc] at hr
    rw [(hf1 r (by constructor <;> linarith [hr.1,hr.2])).deriv]
    exact hpos r (Or.inr hr)
  have hfa : 0 < f1 a := by
    have h := hmonoL (show (0:ℝ) ∈ Icc 0 a by constructor <;> linarith)
      (show a ∈ Icc (0:ℝ) a by constructor <;> linarith) ha
    simpa [hd0] using h
  have hfb : f1 b < 0 := by
    have h := hmonoR (show b ∈ Icc b (1:ℝ) by constructor <;> linarith)
      (show (1:ℝ) ∈ Icc b 1 by constructor <;> linarith) hb
    simpa [hd1] using h
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab.le
    (hdc.mono (by intro r hr; constructor <;> linarith [hr.1,hr.2]))
    (show (0:ℝ) ∈ Icc (f1 b) (f1 a) from ⟨hfb.le,hfa.le⟩)
  have hac : a < c := by
    by_contra h
    have heq : c = a := le_antisymm (le_of_not_gt h) hc.1
    rw [heq] at hc0
    linarith
  have hcb : c < b := by
    by_contra h
    have heq : c = b := le_antisymm hc.2 (le_of_not_gt h)
    rw [heq] at hc0
    linarith
  have hcpos : 0 < c := ha.trans hac
  have hcone : c < 1 := hcb.trans hb
  have hfirst : ∀ r ∈ Ioo (0:ℝ) c, 0 < f1 r := by
    intro r hr
    by_cases hra : r ≤ a
    · have h := hmonoL (show (0:ℝ) ∈ Icc 0 a by constructor <;> linarith)
        (show r ∈ Icc (0:ℝ) a from ⟨hr.1.le,hra⟩) hr.1
      simpa [hd0] using h
    · have h := hantiM (show r ∈ Icc a b by constructor <;> linarith [hr.1,hr.2])
        hc hr.2
      simpa [hc0] using h
  have hlast : ∀ r ∈ Ioo c (1:ℝ), f1 r < 0 := by
    intro r hr
    by_cases hbr : b ≤ r
    · have h := hmonoR (show r ∈ Icc b (1:ℝ) from ⟨hbr,hr.2.le⟩)
        (show (1:ℝ) ∈ Icc b 1 by constructor <;> linarith) hr.2
      simpa [hd1] using h
    · have h := hantiM hc
        (show r ∈ Icc a b by constructor <;> linarith [hr.1,hr.2]) hr.1
      simpa [hc0] using h
  have hfmono : StrictMonoOn f (Icc (0:ℝ) c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hfc.mono (by intro r hr; constructor <;> linarith [hr.1,hr.2]))
    intro r hr
    rw [interior_Icc] at hr
    rw [(hf r (by constructor <;> linarith [hr.1,hr.2])).deriv]
    exact hfirst r hr
  have hfanti : StrictAntiOn f (Icc c (1:ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (hfc.mono (by intro r hr; constructor <;> linarith [hr.1,hr.2]))
    intro r hr
    rw [interior_Icc] at hr
    rw [(hf r (by constructor <;> linarith [hr.1,hr.2])).deriv]
    exact hlast r hr
  intro r hr
  by_cases hrc : r ≤ c
  · have h := hfmono (show (0:ℝ) ∈ Icc 0 c by constructor <;> linarith)
      (show r ∈ Icc (0:ℝ) c from ⟨hr.1.le,hrc⟩) hr.1
    simpa [h0] using h
  · have h := hfanti (show r ∈ Icc c (1:ℝ) by constructor <;> linarith [hr.2])
      (show (1:ℝ) ∈ Icc c 1 by constructor <;> linarith) hr.2
    simpa [h1] using h

end SlowEquilibration.DoubleWellPositive
