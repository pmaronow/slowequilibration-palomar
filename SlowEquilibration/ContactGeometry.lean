-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

/-!
# Contact geometry for a strictly convex curvature comparator

The analytic part of `prop:th-convex` is a theorem about actual differentiable
functions. A nonnegative twice-differentiable potential has horizontal contacts;
Rolle's theorem produces zeros of its ordinary second derivative between them.
A strictly convex comparator cannot have three zeros. No contact-count or
nondegeneracy conclusion is included among the hypotheses.
-/

namespace SlowEquilibration.ContactGeometry

open Set Filter
open scoped Topology

/-- A strictly convex function cannot have three ordered zeros in its domain. -/
theorem strictConvex_no_three_zeros {D : ℝ → ℝ} {s : Set ℝ}
    (hD : StrictConvexOn ℝ s D) {x y z : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z)
    (hDx : D x = 0) (hDy : D y = 0) (hDz : D z = 0) : False := by
  have hy : y ∈ openSegment ℝ x z := by
    rw [openSegment_eq_Ioo (hxy.trans hyz)]
    exact ⟨hxy, hyz⟩
  have hlt := hD.lt_on_openSegment hx hz (hxy.trans hyz).ne hy
  rw [hDx, hDy, hDz] at hlt
  norm_num at hlt

private theorem no_third_zero_of_ordered_zeros {D : ℝ → ℝ} {s : Set ℝ}
    (hD : StrictConvexOn ℝ s D) {x y z : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hxy : x < y)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hDx : D x = 0) (hDy : D y = 0) (hDz : D z = 0) : False := by
  rcases lt_trichotomy z x with hzx' | hzx' | hxz
  · exact strictConvex_no_three_zeros hD hz hy hzx' hxy hDz hDx hDy
  · exact hzx hzx'
  · rcases lt_trichotomy z y with hzy' | hzy' | hyz
    · exact strictConvex_no_three_zeros hD hx hy hxz hzy' hDx hDz hDy
    · exact hzy hzy'
    · exact strictConvex_no_three_zeros hD hx hz hxy hyz hDx hDy hDz

/-- The zero set of a strictly convex real function has extended cardinality
at most two, derived directly from strict convexity. -/
theorem strictConvex_zeroSet_encard_le_two {D : ℝ → ℝ} {s : Set ℝ}
    (hD : StrictConvexOn ℝ s D) : {r | r ∈ s ∧ D r = 0}.encard ≤ 2 := by
  let Z : Set ℝ := {r | r ∈ s ∧ D r = 0}
  change Z.encard ≤ 2
  by_cases hsmall : Z.encard ≤ 1
  · exact hsmall.trans (by norm_num)
  · have hlarge : 1 < Z.encard := lt_of_not_ge hsmall
    obtain ⟨x, y, hx, hy, hxy⟩ := Set.one_lt_encard_iff.mp hlarge
    have hsub : Z ⊆ {x, y} := by
      intro z hz
      by_cases hzx : z = x
      · simp [hzx]
      by_cases hzy : z = y
      · simp [hzy]
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · exact False.elim (no_third_zero_of_ordered_zeros hD hx.1 hy.1 hz.1 hlt
          hzx hzy hx.2 hy.2 hz.2)
      · exact False.elim (no_third_zero_of_ordered_zeros hD hy.1 hx.1 hz.1 hgt
          hzy hzx hy.2 hx.2 hz.2)
    exact (Set.encard_mono hsub).trans_eq (Set.encard_pair hxy)

/-- A continuous function has nonnegative second derivative at a local
minimum. Negative curvature would give a local maximum by the second derivative
test; the resulting locally constant function has zero second derivative. -/
theorem deriv2_nonneg_of_isLocalMin {V : ℝ → ℝ} {q : ℝ}
    (hmin : IsLocalMin V q) (hcont : ContinuousAt V q) :
    0 ≤ deriv (deriv V) q := by
  by_contra hnot
  have hneg : deriv (deriv V) q < 0 := lt_of_not_ge hnot
  have hmax : IsLocalMax V q :=
    isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hcont
  have heq : V =ᶠ[𝓝 q] (fun _ => V q) := by
    filter_upwards [hmin, hmax] with x hxmin hxmax
    exact le_antisymm hxmax hxmin
  have hderiv2 := heq.deriv.deriv_eq
  simp at hderiv2
  exact hneg.ne hderiv2

/-- Every interior zero of a nonnegative potential is an actual local minimum. -/
theorem contact_isLocalMin {V : ℝ → ℝ}
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r) {q : ℝ}
    (hq : q ∈ Ioo 0 1) (hVq : V q = 0) : IsLocalMin V q := by
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
  rw [hVq]
  exact hnonneg r ⟨hr.1.le, hr.2⟩

/-- Consequently every positive contact has vanishing ordinary first derivative. -/
theorem contact_deriv_zero {V : ℝ → ℝ}
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r) {q : ℝ}
    (hq : q ∈ Ioo 0 1) (hVq : V q = 0) : deriv V q = 0 :=
  (contact_isLocalMin hnonneg hq hVq).deriv_eq_zero

private theorem continuousOn_Icc {f : ℝ → ℝ}
    (hf : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ f r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) : ContinuousOn f (Icc a b) := by
  intro r hr
  exact (hf r ⟨ha.trans hr.1, hr.2.trans_lt hb⟩).continuousAt.continuousWithinAt

/-- Two applications of Rolle's theorem give two ordered second-derivative
zeros strictly between horizontal contacts. The first Rolle point supplies the
same intermediate stationary point as the manuscript's extremum argument. -/
theorem two_deriv2_zeros_between {V : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) (hab : a < b)
    (hVa : V a = 0) (hVb : V b = 0)
    (hda : deriv V a = 0) (hdb : deriv V b = 0) :
    ∃ u v, u ∈ Ioo a b ∧ v ∈ Ioo a b ∧ u < v ∧
      deriv (deriv V) u = 0 ∧ deriv (deriv V) v = 0 := by
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hab
    (continuousOn_Icc hV ha hb) (hVa.trans hVb.symm)
  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_zero hc.1
    (continuousOn_Icc hV' ha (hc.2.trans hb)) (hda.trans hdc.symm)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hc.2
    (continuousOn_Icc hV' (ha.trans hc.1.le) hb) (hdc.trans hdb.symm)
  exact ⟨u, v, ⟨hu.1, hu.2.trans hc.2⟩, ⟨hc.1.trans hv.1, hv.2⟩,
    hu.2.trans hv.1, hdu, hdv⟩

/-- Two distinct positive contacts would create three ordered comparator
zeros, contradicting strict convexity. -/
theorem no_ordered_positive_contacts {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {a b : ℝ} (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1)
    (hVa : V a = 0) (hVb : V b = 0) (hab : a < b) : False := by
  have hda := contact_deriv_zero hnonneg ha hVa
  have hdb := contact_deriv_zero hnonneg hb hVb
  obtain ⟨u, v, hu, hv, huv, hdu, hdv⟩ :=
    two_deriv2_zeros_between hV hV' (by norm_num) ha.2 ha.1 hV0 hVa hd0 hda
  obtain ⟨w, hw, hdw⟩ := exists_deriv_eq_zero hab
    (continuousOn_Icc hV' ha.1.le hb.2) (hda.trans hdb.symm)
  have hu01 : u ∈ Ioo 0 1 := ⟨hu.1, hu.2.trans ha.2⟩
  have hv01 : v ∈ Ioo 0 1 := ⟨hv.1, hv.2.trans ha.2⟩
  have hw01 : w ∈ Ioo 0 1 := ⟨ha.1.trans hw.1, hw.2.trans hb.2⟩
  exact strictConvex_no_three_zeros hD hu01 hw01 huv (hv.2.trans hw.1)
    ((hzero u hu01).mp hdu) ((hzero v hv01).mp hdv) ((hzero w hw01).mp hdw)

/-- The nonnegative potential has at most one positive contact. -/
theorem positive_contacts_unique {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {a b : ℝ} (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1)
    (hVa : V a = 0) (hVb : V b = 0) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (no_ordered_positive_contacts hV hV' hnonneg hV0 hd0 hD hzero
      ha hb hVa hVb hab)
  · exact hab
  · exact False.elim (no_ordered_positive_contacts hV hV' hnonneg hV0 hd0 hD hzero
      hb ha hVb hVa hab)

/-- Every positive contact is nondegenerate, with strictly positive actual
second derivative. This is derived from Rolle and strict convexity, rather than
being an input in a contact certificate. -/
theorem positive_contact_deriv2_pos {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {q : ℝ} (hq : q ∈ Ioo 0 1) (hVq : V q = 0) :
    0 < deriv (deriv V) q := by
  have hdq := contact_deriv_zero hnonneg hq hVq
  have hnonneg2 := deriv2_nonneg_of_isLocalMin
    (contact_isLocalMin hnonneg hq hVq) (hV q ⟨hq.1.le, hq.2⟩).continuousAt
  apply lt_of_le_of_ne hnonneg2
  intro hzero2
  have hd2 : deriv (deriv V) q = 0 := hzero2.symm
  obtain ⟨u, v, hu, hv, huv, hdu, hdv⟩ :=
    two_deriv2_zeros_between hV hV' (by norm_num) hq.2 hq.1 hV0 hVq hd0 hdq
  have hu01 : u ∈ Ioo 0 1 := ⟨hu.1, hu.2.trans hq.2⟩
  have hv01 : v ∈ Ioo 0 1 := ⟨hv.1, hv.2.trans hq.2⟩
  exact strictConvex_no_three_zeros hD hu01 hq huv hv.2
    ((hzero u hu01).mp hdu) ((hzero v hv01).mp hdv) ((hzero q hq).mp hd2)

/-- Once a positive contact `q` exists, the entire contact set is contained
in the two-point set `{0,q}`. -/
theorem contacts_subset_zero_and_positive {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {q : ℝ} (hq : q ∈ Ioo 0 1) (hVq : V q = 0) :
    {r | r ∈ Ico 0 1 ∧ V r = 0} ⊆ {0, q} := by
  intro r hr
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1.1 (Ne.symm hr0)
    have heq := positive_contacts_unique hV hV' hnonneg hV0 hd0 hD hzero
      ⟨hrpos, hr.1.2⟩ hq hr.2 hVq
    simp [heq]

/-- With a positive contact present, the full contact set is exactly `{0,q}`. -/
theorem contacts_eq_zero_and_positive {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {q : ℝ} (hq : q ∈ Ioo 0 1) (hVq : V q = 0) :
    {r | r ∈ Ico 0 1 ∧ V r = 0} = {0, q} := by
  apply Set.Subset.antisymm
  · exact contacts_subset_zero_and_positive hV hV' hnonneg hV0 hd0 hD hzero hq hVq
  · intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨le_rfl, by norm_num⟩, hV0⟩
    · exact ⟨⟨hq.1.le, hq.2⟩, hVq⟩

/-- The complete contact set has at most two elements, with no hypothesis
that a positive contact exists. -/
theorem contacts_encard_le_two {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0) :
    {r | r ∈ Ico 0 1 ∧ V r = 0}.encard ≤ 2 := by
  by_cases hexists : ∃ q ∈ Ioo 0 1, V q = 0
  · obtain ⟨q, hq, hVq⟩ := hexists
    rw [contacts_eq_zero_and_positive hV hV' hnonneg hV0 hd0 hD hzero hq hVq,
      Set.encard_pair hq.1.ne]
  · have hsub : {r | r ∈ Ico 0 1 ∧ V r = 0} ⊆ ({0} : Set ℝ) := by
      intro r hr
      by_cases hr0 : r = 0
      · simpa using hr0
      · have hrpos : 0 < r := lt_of_le_of_ne hr.1.1 (Ne.symm hr0)
        exact False.elim (hexists ⟨r, ⟨hrpos, hr.1.2⟩, hr.2⟩)
    exact (Set.encard_mono hsub).trans (by simp)

/-- The potential is strictly positive away from its positive contact and the
origin, as required by the analytic part of a strict two-contact certificate. -/
theorem potential_pos_away_from_positive_contact {V D : ℝ → ℝ}
    (hV : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ V r)
    (hV' : ∀ r ∈ Ico 0 1, DifferentiableAt ℝ (deriv V) r)
    (hnonneg : ∀ r ∈ Ico 0 1, 0 ≤ V r)
    (hV0 : V 0 = 0) (hd0 : deriv V 0 = 0)
    (hD : StrictConvexOn ℝ (Ioo 0 1) D)
    (hzero : ∀ r ∈ Ioo 0 1, deriv (deriv V) r = 0 ↔ D r = 0)
    {q : ℝ} (hq : q ∈ Ioo 0 1) (hVq : V q = 0)
    {r : ℝ} (hr : r ∈ Ioo 0 1) (hrq : r ≠ q) : 0 < V r := by
  apply lt_of_le_of_ne (hnonneg r ⟨hr.1.le, hr.2⟩)
  intro hVr
  exact hrq (positive_contacts_unique hV hV' hnonneg hV0 hd0 hD hzero hr hq hVr.symm hVq)

end SlowEquilibration.ContactGeometry
