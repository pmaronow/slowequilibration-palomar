module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

/-! Stationarity from a positive interior derivative weight.

The weight may vanish at the endpoint itself. This is needed for physical
mixed covariances with ξ″(0)=0, where dividing by the endpoint curvature would
be invalid.
-/
noncomputable section
open Set Filter Topology
namespace FourPapersCommon

theorem endpointQ_le_of_weighted_minimum {F Q w : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b))
    (hQ : ContinuousWithinAt Q (Icc a b) a)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (w x * (x - Q x)) x)
    (hw : ∀ x ∈ Ioo a b, 0 < w x)
    (hmin : ∀ x ∈ Icc a b, F a ≤ F x) : Q a ≤ a := by
  by_contra hn
  have hpos : 0 < Q a - a := sub_pos.mpr (lt_of_not_ge hn)
  have hcts : ContinuousWithinAt (fun x => Q x - x) (Icc a b) a :=
    hQ.sub continuous_id.continuousWithinAt
  have hmem : {x | 0 < Q x - x} ∈ 𝓝[Icc a b] a :=
    hcts.tendsto.eventually (Ioi_mem_nhds hpos)
  rw [nhdsWithin_Icc_eq_nhdsGE hab] at hmem
  obtain ⟨c, hac, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hmem
  let d := min c b
  have had : a < d := lt_min hac hab
  have hdsub : Icc a d ⊆ Icc a b := Icc_subset_Icc le_rfl (min_le_right _ _)
  have hanti : StrictAntiOn F (Icc a d) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hF.mono hdsub)
    rw [interior_Icc]
    intro x hx
    have hx0 : x ∈ Ioo a b := ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
    rw [(hd x hx0).deriv]
    apply mul_neg_of_pos_of_neg (hw x hx0)
    have hh := hsub (show x ∈ Icc a c from ⟨hx.1.le, hx.2.le.trans (min_le_left _ _)⟩)
    change 0 < Q x - x at hh
    linarith
  have hh := hanti (show a ∈ Icc a d from ⟨le_rfl, had.le⟩)
    (show d ∈ Icc a d from ⟨had.le, le_rfl⟩) had
  exact (not_lt_of_ge (hmin d (hdsub ⟨had.le, le_rfl⟩))) hh

end FourPapersCommon
