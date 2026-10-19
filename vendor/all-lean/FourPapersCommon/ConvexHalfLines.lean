module
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Gluing the two half-line convexity statements requires agreement of the
actual derivatives at the common endpoint. Mere continuity is insufficient. -/
noncomputable section
open Set
namespace FourPapersCommon

theorem convexOn_univ_of_halfLines {f : ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hleft : ConvexOn ℝ (Iic 0) f) (hright : ConvexOn ℝ (Ici 0) f) :
    ConvexOn ℝ univ f := by
  have hl := hleft.monotoneOn_deriv (fun x _ => hf x)
  have hr := hright.monotoneOn_deriv (fun x _ => hf x)
  apply Monotone.convexOn_univ_of_deriv hf
  intro x y hxy
  by_cases hy : y≤0
  · exact hl (le_trans hxy hy) hy hxy
  by_cases hx : 0≤x
  · exact hr hx (le_trans hx hxy) hxy
  exact (hl (le_of_not_ge hx) (mem_Iic.mpr (le_refl (0 : ℝ))) (le_of_not_ge hx)).trans
    (hr (mem_Ici.mpr (le_refl (0 : ℝ))) (le_of_not_ge hy) (le_of_not_ge hy))

end FourPapersCommon
