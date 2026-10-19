-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemicircleQuadraticTangent

/-! Global concavity of the literal semicircle potential minus its support
quadratic. The spectral edges are handled by continuity of the true potential. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SemicirclePotential
open Set OAI.CriticalSK SemicircleWholeLine
set_option maxHeartbeats 300000

def modifiedPotential (t : ℝ) : ℝ := potential t-t^2/4

theorem resolvent_explicit_root {m : ℝ} (hm : 2 < m) :
    resolvent m=(m-Real.sqrt (m^2-4))/2 := by
  rw [resolvent_eq_semicircleResolvent hm]
  unfold semicircleResolvent
  rw [show (m-2)*(4+(m-2))=m^2-4 by ring]
  ring

/-- The actual semicircle potential lies below its support quadratic,
including both exterior regions and every singular shift. -/
theorem potential_le_support_quadratic (t : ℝ) : potential t ≤ t^2/4-1/2 := by
  let g := fun m : ℝ => potential m+(m-Real.sqrt (m^2-4))/2*(t-m)+(t-m)^2/4
  have hbound : ∀ m ∈ Ioi (2 : ℝ),potential t ≤ g m := by
    intro m hm
    have hh := potential_global_quadratic_tangent hm t
    rw [resolvent_explicit_root hm] at hh
    exact hh
  have hg : Continuous g := by
    dsimp [g]
    have hp := potential_continuous
    fun_prop
  have hEdge : potential t ≤ g 2 := by
    apply le_on_closure hbound continuous_const.continuousOn hg.continuousOn
    rw [closure_Ioi]
    exact le_rfl
  dsimp [g] at hEdge
  rw [potential_eq_inside 2 (by norm_num)] at hEdge
  norm_num at hEdge
  nlinarith

theorem modifiedPotential_even (t : ℝ) : modifiedPotential (-t)=modifiedPotential t := by
  unfold modifiedPotential
  rw [potential_even,neg_sq]

theorem modifiedPotential_positive_support {m : ℝ} (hm : 2 < m) (t : ℝ) :
    modifiedPotential t ≤ modifiedPotential m+(resolvent m-m/2)*(t-m) := by
  have hh := potential_global_quadratic_tangent hm t
  unfold modifiedPotential
  nlinarith

theorem modifiedPotential_has_global_support (m : ℝ) :
    ∃ v : ℝ,∀ t : ℝ,modifiedPotential t ≤ modifiedPotential m+v*(t-m) := by
  by_cases hm : 2 < m
  · exact ⟨resolvent m-m/2,modifiedPotential_positive_support hm⟩
  by_cases hm' : m < -2
  · refine ⟨-(resolvent (-m)-(-m)/2),?_⟩
    intro t
    have hh := modifiedPotential_positive_support (m := -m) (by linarith) (-t)
    rw [modifiedPotential_even,modifiedPotential_even] at hh
    nlinarith
  · refine ⟨0,?_⟩
    intro t
    have hinside : |m| ≤ 2 := abs_le.mpr ⟨by linarith,le_of_not_gt hm⟩
    have hh := potential_le_support_quadratic t
    simp only [modifiedPotential,potential_eq_inside m hinside,zero_mul,add_zero]
    linarith

theorem concaveOn_of_global_support (f : ℝ → ℝ)
    (hf : ∀ m : ℝ,∃ v : ℝ,∀ t : ℝ,f t ≤ f m+v*(t-m)) :
    ConcaveOn ℝ univ f := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let z := a*x+b*y
  obtain ⟨v,hv⟩ := hf z
  have hx := mul_le_mul_of_nonneg_left (hv x) ha
  have hy := mul_le_mul_of_nonneg_left (hv y) hb
  have hcancel : a*(v*(x-z))+b*(v*(y-z))=0 := by
    calc
      _=v*(a*x+b*y-(a+b)*z) := by ring
      _=0 := by rw [hab]; dsimp [z]; ring
  have hweighted : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  change a*f x+b*f y ≤ f z
  nlinarith

/-- The source whole-line modified semicircle potential is genuinely
concave, with no differentiability postulate at either spectral edge. -/
theorem modifiedPotential_concave : ConcaveOn ℝ univ modifiedPotential :=
  concaveOn_of_global_support modifiedPotential modifiedPotential_has_global_support

end SlowEquilibration.SemicirclePotential
