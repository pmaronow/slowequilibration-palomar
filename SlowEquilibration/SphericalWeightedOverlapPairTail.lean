-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedOverlapTail
public import SlowEquilibration.SphericalCentralOverlapPerturbation

/-! Weighted overlap-annulus estimates under two actual independent
uniform sphere points. No rotational intensity or overlap-density premise
is used in the spatial integration. -/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A dimension-uniform actual product-sphere annulus bound. It can be
applied directly to a Kac--Rice integrand bounded by `exp(a N r²)`. -/
theorem sphere_pair_weighted_overlap_tail_eventually_le {a b : ℝ}
    (hb : 0 ≤ b) (hsub : b < 1/2) (hab : a ≤ b) :
    ∃ C > 0, ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 ≤ t →
      (∫ p : Vector N × Vector N,
        ({q : Vector N × Vector N | t < |overlap q.1 q.2|}.indicator
          (fun q => Real.exp (a*(N:ℝ)*(overlap q.1 q.2)^2)) p)
            ∂(sphereLaw N).prod (sphereLaw N)) ≤
        C*Real.exp (-(b-a)*(N:ℝ)*t^2) := by
  obtain ⟨C,hC,hbound⟩ := sphere_weighted_overlap_tail_eventually_le hb hsub hab
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with N hNbound hN
  intro t ht
  let A := {q : Vector N × Vector N | t < |overlap q.1 q.2|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by unfold overlap; fun_prop)
  have hf : Continuous (fun q : Vector N × Vector N =>
      Real.exp (a*(N:ℝ)*(overlap q.1 q.2)^2)) := by unfold overlap; fun_prop
  have hi := ((memLp_spherePair_continuous hN hf 1).integrable le_rfl).indicator hA
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _x : Vector N,C*Real.exp (-(b-a)*(N:ℝ)*t^2) ∂sphereLaw N := by
      apply integral_mono_of_nonneg
        (.of_forall fun _ => integral_nonneg fun _ =>
          Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
        (integrable_const _)
      filter_upwards [sphereLaw_support hN] with x hx
      exact hNbound x hx t ht
    _ = _ := by simp

end
end SlowEquilibration.SphericalModel
