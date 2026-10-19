-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSubcriticalOverlapMoment

/-! Dimension-uniform weighted tails for the actual uniform spherical law.
The bound follows from the proved subcritical overlap moment, so neither an
overlap density formula nor a concentration hypothesis is required. -/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalBarycenter SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma weighted_square_tail_indicator_le {a b n t r : ℝ}
    (hn : 0 ≤ n) (ht : 0 ≤ t) (hab : a ≤ b) :
    ({z : ℝ | t < |z|}.indicator (fun z => Real.exp (a*n*z^2)) r) ≤
      Real.exp (-(b-a)*n*t^2)*Real.exp (b*n*r^2) := by
  by_cases hr : t < |r|
  · rw [Set.indicator_of_mem (show r ∈ {z : ℝ | t < |z|} from hr), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs : t^2 ≤ r^2 := by nlinarith [sq_abs r]
    have hmul := mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) hn) (sub_nonneg.mpr hs)
    nlinarith
  · rw [Set.indicator_of_notMem (show r ∉ {z : ℝ | t < |z|} from hr)]
    positivity

/-- The literal overlap-annulus cost is exponentially small beyond any
nonnegative cutoff, with constants chosen before the ambient dimension,
the spherical center, and the cutoff. The exponent is the spare quadratic
coefficient `b-a` in the genuine subcritical exponential moment. -/
theorem sphere_weighted_overlap_tail_eventually_le {a b : ℝ}
    (hb : 0 ≤ b) (hsub : b < 1/2) (hab : a ≤ b) :
    ∃ C > 0, ∀ᶠ N : ℕ in atTop, ∀ x : Vector N,
      ‖x‖^2 = (N:ℝ) → ∀ t : ℝ, 0 ≤ t →
      (∫ y : Vector N,
        ({z : Vector N | t < |overlap x z|}.indicator
          (fun z => Real.exp (a*(N:ℝ)*(overlap x z)^2)) y) ∂sphereLaw N) ≤
        C*Real.exp (-(b-a)*(N:ℝ)*t^2) := by
  obtain ⟨C,hC,hall⟩ := sphere_overlap_exp_square_eventually_bounded hb hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hall,eventually_ge_atTop 1] with N hmoment hN
  intro x hx t ht
  let A := {z : Vector N | t < |overlap x z|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by unfold overlap; fun_prop)
  have hfa : Continuous (fun z : Vector N => Real.exp (a*(N:ℝ)*(overlap x z)^2)) := by
    unfold overlap
    fun_prop
  have hfb : Continuous (fun z : Vector N => Real.exp (b*(N:ℝ)*(overlap x z)^2)) := by
    unfold overlap
    fun_prop
  have hia := integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN) hfa
  have hib := integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN) hfb
  have hdom : ∀ y : Vector N,
      A.indicator (fun z => Real.exp (a*(N:ℝ)*(overlap x z)^2)) y ≤
        Real.exp (-(b-a)*(N:ℝ)*t^2)*Real.exp (b*(N:ℝ)*(overlap x y)^2) := by
    intro y
    simpa only [A,Set.indicator_apply,Set.mem_setOf_eq] using
      weighted_square_tail_indicator_le (Nat.cast_nonneg N) ht hab (r := overlap x y)
  have hi := integral_mono (hia.indicator hA) (hib.const_mul _) hdom
  rw [integral_const_mul] at hi
  calc
    _ ≤ Real.exp (-(b-a)*(N:ℝ)*t^2)*
        (∫ y : Vector N,Real.exp (b*(N:ℝ)*(overlap x y)^2) ∂sphereLaw N) := hi
    _ ≤ Real.exp (-(b-a)*(N:ℝ)*t^2)*C :=
      mul_le_mul_of_nonneg_left (hmoment x hx) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end
end SlowEquilibration.SphericalModel
