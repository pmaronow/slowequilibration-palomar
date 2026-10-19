module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Instances.NNReal.Lemmas

public section
/-! Local fixed-horizon gluing on nonnegative time, including time zero. -/
open Set Filter Topology
open scoped NNReal
namespace SphericalAging.LocalHorizonContinuity
theorem continuous_of_horizon_agreement {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (f : ℝ≥0 × X → E) (g : ℝ≥0 → ℝ≥0 × X → E)
    (hg : ∀ T,0<T → Continuous (g T))
    (he : ∀ T,0<T → ∀ z,z.1≤T → f z=g T z) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let T : ℝ≥0 := z.1+1
  have hlt : z.1<T := by dsimp [T];simp
  have hT : 0<T := lt_of_le_of_lt (show 0≤z.1 from zero_le) hlt
  apply (hg T hT).continuousAt.congr_of_eventuallyEq
  have ht : ∀ᶠ y : ℝ≥0 × X in 𝓝 z,y.1<T :=
    continuous_fst.continuousAt.eventually (eventually_lt_nhds hlt)
  filter_upwards [ht] with y hy
  exact he T hT y hy.le
end SphericalAging.LocalHorizonContinuity
