-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Compact uniformization of decreasing finite-block failure
probabilities. This is the topological heart of source Proposition 9.16:
once overlap-array limit laws are represented by directing kernels,
pointwise companion extraction is promoted to one block count uniformly
over all subsequential laws. Closed failure events yield the required
open strict sublevel sets by Portmanteau. -/

@[expose] public section
namespace SlowEquilibration.PureCaptureCompactFailureUniformization

open Set Filter
open scoped Topology

set_option autoImplicit false

/-- Directed open-cover version of the finite-replica compactness step.
The functions need only have open strict sublevel sets, rather than be
continuous; this accommodates closed failure events via Portmanteau. -/
theorem compact_uniform_sublevel {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : ℕ → X → ℝ)
    (hanti : ∀ {s t : ℕ}, s ≤ t → ∀ x, f t x ≤ f s x)
    (ε : ℝ) (hopen : ∀ T, IsOpen {x | f T x < ε})
    (hpoint : ∀ x ∈ K, ∃ T, f T x < ε) :
    ∃ T, ∀ x ∈ K, f T x < ε := by
  let U (T : ℕ) : Set X := {x | f T x < ε}
  have hcover : K ⊆ ⋃ T, U T := by
    intro x hx
    obtain ⟨T,hT⟩ := hpoint x hx
    exact mem_iUnion.mpr ⟨T,hT⟩
  have hdirected : Directed (· ⊆ ·) U := by
    intro s t
    refine ⟨max s t,?_,?_⟩
    · intro x hx
      exact lt_of_le_of_lt (hanti (le_max_left s t) x) hx
    · intro x hx
      exact lt_of_le_of_lt (hanti (le_max_right s t) x) hx
  obtain ⟨T,hT⟩ := hK.elim_directed_cover U hopen hcover hdirected
  exact ⟨T,fun x hx => hT hx⟩

/-- Pointwise vanishing of an antitone family of upper-semicontinuous
failure probabilities becomes uniform over a compact family of possible
limiting laws. The proof uses no convergence rate or monotonicity in N. -/
theorem compact_uniform_tendsto_zero {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : ℕ → X → ℝ)
    (hanti : ∀ {s t : ℕ}, s ≤ t → ∀ x, f t x ≤ f s x)
    (hopen : ∀ ε : ℝ, 0 < ε → ∀ T, IsOpen {x | f T x < ε})
    (hpoint : ∀ x ∈ K, Tendsto (fun T => f T x) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ x ∈ K, f T x < ε := by
  apply compact_uniform_sublevel K hK f hanti ε (hopen ε hε)
  intro x hx
  have hEventually := (hpoint x hx).eventually (Iio_mem_nhds hε)
  exact hEventually.exists

end SlowEquilibration.PureCaptureCompactFailureUniformization
