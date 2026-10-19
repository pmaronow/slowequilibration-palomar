-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Basic

/-! Compact-parameter uniformity derived from convergence along every
convergent parameter sequence and every diverging dimension sequence. -/
@[expose] public section
namespace SlowEquilibration.CompactUniformSequence
noncomputable section
open Function Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Sequential compactness upgrades the actual varying-parameter limits
to a uniform eventual bound; no uniform estimate is assumed. -/
theorem uniform_eventually_le_of_varying_limit {X : Type*} [MetricSpace X]
    {S : Set X} (hS : IsCompact S) (E : ℕ → X → ℝ)
    (hvary : ∀ φ : ℕ → ℕ,Tendsto φ atTop atTop → ∀ p : ℕ → X,∀ x ∈ S,
      Tendsto p atTop (𝓝 x) → Tendsto (fun j=>E (φ j) (p j)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,∀ x ∈ S,E n x ≤ ε := by
  by_contra hnot
  have hf : ∀ N : ℕ,∃ n : ℕ,N ≤ n ∧ ∃ x ∈ S,ε < E n x := by
    intro N
    by_contra hn
    push Not at hn
    apply hnot
    filter_upwards [eventually_ge_atTop N] with n hnN
    exact hn n hnN
  choose φ hφ p hp hbad using hf
  have hφt : Tendsto φ atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hφ j)
  obtain ⟨x,hx,ψ,hψ,ht⟩:=hS.isSeqCompact hp
  have he:=hvary (φ ∘ ψ) (hφt.comp hψ.tendsto_atTop) (p ∘ ψ) x hx ht
  obtain ⟨j,hj⟩:= (he.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad (ψ j)).le) hj

end
end SlowEquilibration.CompactUniformSequence
