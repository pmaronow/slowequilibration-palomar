-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralPlateauNorm

@[expose] public section

/-! # The stronger stationary plateau theorem for every finite mixture

All five source conclusions use one probability-tending-to-one disorder
event. The eigenvalue, Gibbs-typical total variation and stationary mutual
information conclusions also retain their exponential probability event.
The actual planted weighted norm limit and all-finite likelihood transfer
are proved internally; no stochastic or thermodynamic conclusion is assumed.
-/
namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalWeightedReplicaPlateau
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact source thm:main-plateau for every canonical finite mixture,
including quadratic and odd terms, with b strictly below qStar. -/
theorem general_main_plateau (μ : FiniteMixture) {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi)
    (hb : b∈Ioo (0:ℝ) (Thresholds.qStar μ.xi β)) :
    ∃ κ γ a c C : ℝ,0<κ ∧ 0<γ ∧ 0<a ∧ 0<c ∧ 0<C ∧
      (∀ᶠ N : ℕ in atTop,∃ Ω₀ : Set (Disorder N μ.maxDegree),MeasurableSet Ω₀ ∧
        (disorderLaw N μ.maxDegree).real Ω₀ᶜ≤C*Real.exp (-a*N) ∧
        ∀ D∈Ω₀,∀ hN : 2≤N,PersistentMemoryConclusions hN μ β D κ γ a c C) ∧
      (∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,∃ Ω : Set (Disorder N μ.maxDegree),
        MeasurableSet Ω ∧ (disorderLaw N μ.maxDegree).real Ωᶜ<η ∧
        ∀ D∈Ω,∀ hN : 2≤N,MemoryConclusions hN μ β D b κ γ a c C) := by
  apply general_main_plateau_of_planted_norm_error μ hβd hβs hb
  intro q₁ q₂ δ hc hδ
  exact general_sourceNormError_planted_tendsto μ hβd hβs hc hδ.le

end
end SlowEquilibration.SphericalMemoryAssembly
