-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagPhysicalDefinitions

@[expose] public section

/-!
# Subag's fixed-parameter replicated-band concentration

This is the fixed-parameter spherical specialization of Proposition 24,
equation (3.1), in Subag, *Free energy landscapes in spherical spin glasses*,
arXiv:1804.10576v6.  It applies to a single-degree pure model of either
parity as well as to mixed models.  The manuscript itself uses this statement
with `N ≥ k+1` to ensure that the replicated band has positive volume.

`Proposition24` is an explicit theorem hypothesis, not an axiom.  The derived
one-sided estimate is the exact interface needed in the manuscript's finite
net argument for energies of ordinary Gibbs replica means.  The argument
also needs the separate expected-band upper bound, pressure lower bound and
Lipschitz/net estimates; Proposition 24 alone does not imply that conclusion.
-/

namespace SlowEquilibration.LiteratureSubagProposition24

noncomputable section
open MeasureTheory Set
open SphericalModel LiteratureSubagPhysicalDefinitions
set_option autoImplicit false

/-- A strict uniform deviation bound on the entire radius-`sqrt(Nq)`
center sphere.  The intermediate `s<t` retains the strict `sup < t` in
the paper, rather than merely requiring separate pointwise `< t` bounds. -/
def uniformDeviationEvent {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ t : ℝ) : Set (Disorder N μ.maxDegree) :=
  {J | ∃ s : ℝ, s < t ∧
    ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
      |replicatedBandPressure k μ β q δ ρ J m -
        expectedReplicatedBandPressure k μ β q δ ρ m| ≤ s}

/-- Proposition 24 (fixed `k`, `δ`, `ρ` before the dimension limit).
This is a theorem argument at the original disorder law and physical
Hamiltonian, not a claim proved in this repository. -/
def Proposition24 (μ : FiniteMixture) (β q : ℝ) : Prop :=
  0 < β ∧ q ∈ Ico (0 : ℝ) 1 ∧
  ∀ t c : ℝ, 0 < t → 0 < c →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ k₀ : ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∀ k : ℕ, k₀ ≤ k →
      ∀ N : ℕ, k + 1 ≤ N →
        MeasurableSet (uniformDeviationEvent (N := N) k μ β q δ ρ t) ∧
          (disorderLaw N μ.maxDegree).real
            (uniformDeviationEvent (N := N) k μ β q δ ρ t) >
              1 - Real.exp (-c * (N : ℝ))

/-- The direct one-sided conclusion used by the pure and mixed
replicated-mean net arguments.  The expected value is at the same center;
rotational invariance may later identify it with one reference center. -/
theorem oneSided_of_uniformDeviation {N k : ℕ} (μ : FiniteMixture)
    (β q δ ρ t : ℝ) {J : Disorder N μ.maxDegree}
    (hJ : J ∈ uniformDeviationEvent k μ β q δ ρ t)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ) * q) :
    replicatedBandPressure k μ β q δ ρ J m <
      expectedReplicatedBandPressure k μ β q δ ρ m + t := by
  obtain ⟨s, hs, hbound⟩ := hJ
  have hd := hbound m hm
  have hle := le_abs_self
    (replicatedBandPressure k μ β q δ ρ J m -
      expectedReplicatedBandPressure k μ β q δ ρ m)
  linarith

/-- Instantiate Proposition 24 without changing its quantifier order and
obtain an explicit high-probability event with the uniform one-sided bound. -/
theorem fixedParameters_uniform_upper (μ : FiniteMixture) (β q : ℝ)
    (h24 : Proposition24 μ β q) {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ k₀ : ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∀ k : ℕ, k₀ ≤ k →
      ∀ N : ℕ, k + 1 ≤ N →
        ∃ Ω : Set (Disorder N μ.maxDegree),
          MeasurableSet Ω ∧
          (disorderLaw N μ.maxDegree).real Ω >
            1 - Real.exp (-c * (N : ℝ)) ∧
          ∀ J ∈ Ω, ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
            replicatedBandPressure k μ β q δ ρ J m <
              expectedReplicatedBandPressure k μ β q δ ρ m + t := by
  obtain ⟨δ₀,hδ₀,ρ₀,hρ₀,k₀,h24⟩ := h24.2.2 t c ht hc
  refine ⟨δ₀,hδ₀,ρ₀,hρ₀,k₀,?_⟩
  intro δ hδ hδ₀' ρ hρ hρ₀' k hk N hN
  exact ⟨uniformDeviationEvent k μ β q δ ρ t,
    (h24 δ hδ hδ₀' ρ hρ hρ₀' k hk N hN).1,
    (h24 δ hδ hδ₀' ρ hρ hρ₀' k hk N hN).2,
    fun J hJ m hm => oneSided_of_uniformDeviation μ β q δ ρ t hJ m hm⟩

end
end SlowEquilibration.LiteratureSubagProposition24
