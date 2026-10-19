-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGAveragedPositivity

/-! A fixed finite family of literal power-GG errors uniformly controls
negative-overlap mass. All replica counts, shells, tested powers and
constants precede every Hilbert space, dimension, Gibbs law and disorder
or perturbation ensemble. This is the finite measure-theoretic consumer
of the genuine Gaussian self-averaging GG estimates. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGEnsemble

open MeasureTheory ProbabilityTheory Set
open GaussianGGCutoffs GaussianGGPolynomialTests
open scoped ProbabilityTheory Topology BigOperators

set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Uniform finite positivity estimate for arbitrary ordinary Gibbs
ensembles in a real Hilbert unit ball. No power-GG or indicator-GG
identity is an assumption: the actual tested defects appear explicitly. -/
theorem exists_uniform_finite_power_bound {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ n M K : ℕ, ∃ C : ℝ, 2≤n ∧ 0<M ∧ 0<C ∧
      ∀ (X Ω H : Type*) [MeasurableSpace X] [MeasurableSpace Ω]
      [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H],
      ∀ (π : Measure X) [IsProbabilityMeasure π] (d : Measure Ω) [IsProbabilityMeasure d]
      (G : Kernel (X × Ω) H) [IsMarkovKernel G],
      (∀ᵐ x ∂π, ∀ᵐ ω ∂d, ∀ᵐ z ∂G (x,ω), ‖z‖≤1) →
      (∫x,starMass d (G.sectR x) ε 1 ∂π)≤η+C*finitePowerError π d G ε n M K := by
  have hhalf : 0<ε/2 := by positivity
  have hηhalf : 0<η/2 := by positivity
  obtain ⟨n,γ,C₀,hn,hγ,hC₀,hNumeric⟩ := GaussianGGWeights.exists_finite_exclusion hhalf hηhalf
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  let δ : ℝ := η/(8*C₀*(n:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨M,hMbig⟩ := exists_nat_gt (8*C₀*(n:ℝ)/η)
  have hMpos : 0<(M:ℝ) := lt_trans (by positivity : 0<8*C₀*(n:ℝ)/η) hMbig
  have hM : 0<M := by exact_mod_cast hMpos
  obtain ⟨P,K,Ccoef,hCcoef,happ,hK,hcoef⟩ := exists_bounded_polynomial_family ε M hδ
  have hδsmall : 2*C₀*(n:ℝ)*δ=η/4 := by
    dsimp [δ]
    field_simp [hC₀.ne',hnpos.ne']
    ring
  have hMsmall : 2*C₀*(n:ℝ)/(M:ℝ)≤η/4 := by
    apply (div_le_iff₀ hMpos).mpr
    have hh := (div_lt_iff₀ hη).mp hMbig
    nlinarith
  have hsmall : C₀*((n:ℝ)*(2*δ+2/(M:ℝ)))≤η/2 := by
    have heq : C₀*((n:ℝ)*(2*δ+2/(M:ℝ)))=
        2*C₀*(n:ℝ)*δ+2*C₀*(n:ℝ)/(M:ℝ) := by ring
    rw [heq,hδsmall]
    linarith
  refine ⟨n,M,K,C₀*Ccoef,hn,hM,mul_pos hC₀ hCcoef,?_⟩
  intro X Ω H _ _ _ _ _ _ _ _ π _ d _ G _ hG
  have ht := averaged_pair_mass_le_polynomial_errors π d G hG hε hε1
    n γ C₀ hγ hC₀.le hNumeric M hM P K hK Ccoef hCcoef.le hcoef hδ.le
    (fun j r hr => (happ j r hr).le)
  calc
    _ ≤ η/2+C₀*(Ccoef*finitePowerError π d G ε n M K+(n:ℝ)*(2*δ+2/(M:ℝ))) := ht
    _ = η/2+(C₀*Ccoef)*finitePowerError π d G ε n M K+C₀*((n:ℝ)*(2*δ+2/(M:ℝ))) := by ring
    _ ≤ _ := by linarith

end SlowEquilibration.GaussianGGEnsemble
