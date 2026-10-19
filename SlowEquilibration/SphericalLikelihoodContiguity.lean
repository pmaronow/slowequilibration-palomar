-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLikelihoodTransfer

@[expose] public section

/-! # Actual planted-to-Gibbs-reference convergence transfer

The lower-tail tightness required from the normalized partition function
is stated explicitly. The finite likelihood identity proves convergence
transfer without an exponential rate or a pressure assumption.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact lower-tail property supplied by the positive HMP partition
limit in the manuscript. This definition asserts no such limit. -/
def LikelihoodLowerTailTight (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, ∀ᶠ N : ℕ in atTop,
    (disorderLaw N μ.maxDegree).real
      {D | likelihood (mixtureCoefficients μ) β D < Real.exp (-τ)} ≤ ε

/-- Convergence of literal planted event probabilities transfers to the
literal Gibbs-reference law if the likelihood stays away from zero in
probability. In particular this step introduces no exponential rate. -/
theorem gibbsReference_event_tendsto_of_planted
    (μ : FiniteMixture) (β : ℝ)
    (E : (N : ℕ) → Set (Disorder N μ.maxDegree × Vector N))
    (hE : ∀ N, MeasurableSet (E N))
    (hTight : LikelihoodLowerTailTight μ β)
    (hPlanted : Tendsto (fun N => (plantedLaw (mixtureCoefficients μ) β).real (E N))
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun N => (gibbsReferenceLaw (mixtureCoefficients μ) β).real (E N))
      atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall fun N => ha.trans_le measureReal_nonneg
  · intro ε hε
    obtain ⟨τ,hτ⟩ := hTight (ε/2) (half_pos hε)
    have hp := hPlanted.eventually (gt_mem_nhds
      (show 0 < (ε/2)/Real.exp τ by positivity))
    filter_upwards [hτ,hp,eventually_ge_atTop 1] with N hτ hp hN
    have hSplit := gibbsReference_event_le_likelihood_split hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β τ (hE N)
    have hWeight : Real.exp τ*(plantedLaw (mixtureCoefficients μ) β).real (E N) < ε/2 := by
      exact (lt_div_iff₀' (Real.exp_pos τ)).mp hp
    exact hSplit.trans_lt (by linarith)

end
end SlowEquilibration.SphericalModel
