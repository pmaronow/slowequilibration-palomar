-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail
public import SlowEquilibration.SphericalLikelihoodContiguity

@[expose] public section

/-! The normalized physical spherical partition stays away from zero in
probability for every strict RS finite mixture, including quadratic and odd
terms. Consequently the true planted-to-Gibbs-reference HMP event transfer
has no remaining tightness or minimum-degree-three premise. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

private theorem eventually_of_eventually_succ (P : ℕ → Prop)
    (h : ∀ᶠn : ℕ in atTop,P (n+1)) : ∀ᶠN : ℕ in atTop,P N := by
  obtain ⟨n,hn⟩ := eventually_atTop.mp h
  apply eventually_atTop.mpr
  refine ⟨n+1,?_⟩
  intro N hN
  have hh := hn (N-1) (by omega)
  simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega)] using hh

/-- Genuine lower-tail tightness of the actual normalized partition function
for all finite covariances in the full strict replica-symmetric region. -/
theorem general_likelihoodLowerTailTight (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    LikelihoodLowerTailTight μ β := by
  obtain ⟨C,K,hC,hK,hTail⟩ := general_logPartition_lower_tail μ hβ hβs
  intro ε hε
  let s := Real.sqrt (2*(|Real.log ε|+1))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsexp : Real.exp (-s^2/2)<ε := by
    have hs2 : s^2=2*(|Real.log ε|+1) := Real.sq_sqrt (by positivity)
    rw [hs2]
    calc
      _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith [neg_abs_le (Real.log ε)])
      _ = ε := Real.exp_log hε
  refine ⟨C+K*s,?_⟩
  apply eventually_of_eventually_succ
  filter_upwards [hTail] with n hn
  have hsub : {J : Disorder (n+1) μ.maxDegree |
      likelihood (mixtureCoefficients μ) β J<Real.exp (-(C+K*s))}⊆
      {J : Disorder (n+1) μ.maxDegree | Real.log (mixturePartition μ β J) ≤
        annealedExponent (n+1) (mixtureCoefficients μ) β-C-K*s} := by
    intro J hJ
    change likelihood (mixtureCoefficients μ) β J<Real.exp (-(C+K*s)) at hJ
    rw [likelihood_lt_exp_iff_logPartition (show 1 ≤ n+1 by omega)] at hJ
    change Real.log (mixturePartition μ β J) ≤ _
    have hh := hJ.le
    change Real.log (partition (n+1) β (field (mixtureCoefficients μ) J)) ≤ _ at hh
    change Real.log (partition (n+1) β (field (mixtureCoefficients μ) J)) ≤
      annealedExponent (n+1) (mixtureCoefficients μ) β-C-K*s
    linarith
  exact ((measureReal_mono hsub).trans (hn s hs)).trans hsexp.le

/-- Full genuine HMP convergence transfer, now with degree-two and arbitrary
odd mixed covariances and no supplied likelihood/tightness property. -/
theorem general_gibbsReference_event_tendsto_of_planted (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi)
    (E : (N : ℕ) → Set (Disorder N μ.maxDegree×Vector N))
    (hE : ∀N,MeasurableSet (E N))
    (hPlanted : Tendsto (fun N => (plantedLaw (mixtureCoefficients μ) β).real (E N)) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun N => (gibbsReferenceLaw (mixtureCoefficients μ) β).real (E N)) atTop (𝓝 (0:ℝ)) :=
  gibbsReference_event_tendsto_of_planted μ β E hE (general_likelihoodLowerTailTight μ hβ hβs) hPlanted

end SlowEquilibration.SphericalModel
