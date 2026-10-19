module
public import FourPapersCommon.MixedCoupledOuterExpectation
public import Targets.TalagrandProposition25

@[expose] public section

/-! Actual mixed Gaussian constrained-pressure deficits imply exponentially
small overlap-event probabilities. Only the deficit itself is a hypothesis;
Gaussian concentration and the replica-coordinate identity are proved.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n k : ℕ} {ξ : AdmissibleEvenMixture}
set_option maxHeartbeats 800000

theorem mixed_talagrand_proposition_2_5_explicit (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : constrainedPhi n s (mixedBeta ξ) h sk.U d t u ≤ 2 * guerraPhi n s (mixedBeta ξ) h sk.U t - ε) :
    guerraReplicaMeasure n s (mixedBeta ξ) h sk.U t d (overlapEvent n u) ≤
      Real.exp (-(s.m 1 * ε / 4) * n) +
        Real.exp (-(ε ^ 2 / (128 * (1 + |(mixedBeta ξ)|) ^ 2)) * n) := by
  rw [← mixed_gaussianCoupledEvent_mean_eq sk s h hs ht u hu d hd]
  apply mixedGaussianCoupledEvent_small sk s h hn hs ⟨ht.1.le, ht.2.le⟩ u hu d hε
  rw [mixed_gaussianCoupledGap_mean_eq sk s h hn ⟨ht.1.le, ht.2.le⟩ u hu d hd]
  nlinarith [mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **Lemma 2.6**, now in the original abstract disorder and outer-average formulation.
All means are integrable, and the constant is independent of the system size and time. -/
theorem mixed_talagrand_lemma_2_6 (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : (∫ ω, coupledCascade n s (mixedBeta ξ) d (constrainedBase n (sk.U ω) h t u) (k + 2) 0 0 ∂ℙ) ≤
      (∫ ω, coupledCascade n s (mixedBeta ξ) d (coupledBase n (sk.U ω) h t) (k + 2) 0 0 ∂ℙ) - ε * n) :
    (∫ ω, coupledObservable n s (mixedBeta ξ) (sk.U ω) h t d (overlapEvent n u) (k + 2) 0 0 ∂ℙ) ≤
      talagrandEventConstant s (mixedBeta ξ) ε * Real.exp (-(n : ℝ) / talagrandEventConstant s (mixedBeta ξ) ε) := by
  rw [← mixed_integral_gaussianCoupledEvent_eq sk s h hs ht u hu d hd]
  apply le_trans (mixedGaussianCoupledEvent_small sk s h hn hs ht u hu d hε ?_)
    (talagrandEventConstant_bound s (mixedBeta ξ) hs hε n)
  rw [mixed_integral_gaussianCoupledGap_eq sk s h hn ht u hu d hd]
  unfold coupledGap
  rw [integral_sub (mixed_integrable_constrainedCascade_top sk s h hn ht u hu d hd)
    (mixed_integrable_coupledCascade_top sk s h ht d)]
  linarith

/-- **Proposition 2.5, (2.30)--(2.31)** for the exact-covariance SK model on `0<t<1`.
This time domain is sufficient for the existing endpoint-safe Theorem 2.2 deduction.
The constant is explicitly independent of the system size and interpolation time. -/
theorem mixed_talagrand_proposition_2_5 (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : constrainedPhi n s (mixedBeta ξ) h sk.U d t u ≤ 2 * guerraPhi n s (mixedBeta ξ) h sk.U t - ε) :
    guerraReplicaMeasure n s (mixedBeta ξ) h sk.U t d (overlapEvent n u) ≤
      talagrandEventConstant s (mixedBeta ξ) ε * Real.exp (-(n : ℝ) / talagrandEventConstant s (mixedBeta ξ) ε) :=
  (mixed_talagrand_proposition_2_5_explicit sk s h hn hs ht u hu d hd hε hgap).trans
    (talagrandEventConstant_bound s (mixedBeta ξ) hs hε n)


end FourPapersCommon
