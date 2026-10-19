module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedGuerraConvergence
public import FourPapersCommon.MixedConstrainedConcentration
public import Targets.TalagrandOverlapTail

@[expose] public section

/-! Genuine mixed finite-overlap tails from a constrained-pressure estimate.

The estimate itself is an explicit analytic obligation. The Gaussian tail,
finite-union bound, cascade mass normalization, and Grönwall deductions here
are fully proved for the actual mixed covariance and original physical overlaps.
The covariance-independent finite-union proof follows the Apache 2.0 source
`Targets.TalagrandOverlapTail`; no SK covariance identity is invoked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixed_replica_tail_of_quadratic_bound {n k : ℕ}
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) (hs : 0 < s.m 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (d : ℕ) (hd : d ≤ k + 1)
    {K η : ℝ} (hK : 0 < K) (hη : 0 < η)
    (hquad : ∀ u ∈ attainableOverlaps n,
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U d t u ≤
        2 * mixedInterpolationPsi ξ s h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    guerraReplicaMeasure n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t d
      (fun σ τ => if 2 * K * mixedInterpolationGap ξ s h sk.U t + η ≤
        (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0) ≤
      (n + 1 : ℝ) * (talagrandEventConstant (mixedClockScheme ξ s) (mixedBeta ξ) (η / K) *
        Real.exp (-(n : ℝ) / talagrandEventConstant (mixedClockScheme ξ s) (mixedBeta ξ) (η / K))) := by
  have hε : 0 < η / K := div_pos hη hK
  have hmass : 0 < (mixedClockScheme ξ s).m 1 := hs
  apply guerraReplicaMeasure_overlapTail_le (mixedClockScheme ξ s) (mixedBeta ξ) h
    sk.hU.repr_measurable ht d (s.q (k + 2 - d)) _
    (mul_nonneg (talagrandEventConstant_pos (mixedClockScheme ξ s) (mixedBeta ξ) hmass hε).le
      (Real.exp_pos _).le)
  intro u hu htail
  apply mixed_talagrand_proposition_2_5 sk (mixedClockScheme ξ s) h hn hmass ht u
    (mem_attainableOverlaps.mp hu) d hd hε
  have he : 2 * mixedInterpolationGap ξ s h sk.U t + η / K ≤
      (u - s.q (k + 2 - d)) ^ 2 / K := by
    apply (le_div_iff₀ hK).mpr
    have hc : η / K * K = η := div_mul_cancel₀ η hK.ne'
    nlinarith only [htail, hc]
  dsimp only [mixedInterpolationGap] at he
  linarith only [hquad u hu, he]

theorem mixedOverlapTail_of_quadratic_bound {n k : ℕ}
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) (hs : 0 < s.m 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {K η : ℝ} (hK : 0 < K) (hη : 0 < η)
    (hquad : ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U d t u ≤
        2 * mixedInterpolationPsi ξ s h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    mixedOverlapTail ξ s h sk.U t (2 * K * mixedInterpolationGap ξ s h sk.U t + η) ≤
      (n + 1 : ℝ) * (talagrandEventConstant (mixedClockScheme ξ s) (mixedBeta ξ) (η / K) *
        Real.exp (-(n : ℝ) / talagrandEventConstant (mixedClockScheme ξ s) (mixedBeta ξ) (η / K))) := by
  apply mixedOverlapTail_le_of_replicaMeasure ξ sk s h ht
  intro d hd1 hd
  exact mixed_replica_tail_of_quadratic_bound ξ sk s h hn hs ht d hd hK hη (hquad d hd1 hd)

theorem mixedOverlapTail_eventually_of_quadratic_bound
    (Ωn : ℕ → Type u) [∀ n, MeasureSpace (Ωn n)]
    [∀ n, IsProbabilityMeasure (ℙ : Measure (Ωn n))]
    (ξ : AdmissibleEvenMixture) (sk : ∀ n, MixedDisorder (Ω := Ωn n) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (hs : 0 < s.m 1)
    {t₀ K : ℝ} (ht₀ : t₀ < 1) (hK : 0 < K)
    (hquad : ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U d t u ≤
          2 * mixedInterpolationPsi ξ s h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      mixedOverlapTail ξ s h (sk n).U t (2 * K * mixedInterpolationGap ξ s h (sk n).U t + η) ≤ η := by
  intro η hη
  have hmass : 0 < (mixedClockScheme ξ s).m 1 := hs
  have hC := talagrandEventConstant_pos (mixedClockScheme ξ s) (mixedBeta ξ) hmass (div_pos hη hK)
  have hsmall := (tendsto_overlap_union_bound hC).eventually (gt_mem_nhds hη)
  filter_upwards [hquad, eventually_gt_atTop 0, hsmall] with n hquadn hn hsmalln
  intro t ht
  exact (mixedOverlapTail_of_quadratic_bound ξ (sk n) s h hn hs ⟨ht.1, ht.2.trans ht₀⟩ hK hη
    (hquadn t ht)).trans hsmalln.le

/-- Conditional only on the explicitly stated constrained-pressure estimate.
This theorem does not claim that estimate or the physical Parisi lower bound. -/
theorem mixedInterpolation_uniform_of_quadratic_bound
    (Ωn : ℕ → Type u) [∀ n, MeasureSpace (Ωn n)]
    [∀ n, IsProbabilityMeasure (ℙ : Measure (Ωn n))]
    (ξ : AdmissibleEvenMixture) (sk : ∀ n, MixedDisorder (Ω := Ωn n) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (hs : 0 < s.m 1)
    {t₀ K : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hK : 0 < K)
    (hquad : ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U d t u ≤
          2 * mixedInterpolationPsi ξ s h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) t₀,
      |guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U t -
        mixedInterpolationPsi ξ s h t| < ε := by
  exact mixedInterpolation_uniform_of_overlap_concentration Ωn ξ sk s h ht₀
    (K := 2 * K) (by positivity)
    (mixedOverlapTail_eventually_of_quadratic_bound Ωn ξ sk s h hs ht₀.2 hK hquad)

end FourPapersCommon
