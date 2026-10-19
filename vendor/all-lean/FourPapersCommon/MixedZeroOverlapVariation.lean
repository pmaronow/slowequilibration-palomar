module
public import FourPapersCommon.MixedTerminalStationarity
public import Targets.Section4ZeroOverlapVariation
public import FourPapersCommon.MixtureJetBounds

@[expose] public section

/-! Genuine same-depth right competitors at physical first overlap zero.
The derivative retains ξ″(u) and the true covariance clock ξ′(u). -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixedBeta_sq_mul_clock (ξ : AdmissibleEvenMixture) (u : ℝ) :
    (mixedBeta ξ)^2*ξ.clock u=ξ.first u := by
  rw [mixedBeta_sq,AdmissibleEvenMixture.clock]
  field_simp [ξ.variance_pos.ne']

theorem mixed_zeroOverlap_stationarity_factor {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (hk : 1 ≤ k) (hq : s.q 1 = 0) (u : ℝ) :
    section4TVarianceQ (mixedClockScheme ξ (section4StationarityBase s 1 le_rfl hk))
      (mixedBeta ξ) h 2 (s.m 1)
      (mixedLeftSplitVariance ξ (section4StationarityBase s 1 le_rfl hk) 2 1 u) =
      zeroOuterSquaredSlope (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) k)
        (s.m 1) ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h (ξ.first u) := by
  rw [mixedLeftSplitVariance_eq_clock,one_mul,mixedClockScheme_stationarityBase]
  have hbq : (section4StationarityBase (mixedClockScheme ξ s) 1 le_rfl hk).q 2 =
      (mixedClockScheme ξ s).q 2 := rfl
  rw [hbq]
  simpa only [mixedBeta_sq_mul_clock,mixedClockScheme_m] using
    section4TVarianceQ_zeroOverlap_stationarityBase (mixedClockScheme ξ s)
      (mixedBeta ξ) h hk (by simp only [mixedClockScheme_q,hq,ξ.clock_zero]) (ξ.clock u)

theorem mixed_zeroOverlap_terminal_factor (ξ : AdmissibleEvenMixture)
    (s : RSBScheme 0) (h u : ℝ) :
    section4TVarianceQ (mixedClockScheme ξ (section4TerminalBase s)) (mixedBeta ξ) h 1 1
      (mixedLeftSplitVariance ξ (section4TerminalBase s) 1 1 u) =
      zeroOuterSquaredSlope (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) 0)
        (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) 0)
        (s.m 1) ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h (ξ.first u) := by
  rw [mixedLeftSplitVariance_eq_clock,one_mul,mixedClockScheme_terminalBase]
  have hbq : (section4TerminalBase (mixedClockScheme ξ s)).q 1 =
      (mixedClockScheme ξ s).q 2 := by
    rw [show (section4TerminalBase (mixedClockScheme ξ s)).q 1=1 by simp [section4TerminalBase]]
    exact (mixedClockScheme ξ s).q_top.symm
  rw [hbq]
  simpa only [mixedBeta_sq_mul_clock,mixedClockScheme_m] using
    section4TVarianceQ_zeroOverlap_terminalBase (mixedClockScheme ξ s) (mixedBeta ξ) h (ξ.clock u)

theorem exists_mixedZeroOverlap_comparator {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (hq : s.q 1 = 0)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    ∃ f : ℝ → ℝ,
      (∀ u ∈ Icc 0 (s.q 2),f 0 ≤ f u) ∧
      (∀ u ∈ Icc 0 (s.q 2), HasDerivWithinAt f
        (ξ.second u*s.m 1/2*(u-zeroOuterSquaredSlope
          (parisiF (mixedClockScheme ξ s) (mixedBeta ξ) k)
          (parisiFDeriv (mixedClockScheme ξ s) (mixedBeta ξ) k)
          (s.m 1) ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 2) h (ξ.first u)))
        (Icc 0 (s.q 2)) u) := by
  cases k with
  | zero =>
    let b := section4TerminalBase s
    refine ⟨mixedSection4Phi ξ b h 1 1,?_,?_⟩
    · intro u hu
      have H := mixedSection4Phi_terminalBase_min ξ s h hmin
        (u := u) (by simpa only [s.q_zero,s.q_top] using hu)
      simpa only [Nat.zero_add,hq] using H
    · intro u hu
      have hbq0 : b.q 0 = 0 := b.q_zero
      have hbq1 : b.q 1 = s.q 2 := by simp [b,section4TerminalBase,s.q_top]
      have hd := hasDerivWithinAt_mixedSection4Phi_overlap ξ b h (r := 1) le_rfl le_rfl
        (m := 1) ⟨zero_le_one,le_rfl⟩
        (by simpa only [Nat.reduceSub,b.m_zero] using zero_le_one)
        (u := u) (by simpa only [Nat.reduceSub,hbq0,hbq1] using hu)
      rw [show 1-1=(0:ℕ) by decide,b.m_zero,sub_zero,hbq0,hbq1,
        mixed_zeroOverlap_terminal_factor ξ s h u] at hd
      simpa only [s.m_top,mul_one] using hd
  | succ k =>
    have hk : 1 ≤ k+1 := by omega
    let b := section4StationarityBase s 1 le_rfl hk
    refine ⟨mixedSection4Phi ξ b h 2 (s.m 1),?_,?_⟩
    · intro u hu
      have H := mixedSection4Phi_stationarityBase_min ξ s h le_rfl hk hmin
        (u := u) (by simpa only [hq] using hu)
      simpa only [hq] using H
    · intro u hu
      have hbm1 : b.m 1=0 := by simp [b,section4StationarityBase,RSBScheme.lowerMass,s.m_zero]
      have hbq1 : b.q 1=0 := hq
      have hbq2 : b.q 2=s.q 2 := rfl
      have hd := hasDerivWithinAt_mixedSection4Phi_overlap ξ b h (r := 2) (by omega) (by omega)
        (m := s.m 1) ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩
        (by simpa only [Nat.reduceSub,hbm1] using s.m_nonneg (p := 1) (by omega))
        (u := u) (by simpa only [Nat.reduceSub,hbq1,hbq2] using hu)
      rw [show 2-1=(1:ℕ) by decide,hbm1,sub_zero,hbq1,hbq2,
        mixed_zeroOverlap_stationarity_factor ξ s h hk hq u] at hd
      exact hd

end FourPapersCommon
