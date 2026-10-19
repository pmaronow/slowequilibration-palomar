module
public import FourPapersCommon.MixedSecondInterpolationOffDiagonalBounds
public import FourPapersCommon.MixedSecondCorrection

@[expose] public section

/-! Actual mixed constrained-pressure comparisons with arbitrary physical
constraint and admissible trial overlap. Both the field endpoint and the
theta correction are literal proved quantities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem mixedLeftInterpolationOffDiagonal_zero_le (hn : 0<n)
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (U : Ω→EnergySpace n)
    {r : ℕ} (hr : r≤k+1) {m t u v : ℝ} (hm : 0 ≤ m) (ht : t∈Icc (0:ℝ) 1)
    (hv : v∈Icc (s.q (r-1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] (ell : ℝ) :
    mixedLeftInterpolationOffDiagonal ξ s h U r m t u v 0≤
      2*Real.log 2+section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r m
        (mixedLeftSplitVariance ξ s r t v) ell-ell*u := by
  rw [mixedLeftInterpolationOffDiagonal_zero]
  obtain ⟨p,hp⟩:=Classical.choice (inferInstance : Nonempty (AT.ConstrainedPair n u))
  exact section5FieldEndpoint_le hn (mixedClockScheme ξ s) (mixedBeta ξ) h u hr hm
    (mixedLeftSplitVariance_mem ξ s hr ht hv) ⟨p.1,p.2,hp⟩ ell

 theorem mixedRightInterpolationOffDiagonal_zero_le (hn : 0<n)
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (U : Ω→EnergySpace n)
    {r : ℕ} (hr : r≤k+1) {m t u v : ℝ} (hm : 0 ≤ m) (ht : t∈Icc (0:ℝ) 1)
    (hv : v∈Icc (s.q r) (s.q (r+1)))
    [Nonempty (AT.ConstrainedPair n u)] (ell : ℝ) :
    mixedRightInterpolationOffDiagonal ξ s h U r m t u v 0≤
      2*Real.log 2+section5RightV (mixedClockScheme ξ s) (mixedBeta ξ) h r m
        (mixedRightSplitVariance ξ s r t v) ell-ell*u := by
  rw [mixedRightInterpolationOffDiagonal_zero]
  obtain ⟨p,hp⟩:=Classical.choice (inferInstance : Nonempty (AT.ConstrainedPair n u))
  exact section5RightFieldEndpoint_le hn (mixedClockScheme ξ s) (mixedBeta ξ) h u hr hm
    (mixedRightSplitVariance_mem ξ s hr ht hv) ⟨p.1,p.2,hp⟩ ell

 theorem mixedLeft_constrainedPhi_le (hn : 0<n) (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω:=Ω) n ξ)
    {r : ℕ} (hr0 : 1≤r) (hr : r≤k+1) {m t u v : ℝ}
    (hm : m∈Icc (s.m (r-1)/2) (s.m r)) (ht : t∈Icc (0:ℝ) 1)
    (hv : v∈Icc (s.q (r-1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] (ell : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
      2*Real.log 2+section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r m
        (mixedLeftSplitVariance ξ s r t v) ell-ell*u-
      t*(2*mixedSchemeCorrection ξ s+(m-s.m (r-1))*(ξ.correction (s.q r)-ξ.correction v))+
        t*ξ.tangentRemainder u v := by
  have hb:=mixedLeftInterpolationOffDiagonal_endpoint_bound hn ξ s h sk
    (u:=u) hr0 hr hm ht hv
  rw [mixedLeftPairCorrection_eq ξ s v m hr0 hr] at hb
  have hm0 : 0 ≤ m :=(div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have hz:=mixedLeftInterpolationOffDiagonal_zero_le hn ξ s h sk.U (u:=u) hr hm0 ht hv ell
  linarith

 theorem mixedRight_constrainedPhi_le (hn : 0<n) (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω:=Ω) n ξ)
    {r : ℕ} (hr0 : 1≤r) (hr : r≤k+1) {m t u v : ℝ}
    (hm : m∈Icc (s.m (r-1)) (2*s.m r)) (ht : t∈Icc (0:ℝ) 1)
    (hv : v∈Icc (s.q r) (s.q (r+1)))
    [Nonempty (AT.ConstrainedPair n u)] (ell : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
      2*Real.log 2+section5RightV (mixedClockScheme ξ s) (mixedBeta ξ) h r m
        (mixedRightSplitVariance ξ s r t v) ell-ell*u-
      t*(2*mixedSchemeCorrection ξ s+(m-s.m r)*(ξ.correction v-ξ.correction (s.q r)))+
        t*ξ.tangentRemainder u v := by
  have hb:=mixedRightInterpolationOffDiagonal_endpoint_bound hn ξ s h sk
    (u:=u) hr0 hr hm ht hv
  rw [mixedRightPairCorrection_eq ξ s v m hr] at hb
  have hm0 : 0 ≤ m :=(s.m_nonneg (by omega)).trans hm.1
  have hz:=mixedRightInterpolationOffDiagonal_zero_le hn ξ s h sk.U (u:=u) hr hm0 ht hv ell
  linarith

end FourPapersCommon
