module
public import FourPapersCommon.MixedInterleavedTrace
public import FourPapersCommon.MixedInterleavedClock
public import FourPapersCommon.MixedInterleavedDerivative
public import FourPapersCommon.MixedInterleavedCorrection

@[expose] public section

/-! Genuine tagged mixed interpolation bounds. Only Gaussian variances are
clocked; physical overlaps remain in the tangent remainder and constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem section5InterleavingRank_le (s : RSBScheme k) (r j i : ℕ) :
    section5InterleavingRank s r j i≤k+3 := by
  unfold section5InterleavingRank
  calc
    _ ≤ ∑ p : Fin (k+3), (1:ℕ) := by
      apply Finset.sum_le_sum
      intro p _
      split_ifs <;> omega
    _ = _ := by simp

 theorem section5InterleavedRho_mem_unit (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j≤k+1) {v : ℝ} (hv : |v|≤1) (i : ℕ) :
    section5InterleavedRho s r j |v| i∈Icc (-1:ℝ) 1 :=
  section5Rho_mem_unit s (by omega) ⟨abs_nonneg v,hv⟩ (section5InterleavingRank_le s r j i)

 theorem section5InterleavedCross_mem_unit (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j≤k+1) {v : ℝ} (hv : |v|≤1) (i : ℕ) :
    section5InterleavedCross s r hj v i∈Icc (-1:ℝ) 1 := by
  have hh:=section5InterleavedRho_mem_unit s r hj hv (min i (section5InterleavingCutoff s r hj))
  unfold section5InterleavedCross section5TrialSign
  split_ifs
  · simp only [neg_one_mul]
    constructor <;> linarith [hh.1,hh.2]
  · simpa only [one_mul] using hh

 theorem mixedInterleaved_actualTraceHeat_offDiagonal_le
    (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) (r : ℕ) {j : ℕ}
    (hj0 : 1≤j) (hj : j≤k+1) (u v : ℝ) {t w : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hv : |v|∈Icc (s.q (j-1)) (s.q j)) (hw : w≤1)
    (U : EnergySpace n) [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n→ℝ) :
    let S:=mixedClockScheme ξ s
    let β:=mixedBeta ξ
    (1/(n:ℝ))*(t/2*(∑i:sk.hU.ι,(sk.hU.τ i:ℝ)*
      mixedConstrainedSecond (section5ReverseMode S r j (decide (ξ.clock v<0)))
        (section5ReverseMass S r j)
        (fun l=>section5ReversePathVariance S β t (ξ.clock v) r j l w)
        (2*k+4+1) U (sk.hU.w i) (sk.hU.w i) u x y)-
      t*∑l:Fin (2*k+4+1), β^2*
        (section5InterleavedRho S r j |ξ.clock v| (2*k+4-l+1)-
          section5InterleavedRho S r j |ξ.clock v| (2*k+4-l))*
        mixedLevelVarianceD U u (section5ReverseMode S r j (decide (ξ.clock v<0)))
          (section5ReverseMass S r j)
          (fun i=>section5ReversePathVariance S β t (ξ.clock v) r j i w) l
          (2*k+4+1-(l+1)) (section5ReversePathVariance S β t (ξ.clock v) r j l w) x y) ≤
      -2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
  dsimp only
  have hv1 : |v|≤1:=hv.2.trans (s.q_le_one (by omega))
  let mode:=section5ReverseMode s r j (decide (v<0))
  let m:=section5ReverseMass s r j
  let path:=fun l=>section5ReversePathVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r j l w
  let ρ:=section5InterleavedRho s r j |v|
  let c:=section5InterleavedCross s r hj v
  let μ:=fun p=>mixedConstrainedReplica mode m path (2*k+4-p)
    (2*k+4+1-(2*k+4-p)) U u x y
  have hm : ∀l,0 ≤ m l:=section5ReverseMass_nonneg s r hj
  have hv0 : ∀l,0≤path l:=section5ReversePathVariance_nonneg (mixedClockScheme ξ s)
    (mixedBeta ξ) ht hw r hj (clock_mem_abs_interval ξ s hj hv)
  have hρ:=section5InterleavedRho_endpoints s r hj0 hj |v|
  have hc:=section5InterleavedCross_endpoints s r hj0 hj v
  have H:=mixedConstrained_mixed_trace_sub_heat_eq_covariance_mismatch hn ξ sk U t u v
    mode (section5InterleavedMassNat s r j) ρ c path (2*k+4)
    (by intro i;rw [←section5ReverseMass_eq_massNat];exact hm i) hv0
    (section5InterleavedMassNat_endpoints s r hj0 hj).1
    (section5InterleavedMassNat_endpoints s r hj0 hj).2 hρ.1 hc.1
    (by simpa only [show 2*k+4+1=(k+2)+(k+3) by omega] using hρ.2)
    (by simpa only [show 2*k+4+1=(k+2)+(k+3) by omega] using hc.2)
    (section5ReverseMode_first_covariance_increment ξ s r hj v hv1) x y
  have Hc:=mixedPairCovarianceExpressionMismatch_le hn ξ u v ht.1
    (section5InterleavedMassNat s r j) ρ c (2*k+4)
    (section5InterleavedMassNat_endpoints s r hj0 hj).2
    (fun _ hi=>section5InterleavedMassNat_mono s r j hi) hρ.1 hc.1
    (by simpa only [show 2*k+4+1=(k+2)+(k+3) by omega] using hρ.2)
    (by simpa only [show 2*k+4+1=(k+2)+(k+3) by omega] using hc.2) μ
    (fun l hl p q=>mixedConstrainedReplica_nonneg U u mode m path hm hv0 _ _ x y p q)
    (fun l hl=>sum_mixedConstrainedReplica U u mode m path hm hv0 _ _ x y)
    (fun l hl=>section5InterleavedRho_mem_unit s r hj hv1 (l+1))
    (fun l hl=>section5InterleavedCross_mem_unit s r hj hv1 (l+1))
  have hmass : m=fun i=>section5InterleavedMassNat s r j (2*k+4-i):=
    funext (section5ReverseMass_eq_massNat s r j)
  rw [←hmass] at H
  dsimp [ρ,c] at Hc
  rw [mixedInterleavedCross_correction ξ s r hj0 hj v] at Hc
  have hb : (1/(n:ℝ))*(t/2*(∑i:sk.hU.ι,(sk.hU.τ i:ℝ)*
      mixedConstrainedSecond mode m path (2*k+4+1) U (sk.hU.w i) (sk.hU.w i) u x y)-
    t*∑l:Fin (2*k+4+1),(ξ.first (ρ (2*k+4-l+1))-ξ.first (ρ (2*k+4-l)))*
      mixedLevelVarianceD U u mode m path l (2*k+4+1-(l+1)) (path l) x y) ≤
    -2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
    rw [H]
    dsimp [μ] at Hc
    linarith
  have hmode : section5ReverseMode (mixedClockScheme ξ s) r j (decide (ξ.clock v<0))=mode := by
    funext i
    simp only [section5ReverseMode_clock,clock_lt_zero_iff ξ v hv1,mode]
  have hmass' : section5ReverseMass (mixedClockScheme ξ s) r j=m := by
    funext i
    exact section5ReverseMass_clock ξ s r j i
  simpa only [path,ρ,hmode,hmass',section5InterleavedRho_first_increment] using hb

end FourPapersCommon
