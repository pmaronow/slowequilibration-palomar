module
public import FourPapersCommon.MixedSignedInitialInterpolation
public import Targets.Section5InterleavedOffDiagonalBound

@[expose] public section

/-! Interleaving is determined by masses. Changing the covariance clock
preserves the tagged order and maps the genuine cumulative overlaps. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
variable {k : ℕ}
set_option maxHeartbeats 800000

@[simp] theorem section5Interleaving_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j : ℕ) :
    section5Interleaving (mixedClockScheme ξ s) r j=section5Interleaving s r j := rfl

@[simp] theorem section5InterleavingRank_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j i : ℕ) :
    section5InterleavingRank (mixedClockScheme ξ s) r j i=section5InterleavingRank s r j i := rfl

@[simp] theorem section5ReverseMass_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j i : ℕ) :
    section5ReverseMass (mixedClockScheme ξ s) r j i=section5ReverseMass s r j i := rfl

@[simp] theorem section5InterleavedMassNat_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j i : ℕ) :
    section5InterleavedMassNat (mixedClockScheme ξ s) r j i=section5InterleavedMassNat s r j i := rfl

@[simp] theorem section5ReverseMode_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j : ℕ) (e : Bool) (i : ℕ) :
    section5ReverseMode (mixedClockScheme ξ s) r j e i=section5ReverseMode s r j e i := rfl

theorem clock_nonneg (ξ : AdmissibleEvenMixture) {v : ℝ} (hv : 0≤v) : 0≤ξ.clock v := by
  apply div_nonneg _ ξ.variance_pos.le
  apply tsum_nonneg
  intro p
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (ξ.nonneg p)) (pow_nonneg hv _)

@[simp] theorem clock_abs (ξ : AdmissibleEvenMixture) (v : ℝ) :
    ξ.clock |v|=|ξ.clock v| := by
  by_cases hv:0≤v
  · rw [abs_of_nonneg hv,abs_of_nonneg (clock_nonneg ξ hv)]
  · have hvn:0≤-v:=by linarith
    rw [abs_of_neg (lt_of_not_ge hv),clock_neg,abs_of_nonpos]
    have hh:=clock_nonneg ξ hvn
    rw [clock_neg] at hh
    linarith

@[simp] theorem section5InterleavedRho_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j : ℕ) (v : ℝ) (i : ℕ) :
    section5InterleavedRho (mixedClockScheme ξ s) r j (ξ.clock v) i =
      ξ.clock (section5InterleavedRho s r j v i) := by
  simp only [section5InterleavedRho,section5InterleavingRank_clock,section5Rho_clock]

 theorem clock_lt_zero_iff (ξ : AdmissibleEvenMixture) (v : ℝ) (hv : |v|≤1) :
    ξ.clock v<0 ↔ v<0 := by
  rw [AdmissibleEvenMixture.clock,div_lt_iff₀ ξ.variance_pos,zero_mul]
  have hh : ξ.first v<ξ.first 0 ↔ v<0 :=
    ξ.first_strictMonoOn.lt_iff_lt (abs_le.mp hv) (by norm_num)
  simpa only [ξ.first_zero] using hh

 theorem clock_mem_abs_interval (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    {j : ℕ} (hj : j≤k+1) {v : ℝ} (hv : |v|∈Icc (s.q (j-1)) (s.q j)) :
    |ξ.clock v|∈Icc ((mixedClockScheme ξ s).q (j-1)) ((mixedClockScheme ξ s).q j) := by
  rw [←clock_abs]
  have hv0 : |v|∈Icc (0:ℝ) 1 := ⟨abs_nonneg v,hv.2.trans (s.q_le_one (by omega))⟩
  exact ⟨ξ.clock_strictMonoOn.monotoneOn ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hv0 hv.1,
    ξ.clock_strictMonoOn.monotoneOn hv0 ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hv.2⟩

 theorem section5InterleavedCross_clock (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r : ℕ) {j : ℕ} (hj : j≤k+1) (v : ℝ) (hv : |v|≤1) (i : ℕ) :
    section5InterleavedCross (mixedClockScheme ξ s) r hj (ξ.clock v) i =
      ξ.clock (section5InterleavedCross s r hj v i) := by
  unfold section5InterleavedCross section5TrialSign
  simp only [clock_lt_zero_iff ξ v hv,←clock_abs,section5InterleavedRho_clock]
  by_cases hv:v<0
  · simp only [if_pos hv,neg_one_mul,clock_neg]
    rfl
  · simp only [if_neg hv,one_mul]
    rfl

 theorem section5InterleavedRho_first_increment (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r j : ℕ) (v : ℝ) (i : ℕ) :
    (mixedBeta ξ)^2*(section5InterleavedRho (mixedClockScheme ξ s) r j |ξ.clock v| (i+1)-
      section5InterleavedRho (mixedClockScheme ξ s) r j |ξ.clock v| i)=
      ξ.first (section5InterleavedRho s r j |v| (i+1))-
        ξ.first (section5InterleavedRho s r j |v| i) := by
  rw [←clock_abs,section5InterleavedRho_clock,section5InterleavedRho_clock,mixed_first_increment]

theorem section5ReverseMode_first_covariance_increment (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (r : ℕ) {j : ℕ} (hj : j≤k+1) (v : ℝ) (hv : |v|≤1)
    (l : ℕ) (hl : l<2*k+4+1) :
    ξ.first (section5InterleavedCross s r hj v (2*k+4-l+1))-
      ξ.first (section5InterleavedCross s r hj v (2*k+4-l)) =
    (ξ.first (section5InterleavedRho s r j |v| (2*k+4-l+1))-
      ξ.first (section5InterleavedRho s r j |v| (2*k+4-l)))*
      (section5ReverseMode s r j (decide (v<0)) l).correlation := by
  have hh:=congrArg (fun z=>(mixedBeta ξ)^2*z)
    (section5ReverseMode_covariance_increment (mixedClockScheme ξ s) r hj (ξ.clock v) l hl)
  simp only [section5InterleavedCross_clock ξ s r hj v hv,←clock_abs,
    section5InterleavedRho_clock,section5ReverseMode_clock,clock_lt_zero_iff ξ v hv] at hh
  simpa only [←mul_assoc,mixed_first_increment] using hh

end FourPapersCommon
