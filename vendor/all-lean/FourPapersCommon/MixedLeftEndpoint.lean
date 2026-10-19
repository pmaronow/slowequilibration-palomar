module
public import FourPapersCommon.MixedGuerraConvergence
public import Targets.Section5LambdaUPrime
public import Targets.TalagrandRightInterpolation

@[expose] public section

/-! Actual left and right second-interpolation paths for a mixed covariance.

The scalar Gaussian recursion is evaluated in variance-clock coordinates;
the constrained overlap and its Lagrange multiplier remain physical. These
endpoint identities use the actual cascades, not supplied comparison premises.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω]
set_option maxHeartbeats 800000

def mixedLeftSplitVariance (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (t u : ℝ) : ℝ :=
  t * (ξ.first (s.q r) - ξ.first u)

def mixedRightSplitVariance (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (t u : ℝ) : ℝ :=
  t * (ξ.first u - ξ.first (s.q r))

theorem mixedLeftSplitVariance_eq_clock (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (t u : ℝ) :
    mixedLeftSplitVariance ξ s r t u =
      t * ((mixedBeta ξ) ^ 2 * ((mixedClockScheme ξ s).q r - ξ.clock u)) := by
  rw [mixedBeta_sq]
  simp only [mixedLeftSplitVariance, mixedClockScheme_q, AdmissibleEvenMixture.clock]
  field_simp [ξ.variance_pos.ne']

theorem mixedRightSplitVariance_eq_clock (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (t u : ℝ) :
    mixedRightSplitVariance ξ s r t u =
      t * ((mixedBeta ξ) ^ 2 * (ξ.clock u - (mixedClockScheme ξ s).q r)) := by
  rw [mixedBeta_sq]
  simp only [mixedRightSplitVariance, mixedClockScheme_q, AdmissibleEvenMixture.clock]
  field_simp [ξ.variance_pos.ne']

theorem clock_mem_left_interval (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    ξ.clock u ∈ Icc ((mixedClockScheme ξ s).q (r - 1)) ((mixedClockScheme ξ s).q r) := by
  have hleft : s.q (r - 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have hright : s.q r ∈ Icc (0 : ℝ) 1 := ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have hu0 : u ∈ Icc (0 : ℝ) 1 := ⟨hleft.1.trans hu.1, hu.2.trans hright.2⟩
  exact ⟨ξ.clock_strictMonoOn.monotoneOn hleft hu0 hu.1,
    ξ.clock_strictMonoOn.monotoneOn hu0 hright hu.2⟩

theorem clock_mem_right_interval (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Icc (s.q r) (s.q (r + 1))) :
    ξ.clock u ∈ Icc ((mixedClockScheme ξ s).q r) ((mixedClockScheme ξ s).q (r + 1)) := by
  have hleft : s.q r ∈ Icc (0 : ℝ) 1 := ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have hright : s.q (r + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have hu0 : u ∈ Icc (0 : ℝ) 1 := ⟨hleft.1.trans hu.1, hu.2.trans hright.2⟩
  exact ⟨ξ.clock_strictMonoOn.monotoneOn hleft hu0 hu.1,
    ξ.clock_strictMonoOn.monotoneOn hu0 hright hu.2⟩

theorem mixedLeftSplitVariance_mem (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    mixedLeftSplitVariance ξ s r t u ∈ Icc (0 : ℝ)
      ((mixedBeta ξ) ^ 2 * ((mixedClockScheme ξ s).q r - (mixedClockScheme ξ s).q (r - 1))) := by
  rw [mixedLeftSplitVariance_eq_clock]
  exact section5SplitVariance_mem (mixedClockScheme ξ s) (mixedBeta ξ) ht
    (clock_mem_left_interval ξ s hr hu)

theorem mixedRightSplitVariance_mem (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q r) (s.q (r + 1))) :
    mixedRightSplitVariance ξ s r t u ∈ Icc (0 : ℝ)
      ((mixedBeta ξ) ^ 2 * ((mixedClockScheme ξ s).q (r + 1) - (mixedClockScheme ξ s).q r)) := by
  rw [mixedRightSplitVariance_eq_clock]
  exact section5RightSplitVariance_mem (mixedClockScheme ξ s) (mixedBeta ξ) ht
    (clock_mem_right_interval ξ s hr hu)

def mixedLeftInterpolation {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m t u w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5Mass s r m (k + 2 - j))
      (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t
        (ξ.clock u) r (k + 2 - j) w) (k + 3 - r)
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ

def mixedRightInterpolation {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m t u w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5RightMass s r m (k + 2 - j))
      (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t
        (ξ.clock u) r (k + 2 - j) w) (k + 2 - r)
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem mixedLeftInterpolation_zero {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m t u : ℝ) :
    mixedLeftInterpolation ξ s h U r m t u 0 =
      section5FieldEndpoint n (mixedClockScheme ξ s) (mixedBeta ξ) h u r m
        (mixedLeftSplitVariance ξ s r t u) := by
  rw [mixedLeftSplitVariance_eq_clock]
  simp only [mixedLeftInterpolation, zero_mul, Real.sqrt_zero, zero_smul,
    constrainedPairFieldBase_zero, section5InterpolationVariance_zero,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    section5FieldEndpoint, one_div]
  rfl

theorem mixedRightInterpolation_zero {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m t u : ℝ) :
    mixedRightInterpolation ξ s h U r m t u 0 =
      section5RightFieldEndpoint n (mixedClockScheme ξ s) (mixedBeta ξ) h u r m
        (mixedRightSplitVariance ξ s r t u) := by
  rw [mixedRightSplitVariance_eq_clock]
  simp only [mixedRightInterpolation, zero_mul, Real.sqrt_zero, zero_smul,
    constrainedPairFieldBase_zero, section5RightInterpolationVariance_zero,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    section5RightFieldEndpoint, one_div]
  rfl

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem mixedLeftInterpolation_one {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    mixedLeftInterpolation ξ s h U r m t u 1 =
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U (k + 2 - r) t u := by
  simp only [mixedLeftInterpolation, section5InterpolationVariance_one, one_mul]
  change (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n
      (fun j => section5Mass (mixedClockScheme ξ s) r m (k + 2 - j))
      (fun j => section5FrozenVariance (mixedClockScheme ξ s) (mixedBeta ξ) t r (k + 2 - j))
      (k + 3 - r) (constrainedPairFieldBase n (Real.sqrt t • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ = _
  simp only [section5Cascade_one (mixedClockScheme ξ s) (mixedBeta ξ) h _ hr0 hr m u ht,
    constrainedPhi]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem mixedRightInterpolation_one {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    mixedRightInterpolation ξ s h U r m t u 1 =
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U (k + 2 - r) t u := by
  simp only [mixedRightInterpolation, section5RightInterpolationVariance_one, one_mul]
  change (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n
      (fun j => section5RightMass (mixedClockScheme ξ s) r m (k + 2 - j))
      (fun j => section5FrozenVariance (mixedClockScheme ξ s) (mixedBeta ξ) t r (k + 2 - j))
      (k + 2 - r) (constrainedPairFieldBase n (Real.sqrt t • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ = _
  simp only [section5RightCascade_one (mixedClockScheme ξ s) (mixedBeta ξ) h _ hr0 hr m u ht,
    constrainedPhi]

theorem mixedLeftInterpolation_zero_le {n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr : r ≤ k + 1) {m t u : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    mixedLeftInterpolation ξ s h U r m t u 0 ≤
      2 * Real.log 2 + section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r m
        (mixedLeftSplitVariance ξ s r t u) ℓ - ℓ * u := by
  rw [mixedLeftInterpolation_zero]
  exact section5FieldEndpoint_le hn (mixedClockScheme ξ s) (mixedBeta ξ) h u hr hm
    (mixedLeftSplitVariance_mem ξ s hr ht hu) hu' ℓ

theorem mixedRightInterpolation_zero_le {n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr : r ≤ k + 1) {m t u : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q r) (s.q (r + 1)))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    mixedRightInterpolation ξ s h U r m t u 0 ≤
      2 * Real.log 2 + section5RightV (mixedClockScheme ξ s) (mixedBeta ξ) h r m
        (mixedRightSplitVariance ξ s r t u) ℓ - ℓ * u := by
  rw [mixedRightInterpolation_zero]
  exact section5RightFieldEndpoint_le hn (mixedClockScheme ξ s) (mixedBeta ξ) h u hr hm
    (mixedRightSplitVariance_mem ξ s hr ht hu) hu' ℓ

theorem mixedLeftInterpolation_zero_lambda_gain {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    (U : Ω → EnergySpace n) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) :
    mixedLeftInterpolation ξ s h U r (s.m (r - 1)) t u 0 ≤
      2 * (Real.log 2 + parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h) -
        (section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
          (mixedLeftSplitVariance ξ s r t u) - u) ^ 2 / 2 := by
  obtain ⟨ℓ, hℓ⟩ := section5V_baseline_lambda_gain_Q (mixedClockScheme ξ s) (mixedBeta ξ) h
    hr0 hr (mixedLeftSplitVariance_mem ξ s hr ht hu) u
  have hm := s.m_nonneg (p := r - 1) (by omega)
  have hh := mixedLeftInterpolation_zero_le hn ξ s h U hr hm ht hu hu' ℓ
  change section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
    (mixedLeftSplitVariance ξ s r t u) ℓ - ℓ * u ≤ _ at hℓ
  simp only [mixedClockScheme_m] at hℓ
  linarith

end FourPapersCommon
