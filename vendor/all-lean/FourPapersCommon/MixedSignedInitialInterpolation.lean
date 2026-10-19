module
public import FourPapersCommon.MixedConditionedInitialInterpolation

@[expose] public section

/-! The actual retained-frozen-field signed initial comparison for mixed
even covariance. Hamiltonian reflection is derived from its genuine covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem clock_neg (ξ : AdmissibleEvenMixture) (v : ℝ) : ξ.clock (-v)= -ξ.clock v := by
  simp only [AdmissibleEvenMixture.clock, ξ.first_odd, neg_div]

 theorem tangentRemainder_neg_neg (ξ : AdmissibleEvenMixture) (u v : ℝ) :
    ξ.tangentRemainder (-u) (-v)=ξ.tangentRemainder u v := by
  simp only [AdmissibleEvenMixture.tangentRemainder,ξ.value_even,ξ.first_odd]
  ring

 theorem clock_mem_signed_initial (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    {v : ℝ} (hv : v∈Icc (-s.q 1) (0:ℝ)) :
    ξ.clock v∈Icc (-(mixedClockScheme ξ s).q 1) (0:ℝ) := by
  have hvn : -v∈Icc (0:ℝ) (s.q 1) := by constructor <;> linarith [hv.1,hv.2]
  have hh:=clock_mem_initial_interval ξ s hvn
  rw [clock_neg] at hh
  constructor <;> linarith [hh.1,hh.2]

/-- Signed off-diagonal path after conditioning on the retained positive
field. The original overlaps `u,v` are negative; the conditioned state space
has overlap `-u` and the trial path ends at `-v`. -/
noncomputable def mixedSignedInitialInterpolationOffDiagonal
    (n : ℕ) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (Z : Ω → EnergySpace n)
    (t u v w : ℝ) : ℝ :=
  ∫ z, mixedConditionedInitialInterpolationOffDiagonal n ξ s Z t (-u) (-v)
    (fun i => h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)) * z i)
    (fun i => -(h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)) * z i)) w ∂piGauss n

/-- Direct reflected form of the off-diagonal signed path.  The constraint is
`u`, while every trial covariance (including the anti-shared prefix) uses
`v`. -/
noncomputable def mixedSignedInitialInterpolationOffDiagonalDirect
    (n : ℕ) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (Z : Ω → EnergySpace n)
    (t u v w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, section5SignedInitialOuter n (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) w
    (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock (-v)) 1 (k + 2 - j) w)
      (k + 2) (constrainedPairFieldBase n (Real.sqrt (w * t) • Z ω) u) (k + 2))
    (fun _ => h) (fun _ => h) ∂ℙ

/-- Conditioning/reflection identity for separated signed constraint and trial
overlaps. -/
theorem mixedSignedInitialInterpolationOffDiagonal_eq_direct
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {t u v w : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) (hw : w ∈ Icc 0 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    mixedSignedInitialInterpolationOffDiagonalDirect n ξ s h sk.U t u v w =
      mixedSignedInitialInterpolationOffDiagonal n ξ s h sk.U t u v w := by
  letI := constrainedPair_nonempty_neg (n := n) u
  have hvn : -v ∈ Icc 0 (s.q 1) := by constructor <;> linarith [hv.1, hv.2]
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock (-v)) 1 (k + 2 - j) w
  let V' := fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock (-v)) (k + 2 - j) w
  let b := (1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)
  have hm (j) : 0 ≤ M j := section5Mass_nonneg s (by omega) le_rfl (by omega)
  have hvV (j) : 0 ≤ V j := by
    dsimp [V]
    simpa only [clock_neg] using
      (section5SignedInitial_variances_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) ht
        (clock_mem_signed_initial ξ s hv) hw).2.2 (k + 2 - j) (by omega)
  have hvV' (j) : 0 ≤ V' j :=
    section5ConditionedInitialVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hvn) hw
  let G := fun (ω : Ω) (z : Fin n → ℝ) => coupledFieldCascade n M V' (k + 2)
    (constrainedPairFieldBase n (Real.sqrt (w * t) • sk.U ω) (-u)) (k + 3)
    (fun i => h + Real.sqrt b * z i) (fun i => -(h + Real.sqrt b * z i))
  have hi : Integrable (fun p : Ω × (Fin n → ℝ) => G p.1 p.2)
      ((ℙ : Measure Ω).prod (piGauss n)) :=
    integrable_constrainedPairFieldCascade_frozen_pair sk.hU (Real.sqrt (w * t)) b
      (-u) M V' hm hvV' (k + 2) (k + 3) (fun _ => h)
  have he : mixedSignedInitialInterpolationOffDiagonalDirect n ξ s h sk.U t u v w =
      (1 / (n : ℝ)) * ∫ ω, ∫ z, G ω z ∂piGauss n ∂ℙ := by
    unfold mixedSignedInitialInterpolationOffDiagonalDirect
    congr 1
    apply integral_congr_ae
    filter_upwards [mixedDisorder_even_ae ξ sk] with ω hω
    have hscaled : ∀ σ, (Real.sqrt (w * t) • sk.U ω) (configFlip n σ) =
        (Real.sqrt (w * t) • sk.U ω) σ := by
      intro σ
      simpa only [PiLp.smul_apply, smul_eq_mul] using
        congrArg (fun z => Real.sqrt (w * t) * z) (hω σ)
    rw [section5SignedInitialOuter, coupledLinearStep_shared, mul_zero,
      coupledLinearStep_zero_signed_shared_commute
        (constrainedPairFieldCascade_growth (Real.sqrt (w * t) • sk.U ω) u M V hm hvV
          (k + 2) (k + 2))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simpa only [M, V, V', G, b, mixedClockScheme_m, clock_neg] using!
        section5SignedInitial_anti_prefix_offDiagonal_eq_conditioned (mixedClockScheme ξ s) (mixedBeta ξ) t u (ξ.clock v) w
        (Real.sqrt (w * t) • sk.U ω) hscaled
        (fun i => h + Real.sqrt b * z i) (fun i => h + Real.sqrt b * z i)
  rw [he, integral_integral_swap hi, ← integral_const_mul]
  rfl

theorem mixedSignedInitialInterpolationOffDiagonal_one
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {t u v : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] :
    mixedSignedInitialInterpolationOffDiagonal n ξ s h sk.U t u v 1 =
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t u := by
  rw [← mixedSignedInitialInterpolationOffDiagonal_eq_direct ξ s h sk
    ht hu hv (w := 1) ⟨zero_le_one, le_rfl⟩]
  unfold mixedSignedInitialInterpolationOffDiagonalDirect constrainedPhi
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    simpa only [section5SignedInitialOuter_one, section5InterpolationVariance_one,
      one_mul, section5Mass, mixedClockScheme_m] using
      section5SignedInitialCascade_one (mixedClockScheme ξ s) (mixedBeta ξ) h (sk.U ω) u ht.2

theorem mixedSignedInitialInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 1) t u ≤
      mixedSignedInitialInterpolationOffDiagonal n ξ s h sk.U t u v 0 -
        t * (2 * mixedSchemeCorrection ξ s) + t*ξ.tangentRemainder u v := by
  letI : Nonempty (AT.ConstrainedPair n (-u)) := constrainedPair_nonempty_neg (n := n) u
  have hupos : -u ∈ Icc 0 1 := by
    constructor
    · linarith [hu.2]
    · linarith [hu.1]
  have hvpos : -v ∈ Icc 0 (s.q 1) := by constructor <;> linarith [hv.1, hv.2]
  have hi0 := integrable_mixedConditionedInitialInterpolationOffDiagonal_frozen
    ξ s h sk.hU ht hupos hvpos (w := 0) ⟨le_rfl, zero_le_one⟩
  have hi1 := integrable_mixedConditionedInitialInterpolationOffDiagonal_frozen
    ξ s h sk.hU ht hupos hvpos (w := 1) ⟨zero_le_one, le_rfl⟩
  rw [← mixedSignedInitialInterpolationOffDiagonal_one ξ s h sk ht hu hv]
  unfold mixedSignedInitialInterpolationOffDiagonal
  calc
    _ ≤ ∫ z, mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t (-u) (-v)
        (fun i => h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)) * z i)
        (fun i => -(h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)) * z i)) 0 -
          t * (2 * mixedSchemeCorrection ξ s) +
          t*ξ.tangentRemainder (-u) (-v) ∂piGauss n :=
      integral_mono hi1 ((hi0.sub (integrable_const _)).add (integrable_const _))
        (fun z => mixedConditionedInitialInterpolationOffDiagonal_endpoint_bound
          hn ξ s sk ht hupos hvpos _ _)
    _ = _ := by
      have hmismatch : ξ.tangentRemainder (-u) (-v)=ξ.tangentRemainder u v :=
        tangentRemainder_neg_neg ξ u v
      rw [hmismatch]
      let f : (Fin n → ℝ) → ℝ := fun z =>
        mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t (-u) (-v)
          (fun i => h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)) * z i)
          (fun i => -(h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1)) * z i)) 0
      have hf : Integrable f (piGauss n) := by simpa [f] using hi0
      change (∫ z, (f z - t * (2 * mixedSchemeCorrection ξ s)) +
        t*ξ.tangentRemainder u v ∂piGauss n) = _
      calc
        _ = (∫ z, f z - t * (2 * mixedSchemeCorrection ξ s) ∂piGauss n) +
            ∫ _ : Fin n → ℝ, t*ξ.tangentRemainder u v ∂piGauss n :=
          integral_add (hf.sub (integrable_const _)) (integrable_const _)
        _ = ((∫ z, f z ∂piGauss n) -
              ∫ _ : Fin n → ℝ, t * (2 * mixedSchemeCorrection ξ s) ∂piGauss n) +
            ∫ _ : Fin n → ℝ, t*ξ.tangentRemainder u v ∂piGauss n := by
          rw [integral_sub hf (integrable_const _)]
        _ = _ := by
          simp [f]

end FourPapersCommon
