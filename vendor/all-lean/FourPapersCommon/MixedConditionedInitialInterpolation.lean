module
public import FourPapersCommon.MixedSecondInterpolationComparison
public import FourPapersCommon.MixedDisorderParity
public import Targets.Section5SignedInitialOffDiagonal

@[expose] public section

/-! The genuine conditioned initial mixed interpolation with arbitrary pair
fields. The original frozen positively shared field remains separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem clock_mem_initial_interval (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    {v : ℝ} (hv : v∈Icc (0:ℝ) (s.q 1)) :
    ξ.clock v∈Icc (0:ℝ) ((mixedClockScheme ξ s).q 1) := by
  have hv' : v∈Icc (s.q (1-1)) (s.q 1) := by simpa only [Nat.sub_self,s.q_zero] using hv
  simpa only [Nat.sub_self,(mixedClockScheme ξ s).q_zero] using
    clock_mem_left_interval ξ s (r:=1) (by omega) hv'

private theorem offdiag_conditioned_sqrt_time_derivative_mul {t w : ℝ}
    (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

noncomputable def mixedConditionedInitialInterpolationOffDiagonal
    (n : ℕ) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (Z : Ω → EnergySpace n)
    (t u v : ℝ) (x y : Fin n → ℝ) (w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w)
      (k + 2) (constrainedPairFieldBase n (Real.sqrt (w * t) • Z ω) u)
      (k + 3) x y ∂ℙ

theorem continuousOn_mixedConditionedInitialInterpolationOffDiagonal
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) {t u v : ℝ} (ht : t ∈ Icc 0 1)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 (s.q 1))
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    ContinuousOn
      (mixedConditionedInitialInterpolationOffDiagonal n ξ s Z t u v x y)
      (Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => by
      unfold section5ConditionedInitialVariance
      split_ifs
      · fun_prop
      · unfold section5InterpolationVariance
        fun_prop)
    (fun j w hw => section5ConditionedInitialVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hv) hw)
    (k + 2) (k + 3) (fun _ => x) (fun _ => y) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

theorem hasDerivAt_mixedConditionedInitialInterpolationOffDiagonal
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (sk : MixedDisorder (Ω := Ω) n ξ) {t u v w : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1)
    (hv : v ∈ Icc 0 (s.q 1)) (hw : w ∈ Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    HasDerivAt
      (mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t u v x y)
      (mixedAveragedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) ξ u t
        (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w)
        (fun j => -(t * (ξ.first (section5Rho s 1 v (k + 2 - j + 1)) -
          ξ.first (section5Rho s 1 v (k + 2 - j)))))
        (k + 2) (k + 3) x y) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace sk.hU
    (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega)) (k + 2) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => hasDerivAt_section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w)
    (show ∀ᶠ z in 𝓝 w, ∀ j,
      0 ≤ section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5ConditionedInitialVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hv)
        ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w ∨
      (section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) =ᶠ[𝓝 w]
        fun _ => 0) from by
      intro j hj
      rcases section5ConditionedInitialVariance_pos_or_eq_zero (mixedClockScheme ξ s) (mixedBeta ξ)
        (p := k + 2 - j) (by omega) ht (clock_mem_initial_interval ξ s hv) hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz)) x y
  apply (H.const_mul (1 / (n : ℝ))).congr_deriv
  rw [offdiag_conditioned_sqrt_time_derivative_mul ht.1 hw.1]
  simpa only [section5Rho_clock,mul_assoc,mixed_first_increment] using!
    normalized_mixed_trace_heat_eq_replica hn ξ t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w)
    (fun j => -(t * (mixedBeta ξ)^2*(section5Rho (mixedClockScheme ξ s) 1 (ξ.clock v) (k+2-j+1)-
      section5Rho (mixedClockScheme ξ s) 1 (ξ.clock v) (k+2-j))))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => section5ConditionedInitialVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hv)
      ⟨hw.1.le, hw.2.le⟩)
    (k + 2) (k + 3)
    (fun l _ hz => section5ConditionedInitialVelocity_zero_of_not_pos
      (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hv) hw.2 hz) x y

theorem deriv_mixedConditionedInitialInterpolationOffDiagonal_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (sk : MixedDisorder (Ω := Ω) n ξ) {t u v w : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1)
    (hv : v ∈ Icc 0 (s.q 1)) (hw : w ∈ Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    deriv (mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t u v x y) w ≤
      -t * (2 * mixedSchemeCorrection ξ s) + t*ξ.tangentRemainder u v := by
  rw [(hasDerivAt_mixedConditionedInitialInterpolationOffDiagonal
    hn ξ s sk ht hu hv hw x y).deriv]
  have H := mixedAveragedReplicaPressureDerivative_le_mismatch hn
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) ξ u v ht.1
    (section5Mass s 1 0) (section5Rho s 1 v)
    (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w)
    1 (k + 2)
    (section5Mass_endpoints s (by omega) (by omega) 0).1
    (section5Mass_endpoints s (by omega) (by omega) 0).2
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => section5ConditionedInitialVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hv)
      ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s (by omega)
      (show (0 : ℝ) ∈ Icc (s.m (1 - 1) / 2) (s.m 1) from by
        simp only [Nat.sub_self, s.m_zero, zero_div, mem_Icc, le_refl, true_and]
        exact s.m_nonneg (by omega)) (by omega))
    (section5Rho_endpoints s (by omega) (by omega) v).1
    (section5Rho_endpoints s (by omega) (by omega) v).2
    (by omega) (by simp [section5Rho])
    (fun p hp=>section5Rho_mem_unit s (by omega)
      ⟨hv.1,hv.2.trans (s.q_le_one (by omega))⟩ hp) x y
  rw [mixedLeftPairCorrection_eq ξ s v 0 (by omega) (by omega)] at H
  simpa only [show k + 2 + 1 - 1 = k + 2 by omega,
    show k + 2 + 1 = k + 3 by omega, Nat.sub_self, s.m_zero,
    sub_self, zero_mul, add_zero] using! H

theorem mixedConditionedInitialInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (sk : MixedDisorder (Ω := Ω) n ξ) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 (s.q 1))
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t u v x y 1 ≤
      mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t u v x y 0 -
        t * (2 * mixedSchemeCorrection ξ s) + t*ξ.tangentRemainder u v := by
  have hc := continuousOn_mixedConditionedInitialInterpolationOffDiagonal
    ξ s sk.hU ht hu hv x y
  have hd : DifferentiableOn ℝ
      (mixedConditionedInitialInterpolationOffDiagonal n ξ s sk.U t u v x y)
      (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro w hw
    exact (hasDerivAt_mixedConditionedInitialInterpolationOffDiagonal
      hn ξ s sk ht hu hv hw x y).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Icc (0 : ℝ) 1),
      deriv (mixedConditionedInitialInterpolationOffDiagonal
        n ξ s sk.U t u v x y) w ≤
        -t * (2 * mixedSchemeCorrection ξ s) +
          t*ξ.tangentRemainder u v := by
    rw [interior_Icc]
    exact fun w hw => deriv_mixedConditionedInitialInterpolationOffDiagonal_le
      hn ξ s sk ht hu hv hw x y
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  simp only [sub_zero, mul_one] at H
  linarith

theorem integrable_mixedConditionedInitialInterpolationOffDiagonal_frozen
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) {t u v w : ℝ} (ht : t ∈ Icc 0 1)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 (s.q 1)) (hw : w ∈ Icc 0 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    Integrable (fun z => mixedConditionedInitialInterpolationOffDiagonal
      n ξ s Z t u v
      (fun i => h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2 * (mixedClockScheme ξ s).q 1)) * z i)
      (fun i => -(h + Real.sqrt ((1 - t) * ((mixedBeta ξ)^2 * (mixedClockScheme ξ s).q 1)) * z i)) w)
      (piGauss n) := by
  exact (integrable_constrainedPairFieldCascade_frozen_pair hZ (Real.sqrt (w * t))
    ((1 - t) * ((mixedBeta ξ)^2 * (mixedClockScheme ξ s).q 1)) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) (k + 2 - j) w)
    (fun _ => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun _ => section5ConditionedInitialVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) (by omega) ht (clock_mem_initial_interval ξ s hv) hw)
    (k + 2) (k + 3) (fun _ => h)).integral_prod_right.const_mul (1 / (n : ℝ))


end FourPapersCommon
