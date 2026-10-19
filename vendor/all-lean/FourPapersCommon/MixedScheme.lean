module
public import FourPapersCommon.MixedModel
public import Paper.ParisiPDEFormula
public import FourPapersCommon.MixtureConvexity
public import FourPapersCommon.WeightedCDF

@[expose] public section

/-! Genuine physical-overlap RSB schemes transported by the covariance clock. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon

def mixedClockScheme (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) : RSBScheme k where
  m := s.m
  q := fun p => ξ.clock (s.q p)
  m_zero := s.m_zero
  m_top := s.m_top
  m_mono := s.m_mono
  q_zero := by rw [s.q_zero, ξ.clock_zero]
  q_top := by rw [s.q_top, ξ.clock_one]
  q_mono := by
    intro p hp
    exact ξ.clock_strictMonoOn.monotoneOn
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩ (s.q_mono p hp)

@[simp] theorem mixedClockScheme_m (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) (p : ℕ) :
    (mixedClockScheme ξ s).m p = s.m p := rfl

@[simp] theorem mixedClockScheme_q (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) (p : ℕ) :
    (mixedClockScheme ξ s).q p = ξ.clock (s.q p) := rfl

theorem mixedClockScheme_variance (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (p : ℕ) :
    mixedBeta ξ ^ 2 * ((mixedClockScheme ξ s).q (p + 1) - (mixedClockScheme ξ s).q p) =
      ξ.first (s.q (p + 1)) - ξ.first (s.q p) := by
  rw [mixedClockScheme_q, mixedClockScheme_q, mixedBeta_sq]
  unfold AdmissibleEvenMixture.clock
  field_simp [ξ.variance_pos.ne']

@[simp] theorem parisiSchemeAtom_clock (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (i : Fin (k + 1)) :
    ξ.unitClock (Paper.parisiSchemeAtom s i) = Paper.parisiSchemeAtom (mixedClockScheme ξ s) i := by
  rfl

theorem mixedMeasure_scheme (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) :
    mixedMeasure ξ (Paper.parisiSchemeMeasure s) =
      Paper.parisiSchemeMeasure (mixedClockScheme ξ s) := by
  apply Subtype.ext
  change Measure.map ξ.unitClock (Paper.parisiSchemeRawMeasure s) =
    Paper.parisiSchemeRawMeasure (mixedClockScheme ξ s)
  unfold Paper.parisiSchemeRawMeasure
  rw [Measure.map_finset_sum' ξ.continuous_unitClock.measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_smul, Measure.map_dirac' ξ.continuous_unitClock.measurable]
  · rfl
  · exact ξ.continuous_unitClock.measurable.aemeasurable

theorem mixedPotential_scheme_initial (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) :
    mixedPotential ξ (Paper.parisiSchemeMeasure s) (0, h) =
      parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h := by
  unfold mixedPotential
  simp only [ξ.clock_zero, mixedMeasure_scheme]
  rw [Paper.parisiSchemePotential_eq_actual _ _ (mixedBeta_ne_zero ξ) 0 h (by norm_num),
    Paper.parisiFinitePotential_initial]

theorem mixedScheme_correction_integral (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) :
    (∫ q in (0 : ℝ)..1, q * ξ.second q * Paper.parisiCDF (Paper.parisiSchemeMeasure s) q) =
      ∑ i : Fin (k + 1), (s.m (i + 1) - s.m i) *
        (ξ.correction 1 - ξ.correction (s.q (i + 1))) := by
  change weightedCDFIntegral (fun q => q * ξ.second q) (Paper.parisiSchemeMeasure s) = _
  have hc : ContinuousOn (fun q => q * ξ.second q) (Icc (0 : ℝ) 1) :=
    continuous_id.continuousOn.mul (ξ.continuousOn_second.mono (by
      intro q hq; exact ⟨by linarith [hq.1], hq.2⟩))
  rw [weightedCDFIntegral_eq_measure_integral _ hc]
  change (∫ q, weightedTail (fun r => r * ξ.second r) q ∂Paper.parisiSchemeRawMeasure s) = _
  rw [Paper.parisiSchemeRawMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (s.m_mono i (by omega)))]
    unfold weightedTail Paper.parisiSchemeAtom
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q hq => ξ.hasDerivAt_correction (by
        have hh : q ∈ Icc (0 : ℝ) 1 := by
          rw [uIcc_of_le (s.q_le_one (p := i + 1) (by omega))] at hq
          exact ⟨(s.q_nonneg (p := i + 1) (by omega)).trans hq.1, hq.2⟩
        rw [abs_of_nonneg hh.1]
        linarith [hh.2]))
      ((hc.mono (by
        intro q hq
        rw [uIcc_of_le (s.q_le_one (p := i + 1) (by omega))] at hq
        exact ⟨(s.q_nonneg (p := i + 1) (by omega)).trans hq.1, hq.2⟩)).intervalIntegrable)
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem mixedScheme_correction_mass_sum (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) :
    (∑ l ∈ Finset.range (k + 2),
      (guerraMass (mixedClockScheme ξ s) l - guerraMass (mixedClockScheme ξ s) (l + 1)) *
        ξ.correction (s.q (k + 2 - l))) =
      ∑ i : Fin (k + 1), (s.m (i + 1) - s.m i) * ξ.correction (s.q (i + 1)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (s.m (i + 1) - s.m i) * ξ.correction (s.q (i + 1)))]
  let f : ℕ → ℝ := fun i => (s.m (i + 1) - s.m i) * ξ.correction (s.q (i + 1))
  calc
    _ = ∑ j ∈ Finset.range (k + 1), f (k - j) := by
      rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
      have hz : guerraMass (mixedClockScheme ξ s) 0 - guerraMass (mixedClockScheme ξ s) 1 = 0 := by
        simp [guerraMass, mixedClockScheme, s.m_top]
      rw [hz, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k := by simp only [Finset.mem_range] at hj; omega
      simp only [guerraMass, mixedClockScheme_m]
      change (s.m (k + 1 - j) - s.m (k + 1 - (j + 1))) *
        ξ.correction (s.q ((k + 1 + 1) - (j + 1))) = _
      have h1 : k + 1 - j = k - j + 1 := by omega
      have h2 : k + 1 - (j + 1) = k - j := by omega
      have h3 : k + 1 + 1 - (j + 1) = k - j + 1 := by omega
      rw [h1, h2, h3]
    _ = _ := by simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect f (k + 1)

def mixedSchemeCorrection (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) : ℝ :=
  (1 / 2) * (ξ.correction 1 - ∑ l ∈ Finset.range (k + 2),
    (guerraMass (mixedClockScheme ξ s) l - guerraMass (mixedClockScheme ξ s) (l + 1)) *
      ξ.correction (s.q (k + 2 - l)))

theorem mixedSchemeCorrection_eq_integral (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) :
    mixedSchemeCorrection ξ s = (1 / 2) *
      (∫ q in (0 : ℝ)..1, q * ξ.second q * Paper.parisiCDF (Paper.parisiSchemeMeasure s) q) := by
  rw [mixedSchemeCorrection, mixedScheme_correction_integral, mixedScheme_correction_mass_sum]
  congr 1
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hm : (∑ i : Fin (k + 1), (s.m (i + 1) - s.m i)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => s.m (i + 1) - s.m i),
      Paper.parisiScheme_mass_telescope, s.m_top, s.m_zero]
    norm_num
  rw [← Finset.sum_mul, hm, one_mul]

theorem mixedFunctional_scheme (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure s) =
      Real.log 2 + parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
        mixedSchemeCorrection ξ s := by
  rw [mixedFunctional, mixedPotential_scheme_initial, mixedSchemeCorrection_eq_integral]

end FourPapersCommon
