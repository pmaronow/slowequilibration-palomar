module
public import QuantitativePaper.VectorPosterior
public import QuantitativeFollowup.FinitePosteriorNormalization
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-! Actual fixed-spin posterior probability slices of the normalized vector
law. Their finite positive partition integrals are derived from the genuine
joint law, not supplied as normalization assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

 theorem measurable_vectorPosteriorWeight {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measurable (fun p : VectorGaussianSpace n k × Configuration n =>
      Real.exp (-vectorPosteriorPotential s β t a p.2 p.1)) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (Real.continuous_exp.comp (contDiff_vectorPosteriorPotential s β t a σ).continuous.neg).measurable

 theorem lintegral_vectorPosteriorWeight_sum {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) :
    (∑ σ : Configuration n, ∫⁻x,ENNReal.ofReal (Real.exp (-vectorPosteriorPotential s β t a σ x))) = 1 := by
  have hm := (measurable_vectorPosteriorWeight (n := n) s β t a).ennreal_ofReal
  have hp := vectorEuclideanJointLaw_probability (n := n) s β t a
  have hh := hp.measure_univ
  rw [vectorEuclideanJointLaw_eq_Lebesgue_posterior s β t a hq,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_prod_symm' _ hm,lintegral_count,tsum_fintype] at hh
  exact hh

 theorem integrable_vectorPosteriorWeight {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (σ : Configuration n) :
    Integrable (fun x => Real.exp (-vectorPosteriorPotential s β t a σ x)) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (Real.continuous_exp.comp (contDiff_vectorPosteriorPotential s β t a σ).continuous.neg).aestronglyMeasurable
    (.of_forall fun x => (Real.exp_pos _).le)).mp
  have hs := lintegral_vectorPosteriorWeight_sum (n := n) s β t a hq
  have hb := Finset.single_le_sum (s := (Finset.univ : Finset (Configuration n)))
    (f := fun σ => ∫⁻x,ENNReal.ofReal (Real.exp (-vectorPosteriorPotential s β t a σ x)))
    (fun σ _ => bot_le) (Finset.mem_univ σ)
  rw [hs] at hb
  exact ne_of_lt (hb.trans_lt ENNReal.one_lt_top)

 def vectorSpinPosteriorMass {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (σ : Configuration n) : ℝ :=
  QuantitativeFollowup.posteriorNormalizer (vectorPosteriorPotential s β t a σ)

 def vectorSpinPosteriorLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (σ : Configuration n) : Measure (VectorGaussianSpace n k) :=
  QuantitativeFollowup.normalizedPosteriorMeasure (vectorPosteriorPotential s β t a σ)

 theorem vectorSpinPosteriorMass_pos {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (hq : s.q 1=0) (σ : Configuration n) : 0 < vectorSpinPosteriorMass s β t a σ :=
  QuantitativeFollowup.posteriorNormalizer_pos_finite _ (integrable_vectorPosteriorWeight s β t a hq σ)

 theorem vectorSpinPosteriorLaw_probability {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (hq : s.q 1=0) (σ : Configuration n) :
    IsProbabilityMeasure (vectorSpinPosteriorLaw s β t a σ) :=
  QuantitativeFollowup.normalizedPosteriorMeasure_probability_finite _
    (integrable_vectorPosteriorWeight s β t a hq σ)

 theorem vectorSpinPosteriorMass_sum {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (hq : s.q 1=0) : (∑σ : Configuration n,vectorSpinPosteriorMass s β t a σ) = 1 := by
  have hs := lintegral_vectorPosteriorWeight_sum (n := n) s β t a hq
  have he (σ : Configuration n) : ENNReal.ofReal (vectorSpinPosteriorMass s β t a σ) =
      ∫⁻x,ENNReal.ofReal (Real.exp (-vectorPosteriorPotential s β t a σ x)) :=
    ofReal_integral_eq_lintegral_ofReal (integrable_vectorPosteriorWeight s β t a hq σ)
      (.of_forall fun x => (Real.exp_pos _).le)
  have hn (σ : Configuration n) : 0 ≤ vectorSpinPosteriorMass s β t a σ :=
    (vectorSpinPosteriorMass_pos s β t a hq σ).le
  apply (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun σ _ => hn σ) zero_le_one).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ => hn σ)]
  simpa only [he,ENNReal.ofReal_one] using hs

/-- The raw spin slice is exactly its actual mass times its normalized probability. -/
theorem posteriorDensityMeasure_vector_eq_mass_smul {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (σ : Configuration n) :
    QuantitativeFollowup.posteriorDensityMeasure (vectorPosteriorPotential s β t a σ) =
      ENNReal.ofReal (vectorSpinPosteriorMass s β t a σ) • vectorSpinPosteriorLaw s β t a σ := by
  let V := vectorPosteriorPotential (n := n) s β t a σ
  have hZ : 0 < QuantitativeFollowup.posteriorNormalizer V := vectorSpinPosteriorMass_pos s β t a hq σ
  change (volume : Measure (VectorGaussianSpace n k)).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) =
    ENNReal.ofReal (QuantitativeFollowup.posteriorNormalizer V) •
      (volume : Measure (VectorGaussianSpace n k)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-QuantitativeFollowup.normalizedPosteriorPotential V x)))
  rw [←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  exact .of_forall fun x => by
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [QuantitativeFollowup.exp_neg_normalizedPosteriorPotential V hZ,
      ←ENNReal.ofReal_mul hZ.le]
    congr 1
    field_simp

/-- The actual joint law is the finite mixture of its normalized spin slices. -/
theorem vectorEuclideanJointLaw_eq_spin_mixture {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) :
    vectorEuclideanJointLaw (n := n) s β t a=
      ∑σ : Configuration n,ENNReal.ofReal (vectorSpinPosteriorMass s β t a σ) •
        (vectorSpinPosteriorLaw s β t a σ).map (fun z => (z,σ)) := by
  rw [vectorEuclideanJointLaw_eq_Lebesgue_posterior s β t a hq,
    Measure.count,Measure.prod_sum_right,withDensity_sum,Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Measure.prod_dirac]
  have hm := FourPapersCommon.map_withDensity_pullback
    (volume : Measure (VectorGaussianSpace n k)) (fun z => (z,σ)) measurable_prodMk_right
    (fun p => ENNReal.ofReal (Real.exp (-vectorPosteriorPotential s β t a p.2 p.1)))
    (measurable_vectorPosteriorWeight s β t a).ennreal_ofReal
  rw [←hm]
  change (QuantitativeFollowup.posteriorDensityMeasure
    (vectorPosteriorPotential s β t a σ)).map (fun z => (z,σ))=_
  rw [posteriorDensityMeasure_vector_eq_mass_smul s β t a hq σ,
    Measure.map_smul _ measurable_prodMk_right.aemeasurable]

end QuantitativePaper
