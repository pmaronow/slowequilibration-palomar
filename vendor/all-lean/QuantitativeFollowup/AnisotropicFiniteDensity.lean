module
public import QuantitativeFollowup.AnisotropicFiniteLaw
public import FourPapersCommon.FiniteHistoryDensity
public import QuantitativePaper.HistoryDensityExponential

@[expose] public section

/-! Exact normalized anisotropic Gaussian-history density. The initial
disorder tilt and every Gaussian transition weight are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def anisotropicFiniteOuterPartition (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) : ℝ :=
  ∫ ω,Real.exp (a*anisotropicFiniteFieldPotential D s (k+2) ω 0) ∂anisotropicDisorderLaw n

theorem anisotropicFiniteOuterPartition_pos (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : 0 < anisotropicFiniteOuterPartition D s a :=
  integral_exp_pos (integrable_exp_anisotropicFinitePotential D s (k+2) a)

def anisotropicFiniteBaseInitialLaw (n : ℕ) : Measure (AnisotropicParameter n) :=
  (anisotropicDisorderLaw n).map (anisotropicDisorderInjection n)

instance anisotropicFiniteBaseInitialLaw_probability (n : ℕ) :
    IsProbabilityMeasure (anisotropicFiniteBaseInitialLaw n) := by
  unfold anisotropicFiniteBaseInitialLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (anisotropicDisorderInjection n).continuous.measurable.aemeasurable).mpr inferInstance

def anisotropicFiniteInitialWeight (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (P : AnisotropicParameter n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a*anisotropicFinitePotential D s (k+2) P)/
    anisotropicFiniteOuterPartition D s a)

theorem measurable_anisotropicFiniteInitialWeight (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : Measurable (anisotropicFiniteInitialWeight D s a) :=
  (((contDiff_one_anisotropicFinitePotential D s (k+2)).continuous.measurable.const_mul a).exp.div_const _).ennreal_ofReal

theorem anisotropicFiniteInitialLaw_eq_withDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : anisotropicFiniteInitialLaw D s a =
      (anisotropicFiniteBaseInitialLaw n).withDensity (anisotropicFiniteInitialWeight D s a) := by
  unfold anisotropicFiniteInitialLaw anisotropicFiniteOuterLaw
  rw [Measure.tilted]
  exact map_withDensity_pullback (anisotropicDisorderLaw n) (anisotropicDisorderInjection n)
    (anisotropicDisorderInjection n).continuous.measurable
    (anisotropicFiniteInitialWeight D s a) (measurable_anisotropicFiniteInitialWeight D s a)

def anisotropicFiniteBaseTransition (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : ℕ) :
    Kernel (AnisotropicParameter n) (AnisotropicParameter n) :=
  finiteStateGaussianRawKernel (anisotropicSchemeInput D s (k+1-i))

instance anisotropicFiniteBaseTransition_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : IsMarkovKernel (anisotropicFiniteBaseTransition D s i) := by
  unfold anisotropicFiniteBaseTransition
  infer_instance

def anisotropicFiniteTransitionWeight (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (P Q : AnisotropicParameter n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (anisotropicSchemeMass s (k+1-i)*anisotropicFinitePotential D s (k+1-i) Q)/
    finiteStateGaussianNormalizer (anisotropicSchemeMass s (k+1-i))
      (anisotropicSchemeInput D s (k+1-i)) (anisotropicFinitePotential D s (k+1-i)) P)

theorem measurable_anisotropicFiniteTransitionWeight (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) :
    Measurable (Function.uncurry (anisotropicFiniteTransitionWeight D s i)) := by
  have hU := (contDiff_one_anisotropicFinitePotential D s (k+1-i)).continuous.measurable
  have hN : Measurable (finiteStateGaussianNormalizer (anisotropicSchemeMass s (k+1-i))
      (anisotropicSchemeInput D s (k+1-i)) (anisotropicFinitePotential D s (k+1-i))) :=
    ((hU.const_mul _).exp.stronglyMeasurable.integral_kernel).measurable
  exact (((hU.comp measurable_snd).const_mul _).exp.div (hN.comp measurable_fst)).ennreal_ofReal

theorem anisotropicFiniteTransition_eq_withDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : anisotropicFiniteTransition D s i =
      (anisotropicFiniteBaseTransition D s i).withDensity (anisotropicFiniteTransitionWeight D s i) := rfl

theorem anisotropicFiniteNormalizer_eq_exp (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    finiteStateGaussianNormalizer (anisotropicSchemeMass s j) (anisotropicSchemeInput D s j)
      (anisotropicFinitePotential D s j) P =
        Real.exp (anisotropicSchemeMass s j*anisotropicFinitePotential D s (j+1) P) := by
  unfold finiteStateGaussianNormalizer
  rw [finiteStateGaussianRawKernel_apply,integral_map (by fun_prop)
    (((contDiff_one_anisotropicFinitePotential D s j).continuous.measurable.const_mul _).exp.aestronglyMeasurable),
    anisotropicFinitePotential_coleHopf]
  by_cases ha : anisotropicSchemeMass s j = 0
  · simp [ha]
  · have hp := integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz
      (anisotropicFinitePotential D s j) (anisotropicFinitePotential_lipschitz D s j)
      (anisotropicSchemeInput D s j) P (anisotropicSchemeMass s j))
    simp only [OverlapPaper.sourceLogAverage,ha,ite_false]
    rw [mul_div_cancel₀ _ ha,Real.exp_log hp]

theorem anisotropicFiniteTransitionWeight_eq_exp (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i ≤ k+1) (P Q : AnisotropicParameter n) :
    anisotropicFiniteTransitionWeight D s i P Q = ENNReal.ofReal
      (Real.exp (s.m i*(anisotropicFinitePotential D s (k+1-i) Q-
        anisotropicFinitePotential D s (k+2-i) P))) := by
  rw [anisotropicFiniteTransitionWeight,anisotropicFiniteNormalizer_eq_exp]
  have hj : k+1-(k+1-i) = i := by omega
  have hd : (k+1-i)+1 = k+2-i := by omega
  rw [anisotropicSchemeMass,hj,hd,←Real.exp_sub]
  congr 2
  ring

def anisotropicFiniteBaseHistoryLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    Measure (FiniteHistory (AnisotropicParameter n) (k+2)) :=
  finiteHistoryLaw (anisotropicFiniteBaseInitialLaw n) (anisotropicFiniteBaseTransition D s) (k+2)

instance anisotropicFiniteBaseHistoryLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : IsProbabilityMeasure (anisotropicFiniteBaseHistoryLaw D s) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (fun _ => inferInstance) _

def anisotropicFiniteHistoryDensity (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (p : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ≥0∞ :=
  anisotropicFiniteInitialWeight D s a (p 0)*
    finiteHistoryDensity (anisotropicFiniteTransitionWeight D s) (k+2) p

theorem measurable_anisotropicFiniteHistoryDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : Measurable (anisotropicFiniteHistoryDensity D s a) :=
  ((measurable_anisotropicFiniteInitialWeight D s a).comp (measurable_pi_apply (0 : Fin (k+3)))).mul
    (measurable_finiteHistoryDensity _ (measurable_anisotropicFiniteTransitionWeight D s) _)

theorem anisotropicFiniteHistoryLaw_eq_withDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : anisotropicFiniteHistoryLaw D s a =
      (anisotropicFiniteBaseHistoryLaw D s).withDensity (anisotropicFiniteHistoryDensity D s a) :=
  finiteHistoryLaw_withDensity_initial_and_transitions _ _ _ _
    (fun _ => inferInstance) (fun _ => inferInstance)
    _ (measurable_anisotropicFiniteInitialWeight D s a) (anisotropicFiniteInitialLaw_eq_withDensity D s a)
    _ (measurable_anisotropicFiniteTransitionWeight D s) (anisotropicFiniteTransition_eq_withDensity D s) _

end QuantitativeFollowup
