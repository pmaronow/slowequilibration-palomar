module
public import QuantitativeFollowup.AnisotropicFiniteCascade
public import FourPapersCommon.FiniteHistory

@[expose] public section

/-! Honest anisotropic finite-profile disorder, field-history and terminal
spin probability laws. Normalization follows from the actual Gaussian
Hopf--Cole recursion and Gaussian exponential integrability. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def anisotropicDisorderInjection (n : ℕ) : AnisotropicDisorder n→L[ℝ]AnisotropicParameter n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun z=>WithLp.toLp 2 (Sum.elim (fun i=>z i) (fun _=>0))
      map_add':=by intro x y;ext i;cases i <;> simp
      map_smul':=by intro c x;ext i;cases i <;> simp }

@[simp] theorem anisotropicDisorderInjection_apply (ω : AnisotropicDisorder n) :
    anisotropicDisorderInjection n ω=anisotropicParameterPoint ω 0 := rfl

theorem integrable_exp_anisotropicFinitePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (a : ℝ) :
    Integrable (fun ω=>Real.exp (a*anisotropicFiniteFieldPotential D s j ω 0))
      (anisotropicDisorderLaw n) := by
  have hi:=integrable_exp_finiteStateGaussian_lipschitz (anisotropicFinitePotential D s j)
    (anisotropicFinitePotential_lipschitz D s j) (anisotropicDisorderInjection n)
    (0 : AnisotropicParameter n) a
  simpa only [zero_add,anisotropicDisorderInjection_apply,anisotropicFiniteFieldPotential,
    anisotropicDisorderLaw] using hi

def anisotropicFiniteOuterLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (AnisotropicDisorder n) :=
  (anisotropicDisorderLaw n).tilted (fun ω=>a*anisotropicFiniteFieldPotential D s (k+2) ω 0)

instance anisotropicFiniteOuterLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicFiniteOuterLaw D s a) :=
  isProbabilityMeasure_tilted (integrable_exp_anisotropicFinitePotential D s (k+2) a)

def anisotropicFiniteInitialLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (AnisotropicParameter n) :=
  (anisotropicFiniteOuterLaw D s a).map (anisotropicDisorderInjection n)

instance anisotropicFiniteInitialLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicFiniteInitialLaw D s a) := by
  unfold anisotropicFiniteInitialLaw
  exact (Measure.isProbabilityMeasure_map_iff (anisotropicDisorderInjection n).continuous.measurable.aemeasurable).mpr inferInstance

/-- Forward chronological transition from q_i to q_(i+1). The potential
index runs backward, so repeated levels produce the genuine zero-noise step. -/
def anisotropicFiniteTransition (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : ℕ) :
    Kernel (AnisotropicParameter n) (AnisotropicParameter n) :=
  finiteStateGaussianStepKernel (anisotropicSchemeMass s (k+1-i))
    (anisotropicSchemeInput D s (k+1-i)) (anisotropicFinitePotential D s (k+1-i))

instance anisotropicFiniteTransition_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : IsMarkovKernel (anisotropicFiniteTransition D s i) :=
  isMarkovKernel_finiteStateGaussianStepKernel _ _ _ (anisotropicFinitePotential_lipschitz D s (k+1-i))

theorem anisotropicFiniteTransition_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (P : AnisotropicParameter n) :
    anisotropicFiniteTransition D s i P=
      ((stdGaussian (Field n)).tilted (fun z=>anisotropicSchemeMass s (k+1-i)*
        anisotropicFinitePotential D s (k+1-i) (P+anisotropicSchemeInput D s (k+1-i) z))).map
          (fun z=>P+anisotropicSchemeInput D s (k+1-i) z) := by
  rw [anisotropicFiniteTransition,finiteStateGaussianStepKernel_apply _ _ _
    (contDiff_one_anisotropicFinitePotential D s (k+1-i)).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _
      (contDiff_one_anisotropicFinitePotential D s (k+1-i)).continuous.measurable]

def anisotropicFiniteHistoryLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (FiniteHistory (AnisotropicParameter n) (k+2)) :=
  finiteHistoryLaw (anisotropicFiniteInitialLaw D s a) (anisotropicFiniteTransition D s) (k+2)

instance anisotropicFiniteHistoryLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicFiniteHistoryLaw D s a) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (fun _=>inferInstance) _

def anisotropicFiniteTerminalKernel (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    Kernel (FiniteHistory (AnisotropicParameter n) (k+2)) (Configuration n) :=
  (anisotropicFiniteSpinKernel D s 0).comap (fun h=>h (Fin.last (k+2))) (measurable_pi_apply _)

instance anisotropicFiniteTerminalKernel_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : IsMarkovKernel (anisotropicFiniteTerminalKernel D s) := by
  unfold anisotropicFiniteTerminalKernel
  infer_instance

def anisotropicFiniteJointLaw (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) :
    Measure (FiniteHistory (AnisotropicParameter n) (k+2)×Configuration n) :=
  (anisotropicFiniteHistoryLaw D s a) ⊗ₘ (anisotropicFiniteTerminalKernel D s)

instance anisotropicFiniteJointLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : IsProbabilityMeasure (anisotropicFiniteJointLaw D s a) := by
  unfold anisotropicFiniteJointLaw
  infer_instance

end QuantitativeFollowup
