module
public import QuantitativePaper.VectorRecursionIntegrability
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

/-! Actual measurable normalized finite-dimensional Gaussian transition kernels.
The parameter is retained in the state, so a subsequent path construction keeps
the same disorder rather than resampling it. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace QuantitativePaper

variable {n : ℕ} {A : Type*} [MeasurableSpace A]

def vectorStateUpdate (c : ℝ) (p : (A × Field n) × Field n) : A × Field n :=
  (p.1.1,fieldShift c p.1.2 p.2)

theorem measurable_vectorStateUpdate (c : ℝ) : Measurable (vectorStateUpdate (A := A) (n := n) c) := by
  unfold vectorStateUpdate fieldShift
  fun_prop

def vectorGaussianStateKernel (c : ℝ) : Kernel (A × Field n) (A × Field n) :=
  (Kernel.id ×ₖ Kernel.const (A × Field n) (fieldGaussian n)).map (vectorStateUpdate c)

instance vectorGaussianStateKernel_markov (c : ℝ) :
    IsMarkovKernel (vectorGaussianStateKernel (A := A) (n := n) c) := by
  exact Kernel.IsMarkovKernel.map _ (measurable_vectorStateUpdate c)

theorem vectorGaussianStateKernel_apply (c : ℝ) (p : A × Field n) :
    vectorGaussianStateKernel c p = (fieldGaussian n).map (fun z => (p.1,fieldShift c p.2 z)) := by
  rw [vectorGaussianStateKernel,Kernel.map_apply _ (measurable_vectorStateUpdate c),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (measurable_vectorStateUpdate c) measurable_prodMk_left]
  rfl

def vectorStateWeight (c m : ℝ) (f : A → Field n → ℝ) (p y : A × Field n) : ℝ :=
  Real.exp (m*f p.1 y.2)/vectorStepPartition c m (f p.1) p.2

theorem measurable_vectorStateWeight (f : A → Field n → ℝ)
    (hf : Measurable (fun p : A × Field n => f p.1 p.2)) (c m : ℝ) :
    Measurable (Function.uncurry (vectorStateWeight c m f)) := by
  have hshift : Measurable (fun p : (A × Field n) × Field n => (p.1.1,fieldShift c p.1.2 p.2)) := by
    unfold fieldShift
    fun_prop
  have hF : Measurable (fun p : (A × Field n) × Field n =>
      Real.exp (m*f p.1.1 (fieldShift c p.1.2 p.2))) :=
    Real.measurable_exp.comp ((measurable_const (a := m)).mul (hf.comp hshift))
  have hZ : Measurable (fun p : A × Field n => vectorStepPartition c m (f p.1) p.2) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable
  have hn : Measurable (fun p : (A × Field n) × (A × Field n) => Real.exp (m*f p.1.1 p.2.2)) := by
    apply Real.measurable_exp.comp
    apply Measurable.mul (measurable_const (a := m))
    exact hf.comp (show Measurable (fun p : (A × Field n) × (A × Field n) => (p.1.1,p.2.2)) from by fun_prop)
  exact hn.div (hZ.comp measurable_fst)

def vectorStateKernel (c m : ℝ) (f : A → Field n → ℝ) : Kernel (A × Field n) (A × Field n) :=
  (vectorGaussianStateKernel c).withDensity (fun p y => ENNReal.ofReal (vectorStateWeight c m f p y))

theorem vectorStateKernel_apply (f : A → Field n → ℝ)
    (hf : Measurable (fun p : A × Field n => f p.1 p.2)) (c m : ℝ) (p : A × Field n) :
    vectorStateKernel c m f p = (vectorGaussianStateKernel c p).withDensity
      (fun y => ENNReal.ofReal (vectorStateWeight c m f p y)) :=
  Kernel.withDensity_apply _ (measurable_vectorStateWeight f hf c m).ennreal_ofReal p

theorem integrable_vectorStateWeight (f : A → Field n → ℝ) (K : ℝ≥0)
    (hfl : ∀ a,LipschitzWith K (f a)) (c m : ℝ) (p : A × Field n) :
    Integrable (vectorStateWeight c m f p) (vectorGaussianStateKernel c p) := by
  rw [vectorGaussianStateKernel_apply]
  apply (integrable_map_measure (by
    unfold vectorStateWeight
    exact (Real.measurable_exp.comp ((measurable_const (a := m)).mul
      ((hfl p.1).continuous.measurable.comp measurable_snd))).div_const _ |>.aestronglyMeasurable)
    (by unfold fieldShift;fun_prop)).mpr
  exact integrable_vectorStepWeight (f p.1) K (hfl p.1) c m p.2

theorem integral_vectorStateWeight (f : A → Field n → ℝ) (K : ℝ≥0)
    (hfl : ∀ a,LipschitzWith K (f a)) (c m : ℝ) (p : A × Field n) :
    (∫ y,vectorStateWeight c m f p y ∂vectorGaussianStateKernel c p) = 1 := by
  rw [vectorGaussianStateKernel_apply,integral_map (by unfold fieldShift;fun_prop)
    (by unfold vectorStateWeight;exact (Real.measurable_exp.comp ((measurable_const (a := m)).mul
      ((hfl p.1).continuous.measurable.comp measurable_snd))).div_const _ |>.aestronglyMeasurable)]
  exact integral_vectorStepWeight (f p.1) K (hfl p.1) c m p.2

theorem isMarkovKernel_vectorStateKernel (f : A → Field n → ℝ)
    (hf : Measurable (fun p : A × Field n => f p.1 p.2)) (K : ℝ≥0)
    (hfl : ∀ a,LipschitzWith K (f a)) (c m : ℝ) :
    IsMarkovKernel (vectorStateKernel c m f) := by
  constructor
  intro p
  constructor
  rw [vectorStateKernel_apply f hf c m p,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_vectorStateWeight f K hfl c m p)
      (Eventually.of_forall fun y => div_nonneg (Real.exp_pos _).le
        (vectorStepPartition_pos (f p.1) K (hfl p.1) c m p.2).le),
    integral_vectorStateWeight f K hfl c m p]
  norm_num

end QuantitativePaper
