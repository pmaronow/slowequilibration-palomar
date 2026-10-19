module
public import FourPapersCommon.SignedColeHopfDatum
public import QuantitativePaper.SmoothGaussianStep

@[expose] public section

/-! The scalar logarithmic Gaussian heat operation is exactly a one-coordinate
instance of the actual finite-dimensional Gaussian operation, including mass zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace FourPapersCommon
open QuantitativePaper ColeHopfFoundation.ProbabilityTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def scalarGaussianShift (v : E) : Field 1 →L[ℝ] E :=
  (EuclideanSpace.proj (0 : Fin 1)).smulRight v

@[simp] theorem scalarGaussianShift_apply (v : E) (z : Field 1) :
    scalarGaussianShift v z=z 0 • v := rfl

theorem hasLaw_field_one_coordinate :
    HasLaw (fun z : Field 1=>z 0) (gaussianReal 0 1) (fieldGaussian 1) := by
  have hm : Measurable (fun z : Field 1=>z 0) := (EuclideanSpace.proj (0:Fin 1) : Field 1 →L[ℝ] ℝ).measurable
  refine ⟨hm.aemeasurable,?_⟩
  unfold fieldGaussian SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map hm (WithLp.measurable_toLp 2 _)]
  exact (measurePreserving_eval (μ:=fun _ : Fin 1=>gaussianReal 0 1) (0:Fin 1)).map_eq

theorem integral_field_one_coordinate (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z : Field 1,f (z 0) ∂fieldGaussian 1)=∫ y,f y ∂gaussianReal 0 1 := by
  exact hasLaw_field_one_coordinate.integral_comp hf.aestronglyMeasurable

theorem coleHopf_eq_gaussianShiftColeHopf (f : E → ℝ) (hf : Continuous f)
    (v x : E) (m : ℝ) :
    coleHopf m 1 (fun y=>f (x+y • v)) 0=
      gaussianShiftColeHopf (scalarGaussianShift v) m f x := by
  have h0 := integral_field_one_coordinate (fun y=>f (x+y • v))
    (hf.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have he := integral_field_one_coordinate (fun y=>Real.exp (m*f (x+y • v)))
    (Real.continuous_exp.comp
      ((hf.comp (continuous_const.add (continuous_id.smul continuous_const))).const_mul m))
  unfold coleHopf gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
  simp only [zero_add,scalarGaussianShift_apply]
  split_ifs <;> simp only [h0,he,one_div,div_eq_mul_inv,mul_comm,mul_one]

end FourPapersCommon
