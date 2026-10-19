module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw

@[expose] public section

/-! Genuine independent Gaussian block laws. A finite standard Gaussian on
product coordinates becomes the product of standard Gaussians on its blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
variable {J I : Type*} [Fintype J] [Fintype I]

def gaussianBlockCurry (z : EuclideanSpace ℝ (J×I)) : J → EuclideanSpace ℝ I :=
  fun j => WithLp.toLp 2 (fun i => z (j,i))

theorem measurable_gaussianBlockCurry : Measurable (gaussianBlockCurry (J:=J) (I:=I)) := by
  apply Measurable.of_eval
  intro j
  exact (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).measurable.comp
    (Measurable.of_eval (fun i =>
      (EuclideanSpace.proj (j,i) : EuclideanSpace ℝ (J×I) →L[ℝ] ℝ).measurable))

theorem stdGaussian_map_gaussianBlockCurry :
    (stdGaussian (EuclideanSpace ℝ (J×I))).map gaussianBlockCurry =
      Measure.pi (fun _ : J => stdGaussian (EuclideanSpace ℝ I)) := by
  have hc : (Measure.pi (fun _ : J×I => gaussianReal 0 1)).map
      (MeasurableEquiv.curry J I ℝ) =
        Measure.pi (fun _ : J => Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun (_ : J) (_ : I) => gaussianReal 0 1)
  rw [←map_pi_eq_stdGaussian]
  rw [Measure.map_map measurable_gaussianBlockCurry (by fun_prop)]
  have he : gaussianBlockCurry ∘ WithLp.toLp 2 =
      (fun z : J → I → ℝ => fun j => WithLp.toLp 2 (z j)) ∘
        (MeasurableEquiv.curry J I ℝ) := rfl
  rw [he,←Measure.map_map (by fun_prop) (MeasurableEquiv.curry J I ℝ).measurable,hc,
    Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (WithLp.toLp 2 : (I→ℝ)→EuclideanSpace ℝ I)).aemeasurable)]
  simp only [map_pi_eq_stdGaussian]

theorem hasLaw_gaussianBlockCurry :
    HasLaw (gaussianBlockCurry (J:=J) (I:=I))
      (Measure.pi (fun _ : J => stdGaussian (EuclideanSpace ℝ I)))
      (stdGaussian (EuclideanSpace ℝ (J×I))) :=
  ⟨measurable_gaussianBlockCurry.aemeasurable,stdGaussian_map_gaussianBlockCurry⟩

end FourPapersCommon
