-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteModel
public import SlowEquilibration.GaussianSharpAbsoluteMaximum

/-! Literal finite blocks of the original countable tensor disorder have their
full standard Gaussian coordinate law, including all original coordinates. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ]

abbrev SelectedCoordinate (N : ℕ) (p : σ → ℕ) :=
  (i : σ) × SphericalAging.FiniteModel.TensorIndex N (p i+2)

def finiteCoordinates {N : ℕ} (p : σ → ℕ) (J : Disorder N) :
    EuclideanSpace ℝ (SelectedCoordinate N p) := WithLp.toLp 2 (fun I => J (p I.1) I.2)

theorem finiteCoordinates_measurable {N : ℕ} (p : σ → ℕ) :
    Measurable (finiteCoordinates (N := N) p) := by
  unfold finiteCoordinates
  fun_prop

/-- No tensor coordinates are discarded or replaced in this finite projection. -/
theorem finiteCoordinates_hasLaw {N : ℕ} (p : σ → ℕ) (hp : Function.Injective p) :
    HasLaw (finiteCoordinates (N := N) p)
      (SYK.standardGaussianMeasureOnEuclidean (SelectedCoordinate N p)) (disorderLaw N) := by
  have hblocks : HasLaw (fun J : Disorder N => fun i : σ => J (p i))
      (Measure.pi fun i : σ => SphericalAging.FiniteModel.disorderLaw N (p i+2)) (disorderLaw N) :=
    iIndepFun.hasLaw_pi (fun i => degree_hasLaw (p i)) ((independent_degrees N).precomp hp)
  let e := (MeasurableEquiv.piCurry
    (fun i : σ => fun _ : SphericalAging.FiniteModel.TensorIndex N (p i+2) => ℝ)).symm
  have hflat : HasLaw e
      (Measure.pi fun _ : SelectedCoordinate N p => gaussianReal 0 1)
      (Measure.pi fun i : σ => SphericalAging.FiniteModel.disorderLaw N (p i+2)) := by
    refine ⟨e.measurable.aemeasurable,?_⟩
    have h := Measure.infinitePi_map_piCurry_symm
      (fun (i : σ) (_ : SphericalAging.FiniteModel.TensorIndex N (p i+2)) => gaussianReal 0 1)
    simpa only [Measure.infinitePi_eq_pi,SphericalAging.FiniteModel.disorderLaw] using h
  have hgauss : HasLaw (WithLp.toLp 2 : (SelectedCoordinate N p → ℝ) →
      EuclideanSpace ℝ (SelectedCoordinate N p))
      (SYK.standardGaussianMeasureOnEuclidean (SelectedCoordinate N p))
      (Measure.pi fun _ : SelectedCoordinate N p => gaussianReal 0 1) := ⟨by fun_prop,rfl⟩
  exact hgauss.comp (hflat.comp hblocks)

end SlowEquilibration.SphericalInfiniteModel
