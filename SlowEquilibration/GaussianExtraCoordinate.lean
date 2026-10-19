-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

@[expose] public section

noncomputable section

namespace SlowEquilibration.GaussianExtraCoordinate

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- Projection onto the original Gaussian disorder coordinates. -/
noncomputable def projection :
    EuclideanSpace ℝ (ι ⊕ Unit) →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (Sum.inl i)))

/-- The additional independent standard Gaussian coordinate. -/
noncomputable def extra : EuclideanSpace ℝ (ι ⊕ Unit) →L[ℝ] ℝ :=
  EuclideanSpace.proj (Sum.inr ())

omit [Fintype ι] in
@[simp] theorem projection_apply (x : EuclideanSpace ℝ (ι ⊕ Unit)) (i : ι) :
    projection x i = x (.inl i) := rfl

omit [Fintype ι] in
@[simp] theorem extra_apply (x : EuclideanSpace ℝ (ι ⊕ Unit)) :
    extra x = x (.inr ()) := rfl

omit [Fintype ι] in
@[simp] theorem projection_single_extra [DecidableEq ι] (s : ℝ) :
    projection (EuclideanSpace.single (.inr ()) s : EuclideanSpace ℝ (ι ⊕ Unit)) = 0 := by
  classical
  ext i
  simp

omit [Fintype ι] in
@[simp] theorem extra_single_extra [DecidableEq ι] (s : ℝ) :
    extra (EuclideanSpace.single (.inr ()) s : EuclideanSpace ℝ (ι ⊕ Unit)) = s := by
  classical
  simp

/-- Splitting off the extra coordinate preserves the product Gaussian law. -/
theorem map_split_stdGaussian :
    (stdGaussian (EuclideanSpace ℝ (ι ⊕ Unit))).map
      (fun x => (projection x, extra x)) =
        (stdGaussian (EuclideanSpace ℝ ι)).prod (gaussianReal 0 1) := by
  let g := gaussianReal 0 1
  have hleft : MeasurePreserving (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (Measure.pi (fun _ : ι => g)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hright := measurePreserving_eval (fun _ : Unit => g) ()
  have hp := hleft.prod hright
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ Unit => g)
  have h := (hp.comp hs).map_eq
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact h

end SlowEquilibration.GaussianExtraCoordinate
