-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbsKernel

/-! The actual Gibbs construction is also a probability in the degenerate
zero-dimensional space. This harmless true boundary case permits literal
dimension-indexed probability families without replacing low dimensions. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gibbsLaw_probability_zero (β : ℝ) (H : Vector 0 → ℝ) :
    IsProbabilityMeasure (gibbsLaw 0 β H) := by
  let _ := sphereLaw_probability 0
  have hH : H = fun _ => H 0 := by
    funext x
    exact congrArg H (Subsingleton.elim x 0)
  have hpart : partition 0 β H = Real.exp (β*H 0) := by
    rw [partition, hH, integral_const, probReal_univ, one_smul]
  have hd : (fun x => ENNReal.ofReal (gibbsDensity 0 β H x)) = fun _ => (1 : ℝ≥0∞) := by
    funext x
    rw [gibbsDensity, hpart, show H x = H 0 from congrArg H (Subsingleton.elim x 0),
      div_self (Real.exp_pos _).ne', ENNReal.ofReal_one]
  rw [gibbsLaw, hd]
  change IsProbabilityMeasure ((sphereLaw 0).withDensity 1)
  rw [withDensity_one]
  infer_instance

theorem gibbsLaw_probability_all (N : ℕ) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    IsProbabilityMeasure (gibbsLaw N β H) := by
  cases N with
  | zero => exact gibbsLaw_probability_zero β H
  | succ n => exact gibbsLaw_probability (by omega) β hH

/-- The actual disorder-indexed Gibbs Markov kernel for every dimension. -/
def allDimensionGibbsKernel {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Kernel (Disorder N P) (Vector N) :=
  let _ := sphereLaw_probability N
  (Kernel.const (Disorder N P) (sphereLaw N)).withDensity
    (fun J x => ENNReal.ofReal (gibbsDensity N β (field c J) x))

@[simp] theorem allDimensionGibbsKernel_apply {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder N P) : allDimensionGibbsKernel c β J = gibbsLaw N β (field c J) := by
  let _ := sphereLaw_probability N
  unfold allDimensionGibbsKernel
  rw [Kernel.withDensity_apply _ (gibbsReferenceDensity_measurable (N := N) c β).ennreal_ofReal]
  rfl

instance allDimensionGibbsKernel_isMarkov {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    IsMarkovKernel (allDimensionGibbsKernel (N := N) c β) where
  isProbabilityMeasure J := by
    rw [allDimensionGibbsKernel_apply]
    exact gibbsLaw_probability_all N β (field_contDiff c J).continuous

end SlowEquilibration.SphericalModel
