-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.UnrestrictedConditionedDeterminants
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! True GOE absolute determinant means are positive at every real shift. -/

@[expose] public section
namespace SlowEquilibration.GOEAllShiftPositivity

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet UnrestrictedConditionedDeterminants
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma gaussianReal_isOpenPosMeasure (mu : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal mu v).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  exact fun hz => (hU.measure_pos volume hUne).ne' ((gaussianReal_absolutelyContinuous' mu hv) hz)

lemma symmetricMatrix_continuous (n : ℕ) : Continuous (symmetricMatrix (k := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold symmetricMatrix
  split_ifs <;> exact continuous_apply _

/-- Positive ordinary GOE absolute determinant mean at every k, including
inside the semicircle support. The proof uses an actual positive-density open
coefficient neighborhood of a nonsingular shifted matrix. -/
theorem abs_determinant_mean_pos (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) (k : ℝ) :
    0 < ∫ W : Matrix (Fin n) (Fin n) ℝ, |(W-k • 1).det| ∂goeLaw n N b := by
  let V : UpperIndex n → ℝ≥0 := fun ij =>
    ((b/(N:ℝ))*(if ij.val.1=ij.val.2 then 2 else 1)).toNNReal
  have hV (ij : UpperIndex n) : V ij ≠ 0 := by
    apply ne_of_gt
    apply Real.toNNReal_pos.mpr
    have hdiv : 0 < b/(N:ℝ) := div_pos hb (by exact_mod_cast hN)
    split_ifs <;> positivity
  let (ij : UpperIndex n) : (gaussianReal 0 (V ij)).IsOpenPosMeasure :=
    gaussianReal_isOpenPosMeasure 0 (hV ij)
  let ν := Measure.pi (fun ij : UpperIndex n => gaussianReal 0 (V ij))
  let F := fun z : UpperIndex n → ℝ => |(symmetricMatrix z-k • (1 : Matrix (Fin n) (Fin n) ℝ)).det|
  have hFC : Continuous F :=
    ((symmetricMatrix_continuous n).sub continuous_const).matrix_det.abs
  have hFI : Integrable F ν := by
    have hi := (fixed_shifted_determinant_integrable n N b k).abs
    change Integrable (fun W : Matrix (Fin n) (Fin n) ℝ => |(W-k • 1).det|) (ν.map symmetricMatrix) at hi
    exact (integrable_map_measure hi.aestronglyMeasurable (symmetricMatrix_measurable n).aemeasurable).mp hi
  let z : UpperIndex n → ℝ := fun ij => (k+1)*(if ij.val.1=ij.val.2 then 1 else 0)
  have hz : symmetricMatrix z = (k+1) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [symmetricMatrix,z]
    · simp [symmetricMatrix,z,hij,Ne.symm hij]
  have hFz : F z ≠ 0 := by
    dsimp only [F]
    rw [hz]
    have he : (k+1) • (1 : Matrix (Fin n) (Fin n) ℝ)-k • 1 = 1 := by
      rw [← sub_smul]
      simp
    rw [he,Matrix.det_one,abs_one]
    norm_num
  have hp := integral_pos_of_integrable_nonneg_nonzero hFC hFI (fun _ => abs_nonneg _) hFz
  change 0 < ∫ W : Matrix (Fin n) (Fin n) ℝ,|(W-k • 1).det| ∂ν.map symmetricMatrix
  have hd : Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => |(W-k • 1).det|) :=
    (continuous_id.sub continuous_const).matrix_det.abs
  rw [integral_map (φ := symmetricMatrix) (f := fun W : Matrix (Fin n) (Fin n) ℝ => |(W-k • 1).det|)
    (symmetricMatrix_measurable n).aemeasurable hd.aestronglyMeasurable]
  exact hp

end
end SlowEquilibration.GOEAllShiftPositivity
