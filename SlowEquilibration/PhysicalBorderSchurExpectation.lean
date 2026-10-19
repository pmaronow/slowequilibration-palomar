-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalCommonBorderMoments
public import SlowEquilibration.GOEPhysicalGapEvent

/-! Same-space full/raw-bulk determinant approximation from the literal
clipped Schur scalar. The actual spectral gap supplies the good-event
identity and the full determinant second moment controls the rare loss.
-/
@[expose] public section
namespace SlowEquilibration.PhysicalCommonBorderMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Set Matrix
open BorderSchurExpectation BorderClippedSchurIdentity GOEPhysicalGapEvent
open GOEClippedResolvent GOERawMoments GOEPhysicalPotential
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

def clippedSchur {n : ℕ} (W : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k κ : ℝ) (a : Ω → ℝ) (u : Ω → EuclideanSpace ℝ (Fin (n + 1))) (x : Ω) : ℝ :=
  k - a x - inner ℝ (u x) (clippedInverseOperator k κ (W x) (u x))

lemma border_neg_row_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (u : ι → ℝ) (T : Matrix ι ι ℝ) :
    (GOEBorderedDeterminant.border a (-u) (-u) T).det =
      (GOEBorderedDeterminant.border a u u T).det := by
  rw [GOEBorderedDeterminant.border_det, GOEBorderedDeterminant.border_det,
    Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

/-- All terms are ordinary true expectations on the original common
space; the desired full determinant approximation is a conclusion. -/
theorem normalized_full_border_schur_error [IsProbabilityMeasure P]
    {n N : ℕ} {b k κ : ℝ} (hκ : 0 < κ)
    (W : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hW : Measurable W)
    (hSym : ∀ x, (W x).IsHermitian)
    (hLaw : HasLaw W (SphericalGaussianJet.goeLaw (n + 1) N b) P)
    (a : Ω → ℝ) (u : Ω → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : Measurable a) (hu : Measurable u)
    (hm : 0 < physicalMean n N b k) (s : ℝ)
    (hD2 : Integrable (fun x => (fullBorder W k a u x / physicalMean n N b k) ^ 2) P)
    (hB2 : Integrable (fun x => (matrixAbsoluteDet n k (W x) / physicalMean n N b k) ^ 2) P)
    (hT2 : Integrable (fun x => (clippedSchur W k κ a u x - s) ^ 2) P)
    (hT : Measurable (clippedSchur W k κ a u)) :
    let m := physicalMean n N b k
    let B := fun x => matrixAbsoluteDet n k (W x) / m
    let D := fun x => fullBorder W k a u x / m
    let T := fun x => clippedSchur W k κ a u x - s
    Integrable (fun x => |D x - |s| * B x|) P ∧
      (∫ x, |D x - |s| * B x| ∂P) ≤
        Real.sqrt (∫ x, B x ^ 2 ∂P) * Real.sqrt (∫ x, T x ^ 2 ∂P) +
          (Real.sqrt (∫ x, D x ^ 2 ∂P) + |s| * Real.sqrt (∫ x, B x ^ 2 ∂P)) *
            Real.sqrt ((SphericalGaussianJet.goeLaw (n + 1) N b).real (gapEvent n k κ)ᶜ) ∧
      abs ((∫ x, D x ∂P) - |s|) ≤
        Real.sqrt (∫ x, B x ^ 2 ∂P) * Real.sqrt (∫ x, T x ^ 2 ∂P) +
          (Real.sqrt (∫ x, D x ^ 2 ∂P) + |s| * Real.sqrt (∫ x, B x ^ 2 ∂P)) *
            Real.sqrt ((SphericalGaussianJet.goeLaw (n + 1) N b).real (gapEvent n k κ)ᶜ) := by
  dsimp only
  let m := physicalMean n N b k
  let D := fun x => fullBorder W k a u x / m
  let B := fun x => matrixAbsoluteDet n k (W x) / m
  let T := clippedSchur W k κ a u
  let G := W ⁻¹' gapEvent n k κ
  have hG : MeasurableSet G := (gapEvent_measurable n k κ).preimage hW
  have hDM : MemLp D 2 P := (memLp_two_iff_integrable_sq
    ((fullBorder_measurable hW k ha hu).div_const m).aestronglyMeasurable).mpr hD2
  have hBM : MemLp B 2 P := (memLp_two_iff_integrable_sq
    (((matrixAbsoluteDet_measurable n k).comp hW).div_const m).aestronglyMeasurable).mpr hB2
  have hTM : MemLp (fun x => T x - s) 2 P := (memLp_two_iff_integrable_sq
    (hT.sub_const s).aestronglyMeasurable).mpr hT2
  have hgood : ∀ᵐ x ∂P, x ∈ G → |D x - |s| * B x| ≤ |B x| * |T x - s| := by
    filter_upwards [] with x
    intro hx
    have hgap : ‖(Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)) (W x)‖ ≤ k - κ := hx
    have hp := border_abs_error_of_norm_gap (W x) (hSym x) k hκ hgap (k - a x) s (u x)
    have hleft : |D x - |s| * B x| =
        |fullBorder W k a u x - |s| * matrixAbsoluteDet n k (W x)| / m := by
      dsimp only [D, B]
      rw [← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hm]
    have hB0 : 0 ≤ B x := div_nonneg (abs_nonneg _) hm.le
    rw [hleft, abs_of_nonneg hB0]
    exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by
      dsimp only [B, T, clippedSchur, m, matrixAbsoluteDet]
      ring)
  have hprob : P.real Gᶜ = (SphericalGaussianJet.goeLaw (n + 1) N b).real (gapEvent n k κ)ᶜ := by
    rw [← hLaw.map_eq]
    simp only [Measure.real]
    rw [Measure.map_apply hW (gapEvent_measurable n k κ).compl]
    rfl
  have hE := integral_abs_error_of_good_event D B T hDM hBM s hTM G hG hgood
  have hM := abs_mean_error_of_good_event D B T hDM hBM s hTM G hG hgood
  have hBulkMean : (∫ x, B x ∂P) = 1 := by
    dsimp only [B]
    rw [integral_div]
    have he := hLaw.integral_comp (matrixAbsoluteDet_measurable n k).aestronglyMeasurable
    simp only [Function.comp_def] at he
    rw [he]
    exact div_self hm.ne'
  rw [hprob] at hE hM
  rw [hBulkMean, mul_one] at hM
  exact ⟨hE.1,hE.2,hM⟩

end
end SlowEquilibration.PhysicalCommonBorderMoments
