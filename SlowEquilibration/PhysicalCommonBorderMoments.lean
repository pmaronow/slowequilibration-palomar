-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalClippedDeterminantMoments
public import SlowEquilibration.BorderClippedSchurIdentity
public import SlowEquilibration.BorderFactorFourthMoment

/-! Same-space second moments of the full physical bordered determinant.
The actual physical bulk law supplies clipped moments. Ordinary corner/row
moments control the border, without any independence premise.
-/
@[expose] public section
namespace SlowEquilibration.PhysicalCommonBorderMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix
open GOEAsymptotics GOEScaling GOEPhysicalPotential GOEPhysicalClippedDeterminantMoments
open OneBorderMoments BorderClippedSchurIdentity BorderFactorFourthMoment
open scoped Topology BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

def fullBorder {n : ℕ} (W : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : ℝ) (a : Ω → ℝ) (u : Ω → EuclideanSpace ℝ (Fin (n + 1))) (x : Ω) : ℝ :=
  |(GOEBorderedDeterminant.border (k - a x) (WithLp.ofLp (u x)) (WithLp.ofLp (u x))
    (k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W x)).det|

lemma fullBorder_measurable {n : ℕ}
    {W : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hW : Measurable W)
    (k : ℝ) {a : Ω → ℝ} {u : Ω → EuclideanSpace ℝ (Fin (n + 1))}
    (ha : Measurable a) (hu : Measurable u) : Measurable (fullBorder W k a u) := by
  have hM : Measurable (fun x => GOEBorderedDeterminant.border (k - a x)
      (WithLp.ofLp (u x)) (WithLp.ofLp (u x))
      (k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W x)) := by
    apply Measurable.of_eval_matrix
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact measurable_const.sub ha
      | inr j => exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) j).measurable.comp hu
    | inr i =>
      cases j with
      | inl j => exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).measurable.comp hu
      | inr j =>
        change Measurable (fun x => k * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j - W x i j)
        fun_prop
  exact continuous_id.matrix_det.measurable.comp hM |>.abs

lemma fullBorder_clipped_bound {n : ℕ} (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hW : W.IsHermitian) (k a : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    |(GOEBorderedDeterminant.border (k - a) (WithLp.ofLp u) (WithLp.ofLp u)
      (k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W)).det| ≤
      matrixClippedDet n k ρ W * (|k - a| + ‖u‖ ^ 2 / ρ) := by
  let A := matrixToGaussian W
  have hs : ∀ i j, A i j = A j i := by
    intro i j
    change W i j = W j i
    have hh := congrFun (congrFun hW j) i
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
  have h := OneBorderDeterminant.shifted_one_border_bound W hW k hρ (k - a) (WithLp.ofLp u)
  rw [OneBorderMoments.eigenvalue_trace_eq A hs hW (fun z => Real.log (max |k - z| ρ))] at h
  simpa only [matrixClippedDet, eigenvalues, A, ← EuclideanSpace.real_norm_sq_eq] using h

/-- A true physical GOE bulk and primitive ordinary border moments imply
the full determinant second moment, even if all border randomness depends
on the bulk. The clipped moment input is derived by the uniform GOE theorem. -/
theorem full_border_second_moment_eventually {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g / (2 * Real.sqrt b)) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n + 1 ≤ N → ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (W : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), Measurable W →
        HasLaw W (SphericalGaussianJet.goeLaw (n + 1) N b) P →
      (∀ x, (W x).IsHermitian) →
      ∀ (a : Ω → ℝ) (u : Ω → EuclideanSpace ℝ (Fin (n + 1))), Measurable a → Measurable u →
      ∀ L Ca Cu : ℝ, (scaleFactor n N b * ρ)⁻¹ ≤ L →
      Integrable (fun x => |a x| ^ 4) P → Integrable (fun x => ‖u x‖ ^ 8) P →
      (∫ x, |a x| ^ 4 ∂P) ≤ Ca → (∫ x, ‖u x‖ ^ 8 ∂P) ≤ Cu →
      0 < physicalMean n N b k ∧
      Integrable (fun x => (fullBorder W k a u x / physicalMean n N b k) ^ 2) P ∧
      (∫ x, (fullBorder W k a u x / physicalMean n N b k) ^ 2 ∂P) ≤
        Real.sqrt ((2 : ℝ) ^ 4 * Real.exp (64 * b / g ^ 2)) *
          Real.sqrt (64 * (|k| ^ 4 + Ca) + 8 * L ^ 4 * Cu) := by
  filter_upwards [physical_clipped_normalized_moments_eventually hb hg hρ hρg,
    GOESharpMoments.goe_determinant_moments_eventually hb hg] with n hclip hraw
  intro N hN k hk Ω _ P _ W hW hLaw hSym a u ha hu L Ca Cu hL haI huI haM huM
  let m := physicalMean n N b k
  let κ := scaleFactor n N b * ρ
  have hNp : 0 < N := by omega
  have hκ : 0 < κ := mul_pos (scaleFactor_pos n hNp hb) hρ
  have hm : 0 < m := (hraw N hN k hk).2.1
  have hBF := factor_fourth_moment k hκ hL a u ha hu haI huI haM huM
  have hClip := hclip N hN k hk 4 (by norm_num)
  have hEI := hLaw.integrable_fun_comp hClip.1
  have hEM := hLaw.integral_comp
    (((matrixClippedDet_measurable n k κ).div_const m).pow_const (4 : ℝ)).aestronglyMeasurable
  have hdom : ∀ᵐ x ∂P, fullBorder W k a u x / m ≤
      (matrixClippedDet n k κ (W x) / m) * factor k κ a u x := by
    filter_upwards [] with x
    have hp := fullBorder_clipped_bound (W x) (hSym x) k (a x) (u x) hκ
    exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by unfold factor; ring)
  have h := moment_of_product_domination
    (fun x => fullBorder W k a u x / m) (fun x => matrixClippedDet n k κ (W x) / m)
    (factor k κ a u) ((fullBorder_measurable hW k ha hu).div_const m)
    (((matrixClippedDet_measurable n k κ).comp hW).div_const m)
    (factor_measurable k κ ha hu) (fun x => div_nonneg (abs_nonneg _) hm.le)
    (fun x => div_nonneg (matrixClippedDet_pos n k κ (W x)).le hm.le)
    (factor_nonneg k hκ a u) hdom (r := 2) (by norm_num)
    (by simpa only [show (2 * 2 : ℝ) = 4 by norm_num, m, κ] using hEI)
    (by simpa only [show (2 * 2 : ℝ) = 4 by norm_num, Real.rpow_ofNat] using hBF.1)
  refine ⟨hm, by simpa only [Real.rpow_two] using h.1, ?_⟩
  have hBound : (∫ x, (matrixClippedDet n k κ (W x) / m) ^ (2 * (2 : ℝ)) ∂P) ≤
      (2 : ℝ) ^ 4 * Real.exp (64 * b / g ^ 2) := by
    simpa only [Function.comp_def, show (2 * 2 : ℝ) = 4 by norm_num,
      show 4 * b * (4 : ℝ) ^ 2 / g ^ 2 = 64 * b / g ^ 2 by ring, Real.rpow_ofNat]
      using hEM.trans_le hClip.2
  have hFBound : (∫ x, factor k κ a u x ^ (2 * (2 : ℝ)) ∂P) ≤
      64 * (|k| ^ 4 + Ca) + 8 * L ^ 4 * Cu := by
    simpa only [show (2 * 2 : ℝ) = 4 by norm_num, Real.rpow_ofNat] using hBF.2
  have hh := h.2.trans (mul_le_mul (Real.sqrt_le_sqrt hBound) (Real.sqrt_le_sqrt hFBound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simpa only [Real.rpow_two] using hh

end
end SlowEquilibration.PhysicalCommonBorderMoments
