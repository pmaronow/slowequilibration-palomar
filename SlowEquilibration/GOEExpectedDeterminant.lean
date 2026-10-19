-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPrincipalMinors
public import SlowEquilibration.JacobiPrefactors

@[expose] public section

/-! # Genuine signed Gaussian characteristic-polynomial expectations -/

namespace SlowEquilibration.GOEExpectedDeterminant

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function Matrix Polynomial
open OAI.CriticalSK GOEPrincipalMinors GOEBorderedDeterminant
open scoped ENNReal NNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal shifted matrix, without a spectral representation. -/
def shifted (n : ℕ) (k : ℝ) (A : GaussianMatrix (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  k • 1 - Matrix.of (fun i j => A i j)

def meanDet (n : ℕ) (s k : ℝ) : ℝ := ∫ A, (shifted n k A).det ∂goeLaw (Fin n) s

lemma shifted_det_integrable (n : ℕ) (s k : ℝ) :
    Integrable (fun A => (shifted n k A).det) (goeLaw (Fin n) s) :=
  shifted_determinant_integrable n s k

lemma shifted_det_measurable (n : ℕ) (k : ℝ) :
    Measurable (fun A => (shifted n k A).det) := by unfold shifted; fun_prop

lemma shifted_principal {m n : ℕ} (e : Fin m ↪o Fin n) (k : ℝ) (A : GaussianMatrix (Fin n)) :
    (shifted n k A).submatrix e e = shifted m k (principalMatrix e A) := by
  ext i j
  simp only [shifted, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Matrix.of_apply, principalMatrix, PiLp.toLp_apply,
    e.injective.eq_iff]

lemma adjugate_diagonal_eq_minor (n : ℕ) (k : ℝ) (A : GaussianMatrix (Fin (n + 1)))
    (i : Fin (n + 1)) :
    (shifted (n + 1) k A).adjugate i i = (shifted n k (principalMatrix i.succAboveOrderEmb A)).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hs : (-1 : ℝ) ^ (i + i : ℕ) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hs, one_mul]
  exact congrArg Matrix.det (shifted_principal i.succAboveOrderEmb k A)

lemma adjugate_diagonal_integrable (n : ℕ) (s k : ℝ) (i : Fin (n + 1)) :
    Integrable (fun A => (shifted (n + 1) k A).adjugate i i) (goeLaw (Fin (n + 1)) s) := by
  simp_rw [adjugate_diagonal_eq_minor]
  have hmp : MeasurePreserving (principalMatrix i.succAboveOrderEmb)
      (goeLaw (Fin (n + 1)) s) (goeLaw (Fin n) s) :=
    ⟨principalMatrix_measurable _, delete_principal_law n i s⟩
  exact hmp.integrable_comp_of_integrable (shifted_det_integrable n s k)

lemma mean_adjugate_diagonal (n : ℕ) (s k : ℝ) (i : Fin (n + 1)) :
    (∫ A, (shifted (n + 1) k A).adjugate i i ∂goeLaw (Fin (n + 1)) s) = meanDet n s k := by
  simp_rw [adjugate_diagonal_eq_minor]
  have hmp : MeasurePreserving (principalMatrix i.succAboveOrderEmb)
      (goeLaw (Fin (n + 1)) s) (goeLaw (Fin n) s) :=
    ⟨principalMatrix_measurable _, delete_principal_law n i s⟩
  have h := integral_map (μ := goeLaw (Fin (n + 1)) s) hmp.measurable.aemeasurable
    (shifted_det_measurable n k).aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

lemma mean_adjugate_trace (n : ℕ) (s k : ℝ) :
    (∫ A, (shifted (n + 1) k A).adjugate.trace ∂goeLaw (Fin (n + 1)) s) =
      (n + 1 : ℝ) * meanDet n s k := by
  simp only [Matrix.trace, Matrix.diag]
  rw [integral_finsetSum _ (fun i _ => adjugate_diagonal_integrable n s k i)]
  simp only [mean_adjugate_diagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma gaussian_square_integral (v : ℝ≥0) : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

lemma gaussian_product_second_integral (n : ℕ) (v : ℝ≥0) (i j : Fin n) :
    (∫ x : Fin n → ℝ, x i * x j ∂Measure.pi (fun _ : Fin n => gaussianReal 0 v)) =
      if i = j then (v : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have h := integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 v)
      (i := i) (f := fun x : ℝ => x ^ 2) (by fun_prop)
    simpa only [pow_two] using h.trans (gaussian_square_integral v)
  · rw [ite_eq_right hij]
    have hi := iIndepFun_pi (μ := fun _ : Fin n => gaussianReal 0 v)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => by fun_prop)
    have hind := hi.indepFun hij
    have h := hind.integral_mul_eq_mul_integral
      (show AEStronglyMeasurable (fun x : Fin n → ℝ => x i) _ from (measurable_pi_apply i).aestronglyMeasurable)
      (show AEStronglyMeasurable (fun x : Fin n → ℝ => x j) _ from (measurable_pi_apply j).aestronglyMeasurable)
    simp only [id_eq, Pi.mul_apply] at h
    rw [h]
    simp [integral_eval, integral_id_gaussianReal]

lemma determinant_integrable_of_entry_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {n : ℕ} (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp (fun x => A x i j) p μ) :
    Integrable (fun x => (A x).det) μ := by
  simp_rw [Matrix.det_apply']
  apply integrable_finsetSum
  intro σ hσ
  apply Integrable.const_mul
  apply integrable_product_of_all_moments
  intro i hi p hp
  exact hA _ _ p hp

lemma adjugate_entry_integrable (n : ℕ) (s k : ℝ) (i j : Fin (n + 1)) :
    Integrable (fun A => (shifted (n + 1) k A).adjugate i j) (goeLaw (Fin (n + 1)) s) := by
  simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  apply Integrable.const_mul
  apply determinant_integrable_of_entry_moments
  intro a b p hp
  change MemLp (fun A : GaussianMatrix (Fin (n + 1)) =>
    k * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j.succAbove a) (i.succAbove b) -
      A (j.succAbove a) (i.succAbove b)) p _
  exact (memLp_const _).sub (entry_memLp _ s _ _ hp)

/-- The actual first-row independent product supplied by the proved GOE law. -/
def blockLaw (n : ℕ) (s : ℝ) : Measure (ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n))) :=
  (gaussianReal 0 (4 * s ^ 2).toNNReal).prod
    ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s ^ 2).toNNReal).prod
      (goeLaw (Fin n) s))

lemma shifted_border_det (n : ℕ) (k a : ℝ) (v : Fin n → ℝ) (B : GaussianMatrix (Fin n)) :
    (shifted (n + 1) k (borderMatrix a (WithLp.toLp 2 v) B)).det =
      (k - a) * (shifted n k B).det -
        ∑ i : Fin n, ∑ j : Fin n, v i * (shifted n k B).adjugate i j * v j := by
  let A := shifted (n + 1) k (borderMatrix a (WithLp.toLp 2 v) B)
  have htail : A.submatrix Fin.succ Fin.succ = shifted n k B := by
    ext i j
    simp only [A, shifted, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Matrix.of_apply, borderMatrix_succ_succ, Fin.succ_inj]
  have hdiag : A 0 0 = k - a := by
    simp only [A, shifted, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, Matrix.of_apply, borderMatrix_zero_zero]
  have hrow (i : Fin n) : A 0 i.succ = -v i := by
    simp [A, shifted, (Fin.succ_ne_zero i).symm]
  have hcol (i : Fin n) : A i.succ 0 = -v i := by
    simp [A, shifted, Fin.succ_ne_zero]
  rw [det_successor_border A, htail, hdiag]
  simp only [hrow, hcol, dotProduct, mulVec, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma row_pair_integrable (n : ℕ) (v : ℝ≥0) (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i * x j) (Measure.pi (fun _ : Fin n => gaussianReal 0 v)) := by
  have h (i : Fin n) : HasLaw (fun x : Fin n → ℝ => x i) (gaussianReal 0 v)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 v)) :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 v) i).hasLaw
  exact (h i).hasGaussianLaw.memLp_two.mul (h j).hasGaussianLaw.memLp_two |>.integrable le_rfl

lemma block_linear_integrable (n : ℕ) (s k : ℝ) :
    Integrable (fun p : ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) =>
      (k - p.1) * (shifted n k p.2.2).det) (blockLaw n s) := by
  exact ((integrable_const k (μ := gaussianReal 0 (4 * s ^ 2).toNNReal)).sub
    (IsGaussian.integrable_id (μ := gaussianReal 0 (4 * s ^ 2).toNNReal))).mul_prod
    ((shifted_det_integrable n s k).comp_snd
      (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s ^ 2).toNNReal))

lemma block_pair_integrable (n : ℕ) (s k : ℝ) (i j : Fin (n + 1)) :
    Integrable (fun p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))) =>
      (p.2.1 i * p.2.1 j) * (shifted (n + 1) k p.2.2).adjugate i j) (blockLaw (n + 1) s) :=
  ((row_pair_integrable _ _ i j).mul_prod (adjugate_entry_integrable n s k i j)).comp_snd _

lemma block_linear_integral (n : ℕ) (s k : ℝ) :
    (∫ p : ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)),
      (k - p.1) * (shifted n k p.2.2).det ∂blockLaw n s) = k * meanDet n s k := by
  let μa := gaussianReal 0 (4 * s ^ 2).toNNReal
  let μv := Measure.pi (fun _ : Fin n => gaussianReal 0 (2 * s ^ 2).toNNReal)
  let μB := goeLaw (Fin n) s
  calc
    _ = (∫ a : ℝ, k - a ∂μa) *
        ∫ q : (Fin n → ℝ) × GaussianMatrix (Fin n), (shifted n k q.2).det ∂μv.prod μB :=
      integral_prod_mul (fun a : ℝ => k - a)
        (fun q : (Fin n → ℝ) × GaussianMatrix (Fin n) => (shifted n k q.2).det)
    _ = _ := by
      have ha : (∫ a : ℝ, k - a ∂μa) = k := by
        have h := integral_sub (f := fun _ : ℝ => k) (g := fun a : ℝ => a)
          (μ := μa) (integrable_const _) IsGaussian.integrable_id
        rw [h]
        simp [μa]
      have hb : (∫ q : (Fin n → ℝ) × GaussianMatrix (Fin n),
          (shifted n k q.2).det ∂μv.prod μB) = meanDet n s k := by
        simpa [μv, μB, meanDet] using integral_fun_snd (μ := μv) (ν := μB)
          (fun A => (shifted n k A).det)
      rw [ha, hb]

lemma block_pair_integral (n : ℕ) (s k : ℝ) (i j : Fin (n + 1)) :
    (∫ p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))),
      (p.2.1 i * p.2.1 j) * (shifted (n + 1) k p.2.2).adjugate i j ∂blockLaw (n + 1) s) =
      if i = j then (2 * s ^ 2) * meanDet n s k else 0 := by
  let μa := gaussianReal 0 (4 * s ^ 2).toNNReal
  let μv := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (2 * s ^ 2).toNNReal)
  let μB := goeLaw (Fin (n + 1)) s
  have h1 : (∫ p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))),
      (p.2.1 i * p.2.1 j) * (shifted (n + 1) k p.2.2).adjugate i j ∂blockLaw (n + 1) s) =
      ∫ q : (Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1)),
        (q.1 i * q.1 j) * (shifted (n + 1) k q.2).adjugate i j ∂μv.prod μB := by
    have h := integral_fun_snd (μ := μa) (ν := μv.prod μB)
      (fun q : (Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1)) =>
        (q.1 i * q.1 j) * (shifted (n + 1) k q.2).adjugate i j)
    simpa [μa, blockLaw] using h
  rw [h1]
  have h2 := integral_prod_mul (μ := μv) (ν := μB)
    (fun x : Fin (n + 1) → ℝ => x i * x j)
    (fun A : GaussianMatrix (Fin (n + 1)) => (shifted (n + 1) k A).adjugate i j)
  rw [h2, gaussian_product_second_integral]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, ite_eq_left rfl, mean_adjugate_diagonal]
    rw [Real.coe_toNNReal _ (by positivity)]
  · rw [ite_eq_right hij, ite_eq_right hij, zero_mul]

/-- Exact genuine integration of the independent first row and whole tail.
Off-diagonal quadratic terms vanish by actual Gaussian independence. -/
lemma block_determinant_integral (n : ℕ) (s k : ℝ) :
    (∫ p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))),
      (shifted (n + 2) k (borderMatrix p.1 (WithLp.toLp 2 p.2.1) p.2.2)).det
        ∂blockLaw (n + 1) s) =
      k * meanDet (n + 1) s k - (2 * s ^ 2) * (n + 1 : ℝ) * meanDet n s k := by
  have hi : Integrable (fun p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))) =>
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (p.2.1 i * p.2.1 j) * (shifted (n + 1) k p.2.2).adjugate i j) (blockLaw (n + 1) s) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => block_pair_integrable n s k i j))
  have heq : (fun p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))) =>
      (shifted (n + 2) k (borderMatrix p.1 (WithLp.toLp 2 p.2.1) p.2.2)).det) =
      (fun p => (k - p.1) * (shifted (n + 1) k p.2.2).det -
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          (p.2.1 i * p.2.1 j) * (shifted (n + 1) k p.2.2).adjugate i j) := by
    funext p
    rw [shifted_border_det]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, integral_sub (block_linear_integrable _ s k) hi, block_linear_integral]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => block_pair_integrable n s k i j))]
  simp_rw [integral_finsetSum _ (fun j _ => block_pair_integrable n s k _ j), block_pair_integral]
  simp [Nat.cast_add, Nat.cast_one]
  ring

@[simp] lemma meanDet_zero (s k : ℝ) : meanDet 0 s k = 1 := by
  simp [meanDet, shifted]

@[simp] lemma meanDet_one (s k : ℝ) : meanDet 1 s k = k := by
  have hmean : (∫ A : GaussianMatrix (Fin 1), A 0 0 ∂goeLaw (Fin 1) s) = 0 := by
    have h := integral_map (μ := goeLaw (Fin 1) s)
      (φ := fun A : GaussianMatrix (Fin 1) => A 0 0) (f := id)
      (by fun_prop) aestronglyMeasurable_id
    rw [goe_entry_law] at h
    simp only [id_eq, ite_true, integral_id_gaussianReal] at h
    exact h.symm
  have heq : (fun A : GaussianMatrix (Fin 1) => (shifted 1 k A).det) = fun A => k - A 0 0 := by
    funext A
    rw [Matrix.det_unique]
    simp [shifted]
  rw [meanDet, heq, integral_sub (integrable_const _)
    ((entry_memLp 1 s 0 0 (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).integrable le_rfl), hmean]
  simp

/-- The exact signed expected characteristic polynomial recurrence follows
from the actual Gaussian first-row product law and actual principal-minor laws. -/
theorem meanDet_three_term (n : ℕ) (s k : ℝ) :
    meanDet (n + 2) s k = k * meanDet (n + 1) s k -
      (2 * s ^ 2) * (n + 1 : ℝ) * meanDet n s k := by
  let f : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))) → ℝ := fun p =>
    (shifted (n + 2) k (borderMatrix p.1 (WithLp.toLp 2 p.2.1) p.2.2)).det
  have hf : Measurable f := by
    have hp : Measurable (fun p : ℝ × ((Fin (n + 1) → ℝ) × GaussianMatrix (Fin (n + 1))) =>
        (p.1, (WithLp.toLp 2 p.2.1, p.2.2))) :=
      measurable_fst.prodMk (((WithLp.measurable_toLp 2 _).comp
        (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
    exact (shifted_det_measurable (n + 2) k).comp ((borderMatrix_measurable (n + 1)).comp hp)
  have hmp := goeBlocks_preserving (n + 1) s
  have hmap := integral_map (μ := goeLaw (Fin (n + 2)) s) hmp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  have heq : (fun A : GaussianMatrix (Fin (n + 2)) => (shifted (n + 2) k A).det) =ᵐ[goeLaw (Fin (n + 2)) s]
      (fun A => f (goeBlocks A)) := by
    filter_upwards [goe_symmetric_ae (ι := Fin (n + 2)) s] with A hA
    dsimp [f]
    rw [borderMatrix_blocks A hA]
  calc
    _ = ∫ A, f (goeBlocks A) ∂goeLaw (Fin (n + 2)) s := integral_congr_ae heq
    _ = ∫ p, f p ∂blockLaw (n + 1) s := hmap.symm
    _ = _ := block_determinant_integral n s k

/-- Actual signed GOE determinant expectation, at every real shift and
variance parameter, equals the literal scaled-Hermite polynomial. -/
theorem meanDet_eq_scaledHermite (n : ℕ) (s k : ℝ) :
    meanDet n s k = (scaledHermite (2 * s ^ 2) n).eval k := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [scaledHermite]
  | more n h0 h1 =>
      rw [meanDet_three_term, h0, h1, scaledHermite_three_term]
      simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The same exact equality for the original explicit standard-Gaussian
matrix realization used by all actual absolute determinant estimates. -/
theorem standard_signed_mean_eq_hermiteValue (n : ℕ) (k : ℝ) :
    (∫ A, GOESignedAbsoluteTransfer.signedDet n k A
      ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) = JacobiPrefactors.hermiteValue n k := by
  have hmap := integral_map (μ := stdGaussian (GaussianMatrix (Fin (n + 1))))
    (φ := symmetrizeGaussianMatrix (goeScale n)) (f := fun A => (shifted (n + 1) k A).det)
    (symmetrizeGaussianMatrix_continuous _).measurable.aemeasurable
    (shifted_det_measurable _ _).aestronglyMeasurable
  have hmean := meanDet_eq_scaledHermite (n + 1) (goeScale n) k
  have hscale : 2 * goeScale n ^ 2 = (n + 1 : ℝ)⁻¹ := goeScale_square n
  rw [hscale] at hmean
  exact hmap.symm.trans hmean

end
end SlowEquilibration.GOEExpectedDeterminant
