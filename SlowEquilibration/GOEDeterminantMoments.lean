-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEAsymptotics
public import SlowEquilibration.Upstream.OAI.Probability.SKGap.Matrix.RegularizedLogDet
public import SphericalAging.GaussianLipschitzConcentration

@[expose] public section

/-!
# Actual regularized GOE determinant moments

The determinant here is the square root of the determinant of
`(k I - W)^T (k I - W) + gamma I`, for positive `gamma`. Gaussian concentration
is applied to its actual logarithm, using the proved Frobenius-Lipschitz
matrix log-determinant estimate. This is an auxiliary regularized result;
the manuscript's raw clipped determinant theorem is not identified with it.
-/

namespace SlowEquilibration.GOEDeterminantMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology Matrix.Norms.Frobenius

theorem frobenius_gaussianToMatrix {k : ℕ} (A : GOEAsymptotics.GaussianMatrix k) :
    ‖gaussianToMatrix A‖ = ‖A‖ := rfl

theorem symmetrize_difference_norm {k : ℕ} (sigma : ℝ)
    (A B : GOEAsymptotics.GaussianMatrix k) :
    ‖symmetrizeGaussianMatrix sigma A - symmetrizeGaussianMatrix sigma B‖ ≤
      2 * |sigma| * ‖A - B‖ := by
  rw [symmetrizeGaussianMatrix, symmetrizeGaussianMatrix, ← smul_sub]
  have heq : (A + transposeGaussianMatrix A) - (B + transposeGaussianMatrix B) =
      (A - B) + transposeGaussianMatrix (A - B) := by rw [map_sub]; abel
  rw [heq, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |sigma| * (‖A - B‖ + ‖transposeGaussianMatrix (A - B)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

def shiftedMatrix (n : ℕ) (sigma k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  k • 1 - gaussianToMatrix (symmetrizeGaussianMatrix sigma A)

def rawLogDet (n : ℕ) (sigma gamma k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  ((n + 1 : ℝ) / 2) * OAI.SKGap.LogDet.regularizedLogDet gamma (shiftedMatrix n sigma k A)

def rawDet (n : ℕ) (sigma gamma k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  Real.sqrt (OAI.SKGap.LogDet.regularizedGram gamma (shiftedMatrix n sigma k A)).det

def rawLip (n : ℕ) (sigma gamma : ℝ) : ℝ≥0 :=
  ⟨((n + 1 : ℝ) / 2) * (1 / Real.sqrt ((n + 1 : ℝ) * gamma)) * (2 * |sigma|), by positivity⟩

theorem rawLogDet_lipschitz (n : ℕ) (sigma k : ℝ) {gamma : ℝ} (hgamma : 0 < gamma) :
    LipschitzWith (rawLip n sigma gamma) (rawLogDet n sigma gamma k) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change |rawLogDet n sigma gamma k A - rawLogDet n sigma gamma k B| ≤
    (rawLip n sigma gamma : ℝ) * ‖A - B‖
  unfold rawLogDet
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ) / 2)]
  have hreg := OAI.SKGap.LogDet.regularizedLogDet_lipschitz hgamma
    (shiftedMatrix n sigma k A) (shiftedMatrix n sigma k B)
  have hshift : shiftedMatrix n sigma k A - shiftedMatrix n sigma k B =
      gaussianToMatrix (symmetrizeGaussianMatrix sigma B - symmetrizeGaussianMatrix sigma A) := by
    ext i j
    simp only [shiftedMatrix, gaussianToMatrix, Matrix.sub_apply, PiLp.sub_apply]
    ring
  rw [hshift, frobenius_gaussianToMatrix] at hreg
  have hnorm := symmetrize_difference_norm sigma B A
  rw [norm_sub_rev B A] at hnorm
  have hreg' := hreg.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have h := mul_le_mul_of_nonneg_left hreg' (by positivity : 0 ≤ (n + 1 : ℝ) / 2)
  change _ ≤ (((n + 1 : ℝ) / 2) * (1 / Real.sqrt ((n + 1 : ℝ) * gamma)) * (2 * |sigma|)) * ‖A - B‖
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, mul_assoc] using h

/-- The exponential of the actual logarithm is the literal positive
regularized determinant, not a separately supplied random variable. -/
theorem exp_rawLogDet_eq_rawDet (n : ℕ) (sigma k : ℝ) {gamma : ℝ} (hgamma : 0 < gamma)
    (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    Real.exp (rawLogDet n sigma gamma k A) = rawDet n sigma gamma k A := by
  have hdet := (OAI.SKGap.LogDet.regularizedGram_posDef hgamma (shiftedMatrix n sigma k A)).det_pos
  have hlog : rawLogDet n sigma gamma k A =
      Real.log (OAI.SKGap.LogDet.regularizedGram gamma (shiftedMatrix n sigma k A)).det / 2 := by
    unfold rawLogDet OAI.SKGap.LogDet.regularizedLogDet
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [hlog]
  unfold rawDet
  symm
  apply (Real.sqrt_eq_iff_eq_sq hdet.le (Real.exp_pos _).le).mpr
  rw [← Real.exp_nat_mul]
  convert (Real.exp_log hdet).symm using 1
  congr 1
  ring

theorem rawLip_normalized_sq (n : ℕ) {gamma : ℝ} (hgamma : 0 < gamma) :
    (rawLip n (goeScale n) gamma : ℝ) ^ 2 = 1 / (2 * gamma) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hscale := goeScale_square n
  change (((n + 1 : ℝ) / 2) * (1 / Real.sqrt ((n + 1 : ℝ) * gamma)) * (2 * |goeScale n|)) ^ 2 = _
  rw [mul_pow, mul_pow, div_pow, one_div_pow, mul_pow, sq_abs,
    Real.sq_sqrt (mul_nonneg hn.le hgamma.le)]
  field_simp
  have heq : 2 * goeScale n ^ 2 * (n + 1 : ℝ) = 1 := by
    rw [hscale, inv_mul_cancel₀ hn.ne']
  nlinarith [heq]

/-- Actual centered logarithmic regularized determinants have a
dimension-independent Gaussian MGF bound. -/
theorem rawLogDet_centered_subGaussian (n : ℕ) (k : ℝ) {gamma : ℝ} (hgamma : 0 < gamma) :
    HasSubgaussianMGF (fun A : GOEAsymptotics.GaussianMatrix (n + 1) =>
        rawLogDet n (goeScale n) gamma k A -
          ∫ B, rawLogDet n (goeScale n) gamma k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      (Real.pi ^ 2 / (8 * gamma)).toNNReal (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) := by
  have h := SphericalAging.GaussianLipschitzConcentration.centered_hasSubgaussianMGF
    (rawLogDet n (goeScale n) gamma k) (rawLogDet_lipschitz n (goeScale n) k hgamma)
  have hc : SphericalAging.GaussianSmoothConcentration.rotationConstant
      (rawLip n (goeScale n) gamma) = (Real.pi ^ 2 / (8 * gamma)).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    change (Real.pi / 2) ^ 2 * (rawLip n (goeScale n) gamma : ℝ) ^ 2 = _
    rw [rawLip_normalized_sq n hgamma]
    ring
  rw [hc] at h
  exact h

/-- A general expectation-normalization step, proved by actual Jensen and
the actual centered MGF. It will be instantiated for the realized GOE
determinant logarithm above. -/
theorem normalized_exponential_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (c : ℝ≥0) (hG : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) c μ) :
    0 < ∫ x, Real.exp (f x) ∂μ ∧ ∀ r : ℝ, 0 ≤ r →
      Integrable (fun x => (Real.exp (f x) / (∫ y, Real.exp (f y) ∂μ)) ^ r) μ ∧
      (∫ x, (Real.exp (f x) / (∫ y, Real.exp (f y) ∂μ)) ^ r ∂μ) ≤ Real.exp ((c : ℝ) * r ^ 2 / 2) := by
  let m := ∫ y, f y ∂μ
  have hExp : Integrable (fun x => Real.exp (f x)) μ := by
    have hi := (hG.integrable_exp_mul 1).mul_const (Real.exp m)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun x => by
      simp only [one_mul]
      rw [← Real.exp_add]
      congr 1
      dsimp [m]
      ring)
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun _ => mem_univ _)) hf hExp
  have hmean : 0 < ∫ x, Real.exp (f x) ∂μ := (Real.exp_pos _).trans_le hJ
  refine ⟨hmean, ?_⟩
  intro r hr
  have hpoint (x : Ω) : (Real.exp (f x) / (∫ y, Real.exp (f y) ∂μ)) ^ r ≤
      Real.exp (r * (f x - m)) := by
    calc
      _ ≤ (Real.exp (f x) / Real.exp m) ^ r :=
        Real.rpow_le_rpow (div_nonneg (Real.exp_pos _).le hmean.le)
          (div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos m) hJ) hr
      _ = _ := by rw [← Real.exp_sub, ← Real.exp_mul]; congr 1; ring
  have hInt : Integrable (fun x => (Real.exp (f x) / (∫ y, Real.exp (f y) ∂μ)) ^ r) μ := by
    apply (hG.integrable_exp_mul r).mono'
    · exact (((hf.aemeasurable.exp).div_const _).pow_const r).aestronglyMeasurable
    · exact ae_of_all μ (fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        exact hpoint x)
  refine ⟨hInt, ?_⟩
  exact (integral_mono hInt (hG.integrable_exp_mul r) hpoint).trans (hG.mgf_le r)

/-- Uniform in the dimension and the real shift; every positive moment of
this literal regularized determinant divided by its own expectation is bounded. -/
theorem rawDet_normalized_moments (n : ℕ) (k : ℝ) {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < ∫ A, rawDet n (goeScale n) gamma k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) ∧
    ∀ r : ℝ, 0 ≤ r →
      Integrable (fun A => (rawDet n (goeScale n) gamma k A /
        (∫ B, rawDet n (goeScale n) gamma k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r)
        (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ∧
      (∫ A, (rawDet n (goeScale n) gamma k A /
        (∫ B, rawDet n (goeScale n) gamma k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r
          ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤ Real.exp (Real.pi ^ 2 * r ^ 2 / (16 * gamma)) := by
  have h := normalized_exponential_moments (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    (rawLogDet n (goeScale n) gamma k)
    (SphericalAging.GaussianSmoothConcentration.integrable_lipschitz _
      (rawLogDet_lipschitz n (goeScale n) k hgamma))
    (Real.pi ^ 2 / (8 * gamma)).toNNReal (rawLogDet_centered_subGaussian n k hgamma)
  simp only [exp_rawLogDet_eq_rawDet n (goeScale n) k hgamma] at h
  refine ⟨h.1, fun r hr => ⟨(h.2 r hr).1, ?_⟩⟩
  have hb := (h.2 r hr).2
  rw [Real.coe_toNNReal _ (by positivity)] at hb
  convert hb using 1
  congr 1
  ring

/-- The actual GOE matrix generated from independent standard Gaussian entries. -/
def realization (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  gaussianToMatrix (symmetrizeGaussianMatrix (goeScale n) A)

lemma realization_measurable (n : ℕ) : Measurable (realization n) :=
  (gaussianToMatrix_measurable (n + 1)).comp
    (symmetrizeGaussianMatrix_continuous (goeScale n)).measurable

lemma realization_law (n : ℕ) :
    (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).map (realization n) =
      SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1 := by
  have h := congrArg (fun μ => μ.map (gaussianToMatrix (k := n + 1)))
    (normalized_goeLaw_bridge n)
  rw [Measure.map_map (gaussianToMatrix_measurable (n + 1)) (matrixToGaussian_measurable (n + 1))] at h
  simp only [Function.comp_def, gaussianToMatrix_matrixToGaussian, Measure.map_id'] at h
  rw [OAI.CriticalSK.goeLaw,
    Measure.map_map (gaussianToMatrix_measurable (n + 1))
      (symmetrizeGaussianMatrix_continuous (goeScale n)).measurable] at h
  exact h.symm

def regularizedDet (n : ℕ) (gamma k : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  Real.sqrt (OAI.SKGap.LogDet.regularizedGram gamma (k • 1 - W)).det

lemma regularizedDet_measurable (n : ℕ) (gamma k : ℝ) : Measurable (regularizedDet n gamma k) := by
  unfold regularizedDet OAI.SKGap.LogDet.regularizedGram
  fun_prop

@[simp] lemma regularizedDet_realization (n : ℕ) (gamma k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    regularizedDet n gamma k (realization n A) = rawDet n (goeScale n) gamma k A := rfl

/-- A dimension-uniform moment bound under the same literal Matrix GOE law
used by the canonical mixed-field Hessian. It concerns the regularized
absolute determinant, not the manuscript's clipped or raw determinant. -/
theorem regularizedDet_normalized_moments (n : ℕ) (k : ℝ) {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < ∫ W, regularizedDet n gamma k W ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1 ∧
    ∀ r : ℝ, 0 ≤ r →
      Integrable (fun W => (regularizedDet n gamma k W /
        (∫ V, regularizedDet n gamma k V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) ^ r)
        (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ∧
      (∫ W, (regularizedDet n gamma k W /
        (∫ V, regularizedDet n gamma k V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) ^ r
          ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ≤
        Real.exp (Real.pi ^ 2 * r ^ 2 / (16 * gamma)) := by
  have hm := realization_measurable n
  have hd := regularizedDet_measurable n gamma k
  have hmean : (∫ W, regularizedDet n gamma k W ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) =
      ∫ A, rawDet n (goeScale n) gamma k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) := by
    rw [← realization_law n, integral_map hm.aemeasurable hd.aestronglyMeasurable]
    rfl
  have hraw := rawDet_normalized_moments n k hgamma
  refine ⟨by rw [hmean]; exact hraw.1, ?_⟩
  intro r hr
  have hfn : Measurable (fun W => (regularizedDet n gamma k W /
        (∫ V, regularizedDet n gamma k V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) ^ r) :=
    (hd.div_const _).pow_const r
  have hi := (hraw.2 r hr).1
  have hb := (hraw.2 r hr).2
  rw [hmean] at hfn ⊢
  refine ⟨?_, ?_⟩
  · rw [← realization_law n]
    apply (integrable_map_measure hfn.aestronglyMeasurable hm.aemeasurable).mpr
    simpa only [Function.comp_def, regularizedDet_realization] using hi
  · rw [← realization_law n, integral_map hm.aemeasurable hfn.aestronglyMeasurable]
    simpa only [regularizedDet_realization] using hb

end
end SlowEquilibration.GOEDeterminantMoments
