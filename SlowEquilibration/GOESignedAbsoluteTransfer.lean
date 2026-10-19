-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOESharpMoments

@[expose] public section

/-!
# Signed and absolute GOE determinants

The actual signed determinant agrees with its clipped exponential on the true
spectral-gap event. A genuine Gaussian rare-event estimate then compares their
actual expectations, uniformly in every shift above the fixed positive gap.
-/

namespace SlowEquilibration.GOESignedAbsoluteTransfer

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics GOEEdgeConcentration GOEClippedDeterminants
open scoped NNReal ENNReal Topology BigOperators

/-- A signed observable may have negative values on the exceptional event.
This compares its true signed expectation with the exponential expectation. -/
theorem signed_exponential_expectation_comparison
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y S : Ω → ℝ) (hY : Integrable Y μ) (hS : AEMeasurable S μ)
    (c : ℝ≥0) (hG : HasSubgaussianMGF (fun x => Y x - ∫ y, Y y ∂μ) c μ)
    (B : Set Ω) (hB : MeasurableSet B)
    (hdom : ∀ᵐ x ∂μ, |S x| ≤ Real.exp (Y x))
    (heq : ∀ᵐ x ∂μ, x ∉ B → S x = Real.exp (Y x))
    (hsmall : Real.exp (c : ℝ) * Real.sqrt (μ.real B) ≤ 1 / 4) :
    Integrable S μ ∧ Integrable (fun x => Real.exp (Y x)) μ ∧
      0 < ∫ x, S x ∂μ ∧
      (∫ x, Real.exp (Y x) ∂μ) ≤ 2 * ∫ x, S x ∂μ ∧
      (∫ x, |S x| ∂μ) ≤ 2 * ∫ x, S x ∂μ := by
  let m := ∫ y, Y y ∂μ
  have hExp : Integrable (fun x => Real.exp (Y x)) μ := by
    apply ((hG.integrable_exp_mul 1).mul_const (Real.exp m)).congr
    exact ae_of_all μ (fun x => by
      simp only [one_mul]
      rw [← Real.exp_add]
      congr 1
      dsimp [m]
      ring)
  have hIntS : Integrable S μ := hExp.mono' hS.aestronglyMeasurable (by
    filter_upwards [hdom] with x hx
    simpa only [Real.norm_eq_abs] using hx)
  have hBad : (∫ x in B, Real.exp (Y x) ∂μ) ≤ Real.exp m / 4 := by
    have hb := RareEventMomentTransfer.exponential_on_bad_event_bound hG hB
    have heqExp : (fun x => Real.exp (Y x)) =
        (fun x => Real.exp m * Real.exp (Y x - m)) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heqExp, integral_const_mul]
    calc
      _ ≤ Real.exp m * (Real.exp (c : ℝ) * Real.sqrt (μ.real B)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos m).le
      _ ≤ Real.exp m * (1 / 4) := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos m).le
      _ = _ := by ring
  have hJ : Real.exp m ≤ ∫ x, Real.exp (Y x) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all μ (fun _ => mem_univ _)) hY hExp
  have hdiff : (∫ x, Real.exp (Y x) ∂μ) ≤
      (∫ x, S x ∂μ) + 2 * ∫ x in B, Real.exp (Y x) ∂μ := by
    rw [← integral_indicator hB, ← integral_const_mul, ← integral_add hIntS ((hExp.indicator hB).const_mul 2)]
    apply integral_mono_ae hExp (hIntS.add ((hExp.indicator hB).const_mul 2))
    filter_upwards [hdom, heq] with x hx hxeq
    change Real.exp (Y x) ≤ S x + 2 * B.indicator (fun x => Real.exp (Y x)) x
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB]
      have hneg := neg_abs_le (S x)
      linarith
    · simp only [indicator_of_notMem hxB, mul_zero, add_zero, hxeq hxB]
      exact le_rfl
  have hcompare : (∫ x, Real.exp (Y x) ∂μ) ≤ 2 * ∫ x, S x ∂μ := by linarith
  have hpos : 0 < ∫ x, S x ∂μ := by linarith [Real.exp_pos m]
  refine ⟨hIntS, hExp, hpos, hcompare, ?_⟩
  exact (integral_mono_ae hIntS.abs hExp hdom).trans hcompare

/-- Literal signed determinant of the actual Gaussian matrix realization. -/
def signedDet (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  (k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - GOEDeterminantMoments.realization n A).det

lemma signedDet_measurable (n : ℕ) (k : ℝ) : Measurable (signedDet n k) := by
  unfold signedDet
  have hreal := GOEDeterminantMoments.realization_measurable n
  fun_prop

@[simp] lemma abs_signedDet (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    |signedDet n k A| = absoluteDet n k A := rfl

lemma signedDet_eq_prod (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    signedDet n k A = ∏ i, (k - realizedEigenvalues n A i) := by
  rw [signedDet, GOEDeterminantMoments.realization,
    shifted_det_eq_prod k _ (symmetrize_symmetric _ _)]
  rfl

lemma signedDet_eq_clipped_of_not_bad (n : ℕ) {k g : ℝ} (hg : 0 < g) (hk : 2 + g ≤ k)
    (A : GOEAsymptotics.GaussianMatrix (n + 1)) (hA : A ∉ gapBad n g) :
    signedDet n k A = Real.exp (clippedTrace n k (g / 2) A) := by
  have hrad : realizedRadius n A ≤ 2 + g / 2 := le_of_not_gt hA
  have hpos : 0 < signedDet n k A := by
    rw [signedDet_eq_prod]
    apply Finset.prod_pos
    intro i hi
    have he := (le_abs_self (realizedEigenvalues n A i)).trans
      ((abs_eigenvalue_le_realizedRadius n A i).trans hrad)
    linarith
  calc
    _ = absoluteDet n k A := (abs_of_pos hpos).symm
    _ = _ := absoluteDet_eq_clipped_of_not_bad n hg hk A hA

lemma signed_clipping_smallness_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (2 / (g / 2) ^ 2) *
        Real.sqrt ((stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (gapBad n g)) ≤ 1 / 4 := by
  have htail := GOEEdgeConcentration.gaussian_edge_tail_tendsto (by positivity : 0 < g / 4)
  have htail' : Tendsto (fun n : ℕ => Real.exp (-(n + 1 : ℝ) * g ^ 2 / (16 * Real.pi ^ 2)))
      atTop (𝓝 0) := by
    convert htail using 1
    funext n
    congr 1
    ring
  have hsmall := htail'.sqrt.const_mul (Real.exp (2 / (g / 2) ^ 2))
  simp only [Real.sqrt_zero, mul_zero] at hsmall
  filter_upwards [gapBad_exponential_eventually hg,
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with n hprob hsmall
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprob) (Real.exp_pos _).le).trans hsmall.le

/-- Actual signed and absolute determinant expectations are comparable for
all sufficiently large dimensions, uniformly over every real shift above the gap. -/
theorem signed_absolute_expectations_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + g ≤ k →
      Integrable (signedDet n k) (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ∧
      0 < ∫ A, signedDet n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) ∧
      (∫ A, Real.exp (clippedTrace n k (g / 2) A)
          ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤
        2 * ∫ A, signedDet n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) ∧
      (∫ A, absoluteDet n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤
        2 * ∫ A, signedDet n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) := by
  filter_upwards [signed_clipping_smallness_eventually hg] with n hsmall
  intro k hk
  have hrho : 0 < g / 2 := by positivity
  have h := signed_exponential_expectation_comparison
    (μ := stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    (clippedTrace n k (g / 2)) (signedDet n k) (clippedTrace_integrable n k hrho)
    (signedDet_measurable n k).aemeasurable (2 / (g / 2) ^ 2).toNNReal
    (GOESharpMoments.clippedTrace_centered_sharpGaussian n k hrho)
    (gapBad n g) (gapBad_measurable n g)
    (ae_of_all _ (fun A => absoluteDet_le_exp_clippedTrace n k hrho A))
    (ae_of_all _ (fun A hA => signedDet_eq_clipped_of_not_bad n hg hk A hA))
    (by rw [Real.coe_toNNReal _ (by positivity)]; exact hsmall)
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end
end SlowEquilibration.GOESignedAbsoluteTransfer
