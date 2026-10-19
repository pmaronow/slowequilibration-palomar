-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEScaling
public import SlowEquilibration.RareEventMomentTransfer
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

/-!
# Sharp actual ordinary GOE determinant moments

The literal absolute determinant is normalized by its actual own expectation.
The exact clipped logarithm, proved Gaussian concentration and actual spectral
edge failure bound supply the argument. No regularized determinant is used.
-/

namespace SlowEquilibration.GOESharpMoments

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics GOEEdgeConcentration GOEClippedDeterminants GOEScaling
open scoped NNReal ENNReal Topology BigOperators

theorem clippedTrace_centered_sharpGaussian (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    HasSubgaussianMGF
      (fun A => clippedTrace n k rho A -
        ∫ B, clippedTrace n k rho B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      (2 / rho ^ 2).toNNReal (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) := by
  let I := Sigma (fun _ : Fin (n + 1) => Fin (n + 1))
  let e : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] GOEAsymptotics.GaussianMatrix (n + 1) :=
    LinearIsometryEquiv.piLpCurry ℝ 2 (fun _ : Fin (n + 1) => fun _ : Fin (n + 1) => ℝ)
  have hL : 0 < (clippedLip n rho : ℝ) := by
    have hs := clippedLip_square n hrho
    have hn := (clippedLip n rho).coe_nonneg
    have hp : (0 : ℝ) < 2 / rho ^ 2 := by positivity
    nlinarith
  have hLip : LipschitzWith (clippedLip n rho) (fun x : EuclideanSpace ℝ I => clippedTrace n k rho (e x)) := by
    simpa only [mul_one, Function.comp_def] using (clippedTrace_lipschitz n k hrho).comp e.lipschitzWith
  have h := SYK.product_standardGaussian_hasSubgaussianMGF
    (fun x : EuclideanSpace ℝ I => clippedTrace n k rho (e x)) (clippedLip n rho) hL
    (by simpa only [Real.toNNReal_coe] using hLip)
  have hμ : SYK.standardGaussianMeasureOnEuclidean I = stdGaussian (EuclideanSpace ℝ I) := map_pi_eq_stdGaussian
  rw [hμ, clippedLip_square n hrho] at h
  have hmap : (stdGaussian (EuclideanSpace ℝ I)).map e =
      stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) := stdGaussian_map e
  have hmean : (∫ x, clippedTrace n k rho (e x) ∂stdGaussian (EuclideanSpace ℝ I)) =
      ∫ x, clippedTrace n k rho x ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) := by
    rw [← hmap, integral_map e.continuous.measurable.aemeasurable
      (clippedTrace_lipschitz n k hrho).continuous.aestronglyMeasurable]
  rw [hmean] at h
  have hID : IdentDistrib (fun x : EuclideanSpace ℝ I => e x)
      (fun x : GOEAsymptotics.GaussianMatrix (n + 1) => x)
      (stdGaussian (EuclideanSpace ℝ I)) (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) :=
    ⟨e.continuous.measurable.aemeasurable, measurable_id.aemeasurable, by
      change (stdGaussian (EuclideanSpace ℝ I)).map e =
        (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).map id
      rw [Measure.map_id]
      exact hmap⟩
  apply h.congr_identDistrib
  simpa only [Function.comp_def] using hID.comp
    (u := fun A => clippedTrace n k rho A -
      ∫ B, clippedTrace n k rho B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    ((clippedTrace_lipschitz n k hrho).continuous.sub continuous_const).measurable

lemma clipping_smallness_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (2 / (g / 2) ^ 2) *
        Real.sqrt ((stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (gapBad n g)) ≤ 1 / 2 := by
  have htail := gaussian_edge_tail_tendsto (by positivity : 0 < g / 4)
  have htail' : Tendsto (fun n : ℕ => Real.exp (-(n + 1 : ℝ) * g ^ 2 / (16 * Real.pi ^ 2)))
      atTop (𝓝 0) := by
    convert htail using 1
    funext n
    congr 1
    ring
  have hsmall := htail'.sqrt.const_mul (Real.exp (2 / (g / 2) ^ 2))
  simp only [Real.sqrt_zero, mul_zero] at hsmall
  filter_upwards [gapBad_exponential_eventually hg,
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hprob hsmall
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprob) (Real.exp_pos _).le).trans hsmall.le

/-- Uniform in every real shift above the fixed gap. Actual expectation
positivity and moment integrability are part of the result. -/
theorem raw_absoluteDet_normalized_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + g ≤ k →
      Integrable (absoluteDet n k) (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ∧
      0 < ∫ A, absoluteDet n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) ∧
      ∀ r : ℝ, 0 ≤ r →
        Integrable (fun A => (absoluteDet n k A /
          (∫ B, absoluteDet n k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r)
          (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ∧
        (∫ A, (absoluteDet n k A /
          (∫ B, absoluteDet n k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r
            ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤
          (2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / g ^ 2) := by
  filter_upwards [clipping_smallness_eventually hg] with n hsmall
  intro k hk
  have hrho : 0 < g / 2 := by positivity
  have h := RareEventMomentTransfer.normalized_dominated_exponential_moments
    (μ := stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    (clippedTrace n k (g / 2)) (absoluteDet n k) (clippedTrace_integrable n k hrho)
    (absoluteDet_measurable n k).aemeasurable (2 / (g / 2) ^ 2).toNNReal
    (clippedTrace_centered_sharpGaussian n k hrho) (gapBad n g) (gapBad_measurable n g)
    (ae_of_all _ (fun A => ⟨absoluteDet_nonneg n k A, absoluteDet_le_exp_clippedTrace n k hrho A⟩))
    (ae_of_all _ (fun A hA => absoluteDet_eq_clipped_of_not_bad n hg hk A hA))
    (by rw [Real.coe_toNNReal _ (by positivity)]; exact hsmall)
  refine ⟨h.1, h.2.2.1, fun r hr => ⟨(h.2.2.2 r hr).1, ?_⟩⟩
  have hb := (h.2.2.2 r hr).2
  rw [Real.coe_toNNReal _ (by positivity)] at hb
  exact hb.trans_eq (by congr 1; congr 1; ring)

/-- The source also needs the clipped exponential divided by the ordinary
absolute determinant's own expectation. This is that literal normalization. -/
theorem clipped_over_raw_normalized_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + g ≤ k → ∀ r : ℝ, 0 ≤ r →
      Integrable (fun A => (Real.exp (clippedTrace n k (g / 2) A) /
        (∫ B, absoluteDet n k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r)
        (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ∧
      (∫ A, (Real.exp (clippedTrace n k (g / 2) A) /
        (∫ B, absoluteDet n k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r
          ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤
        (2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / g ^ 2) := by
  filter_upwards [clipping_smallness_eventually hg] with n hsmall
  intro k hk r hr
  have hrho : 0 < g / 2 := by positivity
  have h := RareEventMomentTransfer.normalized_upper_exponential_moments
    (μ := stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    (clippedTrace n k (g / 2)) (absoluteDet n k) (clippedTrace_integrable n k hrho)
    (absoluteDet_measurable n k).aemeasurable (2 / (g / 2) ^ 2).toNNReal
    (clippedTrace_centered_sharpGaussian n k hrho) (gapBad n g) (gapBad_measurable n g)
    (ae_of_all _ (fun A => ⟨absoluteDet_nonneg n k A, absoluteDet_le_exp_clippedTrace n k hrho A⟩))
    (ae_of_all _ (fun A hA => absoluteDet_eq_clipped_of_not_bad n hg hk A hA))
    (by rw [Real.coe_toNNReal _ (by positivity)]; exact hsmall) r hr
  refine ⟨h.1, ?_⟩
  have hb := h.2
  rw [Real.coe_toNNReal _ (by positivity)] at hb
  exact hb.trans_eq (by congr 1; congr 1; ring)

/-- The two source determinant moments are ordered by actual pointwise
clipping domination; the exponent may be any nonnegative real number. -/
theorem raw_le_clipped_normalized_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + g ≤ k → ∀ r : ℝ, 0 ≤ r →
      (∫ A, (absoluteDet n k A /
        (∫ B, absoluteDet n k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r
          ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤
      (∫ A, (Real.exp (clippedTrace n k (g / 2) A) /
        (∫ B, absoluteDet n k B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))) ^ r
          ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) := by
  filter_upwards [raw_absoluteDet_normalized_eventually hg, clipped_over_raw_normalized_eventually hg]
    with n hraw hclip
  intro k hk r hr
  apply integral_mono (hraw k hk |>.2.2 r hr).1 (hclip k hk r hr).1
  intro A
  have hpos := (hraw k hk).2.1
  apply Real.rpow_le_rpow (div_nonneg (absoluteDet_nonneg n k A) hpos.le) _ hr
  exact div_le_div_of_nonneg_right (absoluteDet_le_exp_clippedTrace n k (by positivity) A) hpos.le

def matrixAbsoluteDet (n : ℕ) (k : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  |(k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W).det|

lemma matrixAbsoluteDet_measurable (n : ℕ) (k : ℝ) : Measurable (matrixAbsoluteDet n k) := by
  unfold matrixAbsoluteDet
  fun_prop

@[simp] lemma matrixAbsoluteDet_realization (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    matrixAbsoluteDet n k (GOEDeterminantMoments.realization n A) = absoluteDet n k A := rfl

/-- The same actual ordinary determinant bound under the literal Matrix GOE law. -/
theorem standard_goe_determinant_moments_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + g ≤ k →
      Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ∧
      0 < ∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1 ∧
      ∀ r : ℝ, 0 ≤ r →
        Integrable (fun W => (matrixAbsoluteDet n k W /
          (∫ V, matrixAbsoluteDet n k V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) ^ r)
          (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ∧
        (∫ W, (matrixAbsoluteDet n k W /
          (∫ V, matrixAbsoluteDet n k V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) ^ r
            ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ≤
          (2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / g ^ 2) := by
  filter_upwards [raw_absoluteDet_normalized_eventually hg] with n hn
  intro k hk
  have hraw := hn k hk
  have hm := GOEDeterminantMoments.realization_measurable n
  have hd := matrixAbsoluteDet_measurable n k
  have hmean : (∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) =
      ∫ A, absoluteDet n k A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) := by
    rw [← GOEDeterminantMoments.realization_law n, integral_map hm.aemeasurable hd.aestronglyMeasurable]
    rfl
  refine ⟨?_, by rw [hmean]; exact hraw.2.1, ?_⟩
  · rw [← GOEDeterminantMoments.realization_law n]
    exact (integrable_map_measure hd.aestronglyMeasurable hm.aemeasurable).mpr hraw.1
  · intro r hr
    have hfn : Measurable (fun W => (matrixAbsoluteDet n k W /
        (∫ V, matrixAbsoluteDet n k V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) ^ r) :=
      (hd.div_const _).pow_const r
    rw [hmean] at hfn ⊢
    refine ⟨?_, ?_⟩
    · rw [← GOEDeterminantMoments.realization_law n]
      exact (integrable_map_measure hfn.aestronglyMeasurable hm.aemeasurable).mpr (hraw.2.2 r hr).1
    · rw [← GOEDeterminantMoments.realization_law n, integral_map hm.aemeasurable hfn.aestronglyMeasurable]
      exact (hraw.2.2 r hr).2

lemma matrixAbsoluteDet_scaled (n : ℕ) {a : ℝ} (ha : 0 < a) (k : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    matrixAbsoluteDet n k (a • W) = a ^ (n + 1) * matrixAbsoluteDet n (k / a) W :=
  absolute_determinant_scale ha k W

/-- Uniform actual ordinary determinant moments for the literal variance
`b/N` GOE law, allowing every matrix dimension not exceeding the ambient one.
The constants depend only on the fixed physical gap and variance, not on the
shift, dimension, or ambient normalization. -/
theorem goe_determinant_moments_eventually {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n + 1 ≤ N → ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k →
      Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n + 1) N b) ∧
      0 < ∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) N b ∧
      ∀ r : ℝ, 0 ≤ r →
        Integrable (fun W => (matrixAbsoluteDet n k W /
          (∫ V, matrixAbsoluteDet n k V ∂SphericalGaussianJet.goeLaw (n + 1) N b)) ^ r)
          (SphericalGaussianJet.goeLaw (n + 1) N b) ∧
        (∫ W, (matrixAbsoluteDet n k W /
          (∫ V, matrixAbsoluteDet n k V ∂SphericalGaussianJet.goeLaw (n + 1) N b)) ^ r
            ∂SphericalGaussianJet.goeLaw (n + 1) N b) ≤
          (2 : ℝ) ^ r * Real.exp (4 * b * r ^ 2 / g ^ 2) := by
  have hB := Real.sqrt_pos.mpr hb
  filter_upwards [standard_goe_determinant_moments_eventually (div_pos hg hB)] with n hn
  intro N hmN k hk
  have hN : 0 < N := by omega
  let a := scaleFactor n N b
  have ha : 0 < a := scaleFactor_pos n hN hb
  have hap : 0 < a ^ (n + 1) := pow_pos ha _
  have hstd := hn (k / a) (scaled_shift_gap hN hmN hb hg hk)
  have hmap : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => a • W) := by fun_prop
  have hd := matrixAbsoluteDet_measurable n k
  have hmean : (∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) N b) =
      a ^ (n + 1) * (∫ W, matrixAbsoluteDet n (k / a) W ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) := by
    rw [← goeLaw_scale n hN hb.le, integral_map hmap.aemeasurable hd.aestronglyMeasurable]
    simp only [matrixAbsoluteDet_scaled n ha k]
    exact integral_const_mul _ _
  have hint : Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n + 1) N b) := by
    rw [← goeLaw_scale n hN hb.le]
    apply (integrable_map_measure hd.aestronglyMeasurable hmap.aemeasurable).mpr
    convert hstd.1.const_mul (a ^ (n + 1)) using 1
    funext W
    exact matrixAbsoluteDet_scaled n ha k W
  have hpos : 0 < ∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) N b := by
    rw [hmean]
    exact mul_pos hap hstd.2.1
  refine ⟨hint, hpos, ?_⟩
  intro r hr
  have hratio (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      matrixAbsoluteDet n k (a • W) /
        (a ^ (n + 1) * (∫ V, matrixAbsoluteDet n (k / a) V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1)) =
      matrixAbsoluteDet n (k / a) W /
        (∫ V, matrixAbsoluteDet n (k / a) V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) := by
    rw [matrixAbsoluteDet_scaled n ha k]
    exact mul_div_mul_left _ _ hap.ne'
  have hfn : Measurable (fun W => (matrixAbsoluteDet n k W /
      (a ^ (n + 1) * (∫ V, matrixAbsoluteDet n (k / a) V ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1))) ^ r) :=
    (hd.div_const _).pow_const r
  rw [hmean]
  refine ⟨?_, ?_⟩
  · rw [← goeLaw_scale n hN hb.le]
    apply (integrable_map_measure hfn.aestronglyMeasurable hmap.aemeasurable).mpr
    simpa only [Function.comp_def, hratio] using (hstd.2.2 r hr).1
  · rw [← goeLaw_scale n hN hb.le, integral_map hmap.aemeasurable hfn.aestronglyMeasurable]
    simp only [hratio]
    have hbound := (hstd.2.2 r hr).2
    exact hbound.trans_eq (by
      congr 1
      congr 1
      rw [div_pow, Real.sq_sqrt hb.le]
      field_simp)

end
end SlowEquilibration.GOESharpMoments
