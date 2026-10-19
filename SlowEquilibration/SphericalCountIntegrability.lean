-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.IntrinsicHessianLaw
public import SlowEquilibration.SphericalWindowGeometry
public import SlowEquilibration.GOEPrincipalMinors
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Genuine finite expected total critical count. The unrestricted radial
Gaussian shift is retained; no outside-edge truncation or count integrability
premise is used. -/

@[expose] public section

namespace SlowEquilibration.SphericalCountIntegrability

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.SphericalForm
open SlowEquilibration.SphereHessian SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.SphericalKacRiceGluing SlowEquilibration.SphericalIntrinsicKacRice
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalIntrinsicChartKacRice
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- Every literal entry of the independent-upper-entry GOE has all finite
moments, including at singular or zero covariance. -/
lemma goe_entry_memLp (n N : ℕ) (b : ℝ) (i j : Fin n)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun W : Matrix (Fin n) (Fin n) ℝ => W i j) p (goeLaw n N b) := by
  unfold goeLaw
  rw [memLp_map_measure_iff (g := fun W : Matrix (Fin n) (Fin n) ℝ => W i j)
    (Matrix.measurable_apply (i := i) (j := j)).aestronglyMeasurable
    (symmetricMatrix_measurable n).aemeasurable]
  change MemLp (fun x => symmetricMatrix x i j) p _
  unfold symmetricMatrix
  split_ifs with hij
  · exact (memLp_id_gaussianReal' p hp).comp_measurePreserving
      (measurePreserving_eval (fun ij : UpperIndex n => gaussianReal 0
        ((b / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal) ⟨(i,j), hij⟩)
  · exact (memLp_id_gaussianReal' p hp).comp_measurePreserving
      (measurePreserving_eval (fun ij : UpperIndex n => gaussianReal 0
        ((b / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal)
        ⟨(j,i), le_of_lt (lt_of_not_ge hij)⟩)

/-- The genuine finite-dimensional determinant polynomial is integrable under
an independent real Gaussian radial shift and the actual matrix GOE law. -/
lemma shifted_gaussian_determinant_integrable (n N : ℕ) (b : ℝ) (v : ℝ≥0) :
    Integrable (fun p : ℝ × Matrix (Fin n) (Fin n) ℝ =>
      (p.2 - (p.1 / (N : ℝ)) • 1).det) ((gaussianReal 0 v).prod (goeLaw n N b)) := by
  simp_rw [Matrix.det_apply']
  apply integrable_finsetSum
  intro σ hσ
  apply Integrable.const_mul
  apply GOEPrincipalMinors.integrable_product_of_all_moments
  intro i hi p hp
  have hW := (goe_entry_memLp n N b (σ i) i hp).comp_snd (gaussianReal 0 v)
  have hR := ((memLp_id_gaussianReal' (μ := 0) (v := v) p hp).comp_fst (goeLaw n N b)).mul_const (N : ℝ)⁻¹
  convert hW.sub (hR.mul_const ((1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i)) using 1
  funext x
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, id_eq]
  rfl

/-- The actual radial derivative law is the same at every sphere point. -/
lemma radial_law (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (disorderLaw (n+1) μ.maxDegree).map (jet c 1 x (fun _ => x)) =
      gaussianReal 0 (((n+1 : ℕ) : ℝ) * (Q * μ.xi1 Q + Q^2 * μ.xi2 Q)).toNNReal := by
  dsimp only
  rw [(jet_hasGaussianLaw _ 1 x (fun _ => x)).map_eq_gaussianReal, jet_mean]
  congr 2
  have h := (center_value_radial_covariances (by omega) μ hQ x hx).2.2
  rw [covariance_self (jet_hasGaussianLaw _ 1 x (fun _ => x)).aemeasurable] at h
  exact h

/-- The point-independent full law governing the unconditioned radial score
and its independent actual full tangent GOE matrix. -/
def radialMatrixLaw (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measure (ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (gaussianReal 0 (((n+1 : ℕ) : ℝ) * (Q * μ.xi1 Q + Q^2 * μ.xi2 Q)).toNNReal).prod
    (goeLaw n (n+1) (Q^2 * μ.xi2 Q))

def shiftedDeterminant (n : ℕ) (p : ℝ × Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  |(p.2 - (p.1 / (n+1 : ℕ)) • 1).det|

lemma shiftedDeterminant_measurable (n : ℕ) : Measurable (shiftedDeterminant n) := by
  exact (continuous_snd.sub ((continuous_fst.div_const _).smul continuous_const)).matrix_det.abs.measurable

lemma shiftedDeterminant_integrable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Integrable (shiftedDeterminant n) (radialMatrixLaw n μ Q) :=
  (shifted_gaussian_determinant_integrable n (n+1) _ _).abs

/-- Exact unrestricted zero-gradient radial/GOE product law, pointwise in the
sphere point under the canonical whole-disorder zero kernel. -/
lemma zeroKernel_radial_goe_law (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (coefficientKernel (intrinsicGamma c x) 0).map
      (fun J => (jet c 1 x (fun _ => x) J, hessianMatrix c x (tangentFrame x hx) J)) =
      radialMatrixLaw n μ Q := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let f : ((Option (Fin 1) → ℝ) × Matrix (Fin n) (Fin n) ℝ) →
      ℝ × Matrix (Fin n) (Fin n) ℝ := Prod.map (fun a => a (some 0)) id
  have hf : Measurable f := (measurable_pi_apply (some 0)).prodMap measurable_id
  have hj : Measurable (fun J : Disorder (n+1) μ.maxDegree =>
      (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x (tangentFrame x hx) J)) := by
    convert (scoreHessianDecode_measurable n).comp
      ((scoreHessianCLM c x (tangentFrame x hx)).continuous.measurable.comp
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate (n+1) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable _ _))) using 1
    funext J
    exact (scoreHessianDecode_actual c x (tangentFrame x hx) J).symm
  have h := congrArg (fun m => m.map f) (zeroKernel_score_goe_product (by omega) c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x hx
    (tangentFrame x hx) (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
  rw [Measure.map_map hf hj, ← Measure.map_prod_map _ _ (measurable_pi_apply (some 0)) measurable_id,
    Measure.map_id] at h
  have hscore : Measurable (valueGradient c x (fun _ : Fin 1 => x)) := by
    apply Measurable.of_eval
    intro i
    cases i with
    | none =>
      convert (jetCLM c 0 x (fun i => Fin.elim0 i)).continuous.measurable using 1
      funext J
      exact (jetCLM_apply _ _ _ _ J).symm
    | some i =>
      convert (jetCLM c 1 x (fun _ => x)).continuous.measurable using 1
      funext J
      exact (jetCLM_apply _ _ _ _ J).symm
  rw [Measure.map_map (measurable_pi_apply (some 0)) hscore] at h
  change _ = ((disorderLaw (n+1) μ.maxDegree).map (jet c 1 x (fun _ => x))).prod
    (goeLaw n (n+1) (secondCovariance c 1)) at h
  rw [radial_law n μ hQ.le x hx, secondCovariance_center, secondCovariance_mixture] at h
  exact h

/-- Finite, point-independent unrestricted conditional intrinsic determinant
mean. This quantity is defined by its ordinary absolutely integrable Gaussian
polynomial expectation. -/
def zeroGradientMean (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  ∫ p, shiftedDeterminant n p ∂radialMatrixLaw n μ Q

lemma zeroGradientMean_nonneg (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    0 ≤ zeroGradientMean n μ Q := integral_nonneg fun _ => abs_nonneg _

lemma zeroGradient_intrinsic_det_law (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (fun J => |(intrinsicHessian (field c J) x).det|)
      ((radialMatrixLaw n μ Q).map (shiftedDeterminant n))
      (coefficientKernel (intrinsicGamma c x) 0) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hpairMeas : Measurable (fun J : Disorder (n+1) μ.maxDegree =>
      (jet c 1 x (fun _ => x) J, hessianMatrix c x (tangentFrame x hx) J)) := by
    apply Measurable.prodMk
    · convert (jetCLM c 1 x (fun _ => x)).continuous.measurable using 1
      funext J
      exact (jetCLM_apply _ _ _ _ J).symm
    · apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      convert (jetCLM c 2 x ![tangentFrame x hx i, tangentFrame x hx j]).continuous.measurable using 1
      funext J
      exact (jetCLM_apply _ _ _ _ J).symm
  have hpair : HasLaw (fun J => (jet c 1 x (fun _ => x) J,
      hessianMatrix c x (tangentFrame x hx) J)) (radialMatrixLaw n μ Q)
      (coefficientKernel (intrinsicGamma c x) 0) :=
    ⟨hpairMeas.aemeasurable, zeroKernel_radial_goe_law n μ hQ x hx⟩
  have h := (hasLaw_map (shiftedDeterminant_measurable n).aemeasurable).comp hpair
  apply h.congr
  exact Filter.Eventually.of_forall fun J => by
    change |(intrinsicHessian (field c J) x).det| = _
    rw [intrinsicHessian_det c J x hx]
    rfl

/-- Genuine uniform finite zero-gradient intrinsic determinant integral,
including unrestricted radial shifts and both pure and nonpure mixtures. -/
theorem zeroGradient_intrinsic_det_lintegral (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det|
      ∂coefficientKernel (intrinsicGamma c x) 0) = ENNReal.ofReal (zeroGradientMean n μ Q) := by
  dsimp only
  have h := zeroGradient_intrinsic_det_law n μ hQ x hx
  rw [h.lintegral_comp (by fun_prop), lintegral_map (by fun_prop) (shiftedDeterminant_measurable n)]
  exact (ofReal_integral_eq_lintegral_ofReal (shiftedDeterminant_integrable n μ Q)
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm

/-- Finite expected TOTAL true critical count on the actual sphere. This is
derived from the unrestricted Gaussian determinant polynomial and global KR,
rather than from almost sure finiteness alone. -/
theorem actual_sphere_total_count_lintegral_lt_top (n : ℕ) (hn : 1 ≤ n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualSphereCount n c (fun _ _ => 1) J ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
  dsimp only
  rw [actual_sphere_marked_kacRice_explicit n hn μ hQ (fun _ _ => 1) measurable_const]
  simp only [mul_one]
  have he : (∫⁻ x, ∫⁻ J, ENNReal.ofReal |(intrinsicHessian
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) x).det|
      ∂coefficientKernel (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) 0
      ∂manuscriptRoundVolume n) = ENNReal.ofReal (zeroGradientMean n μ Q) * manuscriptRoundVolume n univ := by
    calc
      _ = ∫⁻ _x, ENNReal.ofReal (zeroGradientMean n μ Q) ∂manuscriptRoundVolume n := by
        apply lintegral_congr_ae
        filter_upwards [manuscriptRoundVolume_onSphere n] with x hx
        exact zeroGradient_intrinsic_det_lintegral n μ hQ x hx
      _ = _ := lintegral_const _
  rw [he]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr (manuscriptRoundVolume_mass_ne_top n)))

end
end SlowEquilibration.SphericalCountIntegrability
