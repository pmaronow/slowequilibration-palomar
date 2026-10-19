-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalNormalizedMoments
public import SlowEquilibration.GaussianSpectralNorm
public import SlowEquilibration.DeterminantHolder

/-! Genuine determinant-weighted exclusion of nonmaximum GOE Hessians. -/
@[expose] public section
namespace SlowEquilibration.GOEMaximumDeterminant
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics GOEEdgeConcentration GOEClippedDeterminants GOEScaling
open GOERawMoments GOEPhysicalPotential GOEPhysicalNormalizedMoments
open OAI.CriticalSK
open scoped Topology ENNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def maximumEvent (n : ℕ) (k : ℝ) : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  {W | eigenvalues n W 0 < k}

lemma maximumEvent_measurable (n : ℕ) (k : ℝ) : MeasurableSet (maximumEvent n k) :=
  measurableSet_lt ((measurable_pi_apply 0).comp (eigenvalues_measurable n)) measurable_const

def maximumMean (n N : ℕ) (b k : ℝ) : ℝ :=
  ∫ W in maximumEvent n k, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n+1) N b

lemma symmetric_eigenvalue_abs_le_opNorm {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    |matrixOrderedEigenvalues A i| ≤ ‖gaussianMatrixCLM A‖ := by
  rw [matrixOrderedEigenvalues_eq A hA]
  let h := gaussianMatrixCLM_symmetric A hA
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := h.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := h.eigenvectorBasis hn |>.norm_eq_one i
  have he : gaussianMatrixCLM A v = h.eigenvalues hn i • v := h.apply_eigenvectorBasis hn i
  have hh := (gaussianMatrixCLM A).le_opNorm v
  rw [he, norm_smul, Real.norm_eq_abs, hv, mul_one, mul_one] at hh
  exact hh

lemma realized_operator_norm_le_radius (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n+1)) :
    ‖gaussianMatrixCLM (symmetrizeGaussianMatrix (goeScale n) A)‖ ≤ realizedRadius n A := by
  have hA := symmetrize_symmetric (goeScale n) A
  apply GaussianSpectralNorm.symmetric_norm_le_of_eigenvalues _
    (gaussianMatrixCLM_symmetric _ hA) (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1)
    ((abs_nonneg _).trans (abs_eigenvalue_le_realizedRadius n A 0))
  intro i
  have h := abs_eigenvalue_le_realizedRadius n A i
  simpa only [realizedEigenvalues, matrixOrderedEigenvalues_eq _ hA] using h

lemma scaled_largest_le_radius (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 < b)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) :
    eigenvalues n (scaleFactor n N b • GOEDeterminantMoments.realization n A) 0 ≤
      scaleFactor n N b * realizedRadius n A := by
  let B := symmetrizeGaussianMatrix (goeScale n) A
  have hB : ∀ i j, B i j = B j i := symmetrize_symmetric (goeScale n) A
  have hS : ∀ i j, (scaleFactor n N b • B) i j = (scaleFactor n N b • B) j i := by
    intro i j
    change scaleFactor n N b * B i j = scaleFactor n N b * B j i
    rw [hB i j]
  have he : matrixToGaussian (scaleFactor n N b • GOEDeterminantMoments.realization n A) =
      scaleFactor n N b • B := by
    rw [matrixToGaussian_scalar, GOEDeterminantMoments.realization, matrixToGaussian_gaussianToMatrix]
  change matrixOrderedEigenvalues _ 0 ≤ _
  rw [he]
  calc
    _ ≤ |matrixOrderedEigenvalues (scaleFactor n N b • B) 0| := le_abs_self _
    _ ≤ ‖gaussianMatrixCLM (scaleFactor n N b • B)‖ := symmetric_eigenvalue_abs_le_opNorm _ hS 0
    _ = scaleFactor n N b * ‖gaussianMatrixCLM B‖ := by
      rw [show gaussianMatrixCLM (scaleFactor n N b • B) = scaleFactor n N b • gaussianMatrixCLM B from
        (gaussianMatrixToCLM (n+1)).map_smul _ B, norm_smul, Real.norm_eq_abs,
        abs_of_pos (scaleFactor_pos n hN hb)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (realized_operator_norm_le_radius n A)
      (scaleFactor_pos n hN hb).le

/-- Actual physical GOE edge exclusion, uniform in all exterior shifts. -/
theorem nonmaximum_probability_eventually {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k →
      (SphericalGaussianJet.goeLaw (n+1) (n+2) b).real (maximumEvent n k)ᶜ ≤
        Real.exp (-(n+1 : ℝ) * (g / Real.sqrt b)^2 / (16 * Real.pi^2)) := by
  have hs := Real.sqrt_pos.mpr hb
  filter_upwards [gapBad_exponential_eventually (div_pos hg hs)] with n hn
  intro k hk
  have hmap : Measurable (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
      scaleFactor n (n+2) b • GOEDeterminantMoments.realization n A) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    change Measurable (fun A => scaleFactor n (n+2) b * GOEDeterminantMoments.realization n A i j)
    exact measurable_const.mul ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (GOEDeterminantMoments.realization_measurable n)))
  rw [← scaled_realization_law n (by omega : 0 < n+2) hb.le, Measure.real,
    Measure.map_apply hmap (maximumEvent_measurable n k).compl]
  have hsub : (fun A => scaleFactor n (n+2) b • GOEDeterminantMoments.realization n A) ⁻¹'
      (maximumEvent n k)ᶜ ⊆ gapBad n (g / Real.sqrt b) := by
    intro A hA
    by_contra hbad
    have hrad : realizedRadius n A ≤ 2 + (g / Real.sqrt b)/2 := le_of_not_gt hbad
    have htop := scaled_largest_le_radius n (by omega : 0 < n+2) hb A
    have hscale := scaleFactor_le_sqrt (n := n) (N := n+2) (by omega) (by omega) hb.le
    have hupper : scaleFactor n (n+2) b * realizedRadius n A ≤ 2*Real.sqrt b+g/2 := by
      calc
        _ ≤ scaleFactor n (n+2) b * (2+(g/Real.sqrt b)/2) :=
          mul_le_mul_of_nonneg_left hrad (scaleFactor_pos n (by omega) hb).le
        _ ≤ Real.sqrt b * (2+(g/Real.sqrt b)/2) :=
          mul_le_mul_of_nonneg_right hscale (by positivity)
        _ = _ := by field_simp
    have hge : k ≤ eigenvalues n (scaleFactor n (n+2) b • GOEDeterminantMoments.realization n A) 0 :=
      le_of_not_gt hA
    linarith
  exact (measureReal_mono hsub).trans hn

lemma determinant_event_holder {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (D : Ω → ℝ)
    (hD : Integrable D ν) (hDn : ∀ᵐ x ∂ν, 0 ≤ D x)
    (hm : 0 < ∫ x, D x ∂ν) (B : Set Ω) (hB : MeasurableSet B)
    {C q : ℝ} (hM : Integrable (fun x => (D x / (∫ y, D y ∂ν)) ^ (2:ℝ)) ν)
    (hMC : (∫ x, (D x / (∫ y, D y ∂ν)) ^ (2:ℝ) ∂ν) ≤ C)
    (hq : ν.real B ≤ q) :
    (∫ x in B, D x ∂ν) / (∫ x, D x ∂ν) ≤ Real.sqrt C * Real.sqrt q := by
  have hφ : AEStronglyMeasurable (B.indicator (fun _ => (1:ℝ))) ν :=
    (measurable_const.indicator hB).aestronglyMeasurable
  have hφb : ∀ᵐ x ∂ν, 0 ≤ B.indicator (fun _ => (1:ℝ)) x ∧
      B.indicator (fun _ => (1:ℝ)) x ≤ 1 := .of_forall fun x => by
    by_cases hx : x ∈ B <;> simp [hx]
  have hφm : (∫ x, B.indicator (fun _ => (1:ℝ)) x ∂ν) ≤ q := by
    rw [integral_indicator hB]
    simpa using hq
  have hh := determinant_weighted_holder ν D _ hD hDn hm hφ hφb
    (by norm_num : (1:ℝ)<2) hM hMC hφm
  have he : (∫ x, D x * B.indicator (fun _ => (1:ℝ)) x ∂ν) = ∫ x in B, D x ∂ν := by
    rw [← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [he] at hh
  convert hh using 1
  norm_num [Real.sqrt_eq_rpow]

/-- The actual excluded determinant weight is at most half its own ordinary
mean, uniformly over the whole fixed exterior radial interval. -/
theorem excluded_determinant_weight_eventually {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2 * Real.sqrt b + g) Z,
      (∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
        ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b) ≤ physicalMean n (n+2) b k / 2 := by
  obtain ⟨C,hC,hmom⟩ := normalized_physical_moments 1 (b := b) (g := g) (Z := Z)
    (r := 2) hb hg (by norm_num)
  have htail := gaussian_edge_tail_tendsto (by positivity : 0 < (g / Real.sqrt b)/4)
  have htail' : Tendsto (fun n : ℕ =>
      Real.exp (-(n+1 : ℝ) * (g / Real.sqrt b)^2 / (16 * Real.pi^2))) atTop (𝓝 0) := by
    convert htail using 1
    funext n
    congr 1
    ring
  have hsmall := htail'.sqrt.const_mul (Real.sqrt C)
  simp only [Real.sqrt_zero, mul_zero] at hsmall
  filter_upwards [nonmaximum_probability_eventually hb hg,
    hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with n hprob hsmall
  intro k hk
  obtain ⟨hD,hm,hM,hMC⟩ := hmom n k hk.1 hk.2
  have hh := determinant_event_holder (SphericalGaussianJet.goeLaw (n+1) (n+2) b)
    (matrixAbsoluteDet n k) hD (.of_forall fun _ => abs_nonneg _) hm
    _ (maximumEvent_measurable n k).compl hM hMC (hprob k hk.1)
  have hu := hh.trans hsmall.le
  apply (div_le_iff₀ hm).mp hu |>.trans_eq
  ring

/-- The literal determinant mean on negative-spectrum Hessians is comparable
to the genuine ordinary absolute determinant mean, with constants 1/2 and 1. -/
theorem maximumMean_comparison_eventually {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc (2 * Real.sqrt b + g) Z,
      physicalMean n (n+2) b k / 2 ≤ maximumMean n (n+2) b k ∧
        maximumMean n (n+2) b k ≤ physicalMean n (n+2) b k := by
  obtain ⟨C,hC,hmom⟩ := normalized_physical_moments 1 (b := b) (g := g) (Z := Z)
    (r := 2) hb hg (by norm_num)
  filter_upwards [excluded_determinant_weight_eventually (Z := Z) hb hg] with n hn
  intro k hk
  have hD := (hmom n k hk.1 hk.2).1
  have he := integral_add_compl (maximumEvent_measurable n k) hD
  have hb0 : 0 ≤ ∫ W in (maximumEvent n k)ᶜ, matrixAbsoluteDet n k W
      ∂SphericalGaussianJet.goeLaw (n+1) (n+2) b := integral_nonneg fun _ => abs_nonneg _
  have hh := hn k hk
  change physicalMean n (n+2) b k/2 ≤ _ ∧ _ ≤ physicalMean n (n+2) b k
  dsimp only [maximumMean, physicalMean] at *
  constructor <;> linarith

end
end SlowEquilibration.GOEMaximumDeterminant
