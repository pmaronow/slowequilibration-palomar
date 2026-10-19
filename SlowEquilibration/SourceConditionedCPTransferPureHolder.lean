-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureMarkedWindows
public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.DeterminantHolder

/-! Proper pure value-and-gradient conditioning transfers the bounded
whole-field entrance mark through its determinant weight. The score window
is intersected with its exact line `(e,p*e)` and never enlarged. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureHolder

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalSequentialRegression IntrinsicHessianLaw SphereHessian
open ConditionedDeterminantMoments
open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_score_count_le_of_uniform_palm
    (d p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (ψ : Disorder (d+2) (FiniteMixture.pure p hp c hc).maxDegree →
      Vector (d+2) → ℝ≥0∞)
    (hψ : Measurable fun z : Disorder (d+2)
      (FiniteMixture.pure p hp c hc).maxDegree × Vector (d+2) => ψ z.1 z.2)
    {q : ℝ≥0∞} (hq : q ≠ ⊤)
    (hPalm : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
      (e : ℝ), pureScoreLine p e ∈ K →
      let μ := FiniteMixture.pure p hp c hc
      (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*ψ J u
        ∂pureLaw p hp c hc Q u hu e) ≤
      q*(∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)
        ∂pureLaw p hp c hc Q u hu e)) :
    let μ := FiniteMixture.pure p hp c hc
    (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q) K ψ J
      ∂disorderLaw (d+2) μ.maxDegree) ≤
      q*(∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
        ∂disorderLaw (d+2) μ.maxDegree) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  rw [(actual_pure_score_window_kacRice (d+1) (by omega) p hp c hc hQ K hK ψ hψ).2]
  rw [(actual_pure_score_window_kacRice (d+1) (by omega) p hp c hc hQ K hK
    (fun _ _ => 1) measurable_const).2]
  have hinner : (∫⁻ u, valueWindowIntensity (d+1) μ Q (pureScoreWindow p K) ψ u
      ∂sphereLaw (d+2)) ≤
      q*(∫⁻ u, valueWindowIntensity (d+1) μ Q (pureScoreWindow p K)
        (fun _ _ => 1) u ∂sphereLaw (d+2)) := by
    rw [← lintegral_const_mul' _ _ hq]
    apply lintegral_mono_ae
    filter_upwards [sphereLaw_support (by omega : 1 ≤ d+2)] with u hu
    rw [valueWindowIntensity,dite_eq_left hu,valueWindowIntensity,dite_eq_left hu]
    rw [← lintegral_const_mul' _ _ hq]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (pureScoreWindow_measurable p K hK)] with e he
    simp only [mul_one]
    have hLaw : pureLaw p hp c hc Q u hu e =
        valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e := by
      unfold pureLaw valueConditionedLaw
      congr 1
    have hpalm := hPalm u hu e he
    rw [hLaw] at hpalm
    simpa only [intrinsicDet,mul_comm,mul_left_comm,mul_assoc] using
      (mul_le_mul_left hpalm (physicalValuePdf (d+2) μ Q e))
  calc
    _ ≤ sphereKRPrefactor (d+1) μ Q *
      (q*(∫⁻ u, valueWindowIntensity (d+1) μ Q (pureScoreWindow p K)
        (fun _ _ => 1) u ∂sphereLaw (d+2))) := by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using
        mul_le_mul_left hinner (sphereKRPrefactor (d+1) μ Q)
    _ = _ := by ac_rfl

/-- One proper-pure determinant moment constant handles every dimension,
every Borel score window, and every bounded measurable whole-field mark. -/
theorem pure_critical_entrance_holder_transfer_uniform
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) {g Z r : ℝ} (hg : 0 < g) (hr : 1 < r) :
    let μ := FiniteMixture.pure p hp c hc
    ∃ Cdet : ℝ, 0 < Cdet ∧
      ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin 2))) (_hK : MeasurableSet K)
      (ψ : Disorder (d+2) μ.maxDegree → Vector (d+2) → ℝ)
      (_hψ : Measurable fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) => ψ z.1 z.2)
      (_hψ01 : ∀ J u, 0 ≤ ψ J u ∧ ψ J u ≤ 1)
      (q : ℝ) (_hq : 0 ≤ q)
      (_hgap : ∀ z ∈ K, 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 ∧ z 1 ≤ Z)
      (_hordinary : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
        (e : ℝ), pureScoreLine p e ∈ K →
        (∫ J, ψ J u ∂pureLaw p hp c hc Q u hu e) ≤ q),
      (∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K
        (fun J u => ENNReal.ofReal (ψ J u)) J ∂disorderLaw (d+2) μ.maxDegree) ≤
        ENNReal.ofReal (Cdet^(1/r)*q^(1-1/r))*
          (∫⁻ J, actualScoreWindowCount (d+1)
            (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
            ∂disorderLaw (d+2) μ.maxDegree) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  obtain ⟨Cdet,hCdet,hMom⟩ := pure_conditioned_determinant_moments
    p hp c hc hQ (Z := Z) (r := r) hg (by linarith)
  refine ⟨Cdet,hCdet,?_⟩
  intro d K hK ψ hψ hψ01 q hq hgap hordinary
  apply pure_score_count_le_of_uniform_palm d p hp c hc hQ K hK
    (fun J u => ENNReal.ofReal (ψ J u))
    (ENNReal.measurable_ofReal.comp hψ) ENNReal.ofReal_ne_top
  intro u hu e he
  let ν := pureLaw p hp c hc Q u hu e
  let D := intrinsicDet μ Q u
  let φ : Disorder (d+2) μ.maxDegree → ℝ := fun J => ψ J u
  have hν : IsProbabilityMeasure ν := by dsimp [ν,pureLaw]; infer_instance
  have hφm : Measurable φ := hψ.comp (measurable_id.prodMk measurable_const)
  have hφ01 : ∀ J, 0 ≤ φ J ∧ φ J ≤ 1 := fun J => hψ01 J u
  have hφnorm : ∀ᵐ J ∂ν, ‖φ J‖ ≤ (1:ℝ) := .of_forall fun J => by
    rw [Real.norm_of_nonneg (hφ01 J).1]
    exact (hφ01 J).2
  have hmarks : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*e ∧ (p:ℝ)*e ≤ Z := by
    simpa [pureScoreLine] using hgap (pureScoreLine p e) he
  have hm := hMom d u hu e hmarks.1 hmarks.2
  have hholder := determinant_weighted_holder ν D φ hm.1
    (.of_forall fun J => abs_nonneg _) hm.2.2.1 hφm.aestronglyMeasurable
    (.of_forall hφ01) hr hm.2.2.2.1 hm.2.2.2.2 (hordinary u hu e he)
  have hreal : (∫ J, D J*φ J ∂ν) ≤
      Cdet^(1/r)*q^(1-1/r)*(∫ J, D J ∂ν) :=
    (div_le_iff₀ hm.2.2.1).mp hholder
  have hprod : Integrable (fun J => D J*φ J) ν :=
    hm.1.mul_bdd hφm.aestronglyMeasurable hφnorm
  have hprodENN : (∫⁻ J, ENNReal.ofReal (D J)*ENNReal.ofReal (φ J) ∂ν) =
      ENNReal.ofReal (∫ J, D J*φ J ∂ν) := by
    calc
      _ = ∫⁻ J, ENNReal.ofReal (D J*φ J) ∂ν :=
        lintegral_congr fun J => (ENNReal.ofReal_mul (abs_nonneg _)).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hprod
        (.of_forall fun J => mul_nonneg (abs_nonneg _) (hφ01 J).1)).symm
  have hmeanENN : ENNReal.ofReal (∫ J, D J ∂ν) = ∫⁻ J, ENNReal.ofReal (D J) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hm.1 (.of_forall fun J => abs_nonneg _)
  have hconst : 0 ≤ Cdet^(1/r)*q^(1-1/r) :=
    mul_nonneg (Real.rpow_nonneg hCdet.le _) (Real.rpow_nonneg hq _)
  change (∫⁻ J, ENNReal.ofReal (D J)*ENNReal.ofReal (φ J) ∂ν) ≤
    ENNReal.ofReal (Cdet^(1/r)*q^(1-1/r))*(∫⁻ J, ENNReal.ofReal (D J) ∂ν)
  rw [hprodENN,← hmeanENN,← ENNReal.ofReal_mul hconst]
  exact ENNReal.ofReal_le_ofReal hreal

end SlowEquilibration.SourceConditionedCPTransferPureHolder
