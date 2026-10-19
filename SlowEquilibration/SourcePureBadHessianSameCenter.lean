-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalBadCriticalVanishingCriterion
public import SlowEquilibration.SourcePureLocalMaxWindowCountBridge

/-! In every fixed centered proper-pure window, the probability of an
original-field critical point with Hessian not strictly negative vanishes. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalPosteriorMaps SphericalForm SphereHessian NegativeDefiniteOperators
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem sourcePure_bad_hessian_probability_tendsto_zero_of_center
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ g : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hunit : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M)
    (hcrit : ∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
      sourceUnfilteredValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
        (sourcePureCenteredNormalizedWindow n m
          (markE (FiniteMixture.pure p hp a ha) β x Q) δ L R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))))
    (L : ℝ) (hL : 0 < L) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let I n := Icc (m (n+1)-L) (m (n+1)+L) ∩
      Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ))
    let K n := physicalEnergyWindow (n+3) (I n) univ
    Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
      {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) y=0 ∧
        actualScore (centerCoefficients (mixtureCoefficients μ) Q) J y ∈ K n ∧
        ¬ NegativeDefinite
          (intrinsicHessian (field (centerCoefficients (mixtureCoefficients μ) Q) J) y)})
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let I (n : ℕ) := Icc (m (n+1)-L) (m (n+1)+L) ∩
    Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ))
  let K (n : ℕ) := physicalEnergyWindow (n+3) (I n) univ
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A (n : ℕ) := ∫⁻ J, actualNegativeCriticalCount (n+2) c (K n) J
    ∂disorderLaw (n+3) μ.maxDegree
  let B (n : ℕ) := ∫⁻ J, actualBadCriticalCount (n+2) c (K n) J
    ∂disorderLaw (n+3) μ.maxDegree
  let C (n : ℕ) := ∫⁻ J, actualScoreWindowCount (n+2) c (K n) (fun _ _ => 1) J
    ∂disorderLaw (n+3) μ.maxDegree
  let P (n : ℕ) := disorderLaw (n+3) μ.maxDegree
      {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)}
  have hm : E ∈ Ioo (E-δ) (E+δ) := by
    constructor <;> dsimp [E] <;> linarith
  have hK (n : ℕ) : MeasurableSet (K n) := by
    exact rectangularScoreWindow_measurable _ _
      ((measurableSet_Icc.inter measurableSet_Ioo).preimage
        (measurable_const_mul ((n+3 : ℕ) : ℝ))) MeasurableSet.univ
  have hscore (n : ℕ) : pureScoreWindow p (K n) =
      sourcePureCenteredNormalizedWindow n m E δ (-L) L := by
    ext z
    simp [K,I,physicalEnergyWindow,rectangularScoreWindow,pureScoreWindow,
      pureScoreLine,sourcePureCenteredNormalizedWindow]
  have hCeq (n : ℕ) : (C n).toReal =
      sourceUnfilteredValueWindowMean (n+2) μ Q
        (sourcePureCenteredNormalizedWindow n m E δ (-L) L) := by
    unfold C sourceUnfilteredValueWindowMean
    congr 1
    apply lintegral_congr
    intro J
    rw [actual_pure_scoreWindowCount_eq_valueWindowCount]
    rw [hscore]
  have hN (n : ℕ) : (A n).toReal =
      sourcePureTruncatedLocalMaxWindowMean (n+1) p hp a ha Q
        (E-δ) (E+δ) (m (n+1)-L) (m (n+1)+L) := by
    unfold A sourcePureTruncatedLocalMaxWindowMean
    congr 1
    exact lintegral_congr_ae
      (actualLocalMaxCount_eq_negative_ae (n+2) (by omega) μ h.overlap_range.1 (K n)).symm
  have hInt : ∀ᶠ n : ℕ in atTop,
      Integrable (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) :=
    pureTruncatedLocalMaxDensity_integrable_eventually p hp a ha h
      (by dsimp [E]; linarith) hg hLeft le_rfl
  have hTail := (sourcePure_truncatedLocalMax_normalized_limits_of_center
    p hp a ha h hm hg hLeft le_rfl m hM hunit).2
  have hWin := compact_centered_window_integral_limit m hInt hTail (by linarith : -L ≤ L)
  have hWin' : Tendsto (fun n : ℕ =>
      sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q
        (E-δ) (E+δ) (m n-L) (m n+L))
      atTop (𝓝 (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L))) := by
    have heq : (fun n : ℕ => ∫ H in Icc (m n + -L) (m n + L),
      pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ)) H) =ᶠ[atTop]
      (fun n => sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q
        (E-δ) (E+δ) (m n-L) (m n+L)) :=
      Filter.Eventually.of_forall (fun n => by
        simpa only [sub_eq_add_neg] using
          (sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha
            h.overlap_range.1 (E-δ) (E+δ) (m n-L) (m n+L)).symm)
    simpa only [neg_mul,mul_neg,neg_neg] using hWin.congr' heq
  have hAlimit : Tendsto (fun n => (A n).toReal) atTop
      (𝓝 (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L))) := by
    have ht := hWin'.comp (tendsto_add_atTop_nat 1)
    exact ht.congr' (Filter.Eventually.of_forall fun n => (hN n).symm)
  have hClimit : Tendsto (fun n => (C n).toReal) atTop
      (𝓝 (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L))) := by
    have ht := hcrit (-L) L (by linarith)
    simpa only [neg_mul,mul_neg,neg_neg] using
      (ht.congr' (Filter.Eventually.of_forall fun n => (hCeq n).symm))
  have hPart (n : ℕ) : A n+B n=C n :=
    pure_negative_mean_add_bad_mean (n+1) p hp a ha h.overlap_range.1 (K n) (hK n)
  have hFinite : ∀ᶠ n : ℕ in atTop, C n < ⊤ :=
    Filter.Eventually.of_forall fun n => by
      unfold C
      rw [actual_pure_count_intensity (n+1) p hp a ha h.overlap_range.1 (K n) (hK n)]
      exact actual_pure_count_intensity_finite (n+1) p hp a ha h.overlap_range.1 (K n) (hK n)
  have hProb (n : ℕ) : P n ≤ B n :=
    pure_bad_critical_probability_le_bad_mean (n+1) p hp a ha h.overlap_range.1 (K n) (hK n)
  exact bad_probability_tendsto_zero_of_matching_means A B C P
    (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)) hFinite hPart hAlimit hClimit hProb

end SlowEquilibration.SphericalMarkedWindows
