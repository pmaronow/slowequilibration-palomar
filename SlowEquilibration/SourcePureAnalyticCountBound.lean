-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureAnalyticScoreCountBridge

/-! Source §9 fixed-window expected critical counts at the manuscript's
explicit logarithmic center, for any Borel radial mark set. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 650000

theorem sourcePure_analytic_center_actual_count_uniform_of_selected
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M) (m : ℕ → ℝ)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-sourcePureAnalyticCenter (j+2)
        (markE (FiniteMixture.pure p hp a ha) β x Q) (β*x)| ≤ M)
    (hselected : ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ n : ℕ,
      let μ := FiniteMixture.pure p hp a ha
      let E := markE μ β x Q
      let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
      let K := {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-R) R ∧ b 1 ∈ U}
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) K
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) K
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B)
    (U : Set ℝ) (hU : MeasurableSet U) (L : ℝ) (hL : 0 < L) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let K n := physicalEnergyWindow (n+3)
      (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-L)
        (sourcePureAnalyticCenter (n+3) E (β*x)+L)) U
    ∃ B : ℝ, ∀ n : ℕ,
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) (K n)
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) (K n)
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-L)
      (sourcePureAnalyticCenter (n+3) E (β*x)+L)) U
  let V (n : ℕ) := {b : EuclideanSpace ℝ (Fin 2) |
    b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-(L+M)) (L+M) ∧
    b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
  let A (n : ℕ) := ∫⁻ J, actualScoreWindowCount (n+2) c (K n)
    (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree
  let D (n : ℕ) := ∫⁻ J, actualScoreWindowCount (n+2) c (V n)
    (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hK (n : ℕ) : MeasurableSet (K n) :=
    rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul ((n+3 : ℕ) : ℝ))) hU
  have hFinite (n : ℕ) : A n < ⊤ := by
    unfold A
    rw [actual_pure_count_intensity (n+1) p hp a ha h.overlap_range.1 (K n) (hK n)]
    exact actual_pure_count_intensity_finite (n+1) p hp a ha
      h.overlap_range.1 (K n) (hK n)
  obtain ⟨B,hD⟩ := hselected (L+M) (by linarith)
  have hGeom := sourcePure_analytic_window_eventually_in_selected_box
    (L := L) hb hM.le hδ m hcenter
  have hBound : ∀ᶠ n : ℕ in atTop, (A n).toReal ≤ B := by
    filter_upwards [hGeom] with n hn
    have hLine := pure_analytic_score_window_subset_selected
      n p hp E (β*x) δ L (L+M) m U hn
    have hPoint (J : Disorder (n+3) μ.maxDegree) :
        actualScoreWindowCount (n+2) c (K n) (fun _ _ => 1) J ≤
          actualScoreWindowCount (n+2) c (V n) (fun _ _ => 1) J :=
      pure_actualScoreWindowCount_mono_of_line (n+2) p hp a ha Q
        (K n) (V n) hLine J
    have hInt : A n ≤ D n := lintegral_mono hPoint
    exact (ENNReal.toReal_mono (hD n).1.ne hInt).trans (hD n).2
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hBound
  let F := ∑ j ∈ Finset.range n₀, (A j).toReal
  refine ⟨B+F,?_⟩
  intro n
  refine ⟨hFinite n,?_⟩
  by_cases hn : n < n₀
  · have hnn : 0 ≤ B := by
      have h0 := (hD 0).2
      exact (ENNReal.toReal_nonneg).trans h0
    have hsum : (A n).toReal ≤ F :=
      Finset.single_le_sum (fun j hj => ENNReal.toReal_nonneg)
        (Finset.mem_range.mpr hn)
    linarith
  · have hFn : 0 ≤ F := Finset.sum_nonneg fun j hj => ENNReal.toReal_nonneg
    exact le_trans (hn₀ n (Nat.le_of_not_gt hn)) (le_add_of_nonneg_right hFn)

end SlowEquilibration.SphericalMarkedWindows
