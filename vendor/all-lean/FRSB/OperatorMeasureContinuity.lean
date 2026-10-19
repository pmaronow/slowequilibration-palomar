module
public import FRSB.ParisiMeasureTopology
public import Paper.ParisiTranslation

@[expose] public section

/-! # Actual Parisi bilinear operator continuity in the weak measure topology

The near-time inverse-square-root heat kernel is controlled by the genuine
CDF L¹ distance. Polarization then controls the complete bilinear operator
norm uniformly over its two unit balls. The generic norm lemmas avoid the
competing inherited module instances of concrete nested BCF operators.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace FRSB
open Paper

/-- Subtraction formed with a generic Banach carrier's coherent CLM instances. -/
def bilinearOperatorSub {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B D : X →L[ℝ] X →L[ℝ] X) : X →L[ℝ] X →L[ℝ] X := B - D

/-- Ordinary continuity expressed using coherent generic carrier instances. -/
def bilinearOperatorContinuous {P X : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : P → X →L[ℝ] X →L[ℝ] X) : Prop := Continuous B

/-- Ordinary operator-norm convergence with the same generic carrier. -/
def bilinearOperatorTendsto {A X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : A → X →L[ℝ] X →L[ℝ] X) (l : Filter A) (D : X →L[ℝ] X →L[ℝ] X) : Prop :=
  Tendsto B l (𝓝 D)

/-- A single-layer generic norm criterion also fixes the nested topology diamond. -/
theorem continuousLinearMap_tendsto_of_norm_sub {E F A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : A → E →L[ℝ] F) (l : Filter A) (D : E →L[ℝ] F)
    (h : ∀ ε > 0, ∀ᶠ i in l, ‖B i - D‖ < ε) : Tendsto B l (𝓝 D) := by
  apply Metric.tendsto_nhds.mpr
  simpa only [dist_eq_norm] using h

theorem symmetric_bilinear_polarization {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] X) (hB : ∀ v w, B v w = B w v) (v w : X) :
    B v w = (1 / 4 : ℝ) • (B (v + w) (v + w) - B (v - w) (v - w)) := by
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  rw [hB w v]
  module

theorem bilinearOperatorNorm_le_of_unit_bounds {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] X) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ v w, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 → ‖B v w‖ ≤ C) :
    bilinearOperatorNorm B ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro w hw
  exact hb v w hv.le hw.le

theorem bilinearOperatorNorm_sub_le_of_diagonal_bound {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B D : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ v w, B v w = B w v) (hD : ∀ v w, D v w = D w v)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ v, ‖v‖ ≤ 2 → ‖B v v - D v v‖ ≤ K) :
    bilinearOperatorNorm (bilinearOperatorSub B D) ≤ K / 2 := by
  unfold bilinearOperatorSub
  apply bilinearOperatorNorm_le_of_unit_bounds _ _ (by positivity)
  intro v w hv hw
  have hplus : ‖v + w‖ ≤ 2 := (norm_add_le v w).trans (by linarith)
  have hminus : ‖v - w‖ ≤ 2 := (norm_sub_le v w).trans (by linarith)
  have hsym : ∀ v w, (B - D) v w = (B - D) w v := by
    intro v w
    simp only [ContinuousLinearMap.sub_apply, hB v w, hD v w]
  rw [symmetric_bilinear_polarization (B - D) hsym v w, norm_smul,
    show ‖(1 / 4 : ℝ)‖ = 1 / 4 by norm_num]
  simp only [ContinuousLinearMap.sub_apply]
  have h := norm_sub_le (B (v + w) (v + w) - D (v + w) (v + w))
    (B (v - w) (v - w) - D (v - w) (v - w))
  have hbplus := hb (v + w) hplus
  have hbminus := hb (v - w) hminus
  linarith

/-- The actual quadratic Gaussian correction varies at the CDF square-root rate. -/
theorem norm_parisiSlabQuadraticOperator_measure_mesh_le (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (v : ParisiSlabGradient a b) (hv : ‖v‖ ≤ 2)
    (δ : ℝ) (hδ : 0 < δ) (hCDF : parisiCDFDistance μ ν ≤ δ) :
    ‖parisiSlabQuadraticOperator β μ hab v - parisiSlabQuadraticOperator β ν hab v‖ ≤
      6 * |β| * gaussianAbsMoment * Real.sqrt δ := by
  have hbase := norm_parisiSlabGradientOperator_measure_L1_sub_le β μ ν hab ha hb
    (fun _ => 0) continuous_const (by simp) v δ hδ
  simp only [Real.norm_eq_abs] at hbase
  change ‖parisiSlabQuadraticOperator β μ hab v -
      parisiSlabQuadraticOperator β ν hab v‖ ≤
    |β| * gaussianAbsMoment * ‖v‖ ^ 2 / 2 *
      (2 * Real.sqrt δ + parisiCDFDistance μ ν * (Real.sqrt δ)⁻¹) at hbase
  have hsqrt : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  have heq : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by
    conv_lhs => arg 1; rw [← Real.sq_sqrt hδ.le]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hsqrt, mul_one]
  have hscaled := mul_le_mul_of_nonneg_right hCDF
    (show 0 ≤ (Real.sqrt δ)⁻¹ by positivity)
  rw [heq] at hscaled
  have hvpow : ‖v‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg v]
  have hp : 0 ≤ |β| * gaussianAbsMoment :=
    mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg
  calc
    _ ≤ |β| * gaussianAbsMoment * ‖v‖ ^ 2 / 2 * (3 * Real.sqrt δ) :=
      hbase.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ = (|β| * gaussianAbsMoment * Real.sqrt δ) * (3 / 2 * ‖v‖ ^ 2) := by ring
    _ ≤ (|β| * gaussianAbsMoment * Real.sqrt δ) * (3 / 2 * 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- The complete actual bilinear operator norm has the same CDF rate. -/
theorem parisiSlabBilinearOperator_measure_mesh_le (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hCDF : parisiCDFDistance μ ν ≤ δ) :
    bilinearOperatorNorm (bilinearOperatorSub (parisiSlabBilinearOperator β μ hab)
      (parisiSlabBilinearOperator β ν hab)) ≤
        3 * |β| * gaussianAbsMoment * Real.sqrt δ := by
  have h := bilinearOperatorNorm_sub_le_of_diagonal_bound
    (parisiSlabBilinearOperator β μ hab) (parisiSlabBilinearOperator β ν hab)
    (parisiSlabBilinearOperator_symm β μ hab) (parisiSlabBilinearOperator_symm β ν hab)
    (6 * |β| * gaussianAbsMoment * Real.sqrt δ)
    (by have := gaussianAbsMoment_nonneg; positivity)
    (fun v hv => by
      simpa only [← parisiSlabQuadraticOperator_eq_bilinear] using
        norm_parisiSlabQuadraticOperator_measure_mesh_le β μ ν hab ha hb v hv δ hδ hCDF)
  exact h.trans_eq (by ring)

/-- A quantitative CDF modulus gives ordinary operator-norm convergence. -/
theorem bilinearOperatorTendsto_of_mesh_estimate {X A : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {l : Filter A} [l.IsCountablyGenerated]
    (B : ParisiMeasure → X →L[ℝ] X →L[ℝ] X) (C : ℝ)
    (hmesh : ∀ μ ν δ, 0 < δ → parisiCDFDistance μ ν ≤ δ →
      bilinearOperatorNorm (bilinearOperatorSub (B μ) (B ν)) ≤ C * Real.sqrt δ)
    (μ : ParisiMeasure) (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) :
    bilinearOperatorTendsto (fun i => B (ν i)) l (B μ) := by
  unfold bilinearOperatorTendsto
  have hCDF := tendsto_parisiCDFDistance_of_tendsto hν
  have herr : Tendsto (fun n : ℕ => C * Real.sqrt (1 / (n + 1 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
  apply continuousLinearMap_tendsto_of_norm_sub
  intro ε hε
  obtain ⟨n, hn⟩ := (herr.eventually (eventually_lt_nhds hε)).exists
  have hδ : (0 : ℝ) < 1 / (n + 1 : ℕ) := by positivity
  filter_upwards [hCDF.eventually (eventually_lt_nhds hδ)] with i hi
  exact (hmesh (ν i) μ _ hδ hi.le).trans_lt hn

theorem bilinearOperatorContinuous_of_mesh_estimate {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ParisiMeasure → X →L[ℝ] X →L[ℝ] X) (C : ℝ)
    (hmesh : ∀ μ ν δ, 0 < δ → parisiCDFDistance μ ν ≤ δ →
      bilinearOperatorNorm (bilinearOperatorSub (B μ) (B ν)) ≤ C * Real.sqrt δ) :
    bilinearOperatorContinuous B := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact bilinearOperatorTendsto_of_mesh_estimate B C hmesh μ id tendsto_id

/-- Standard weak convergence implies convergence in the actual operator norm. -/
theorem tendsto_parisiSlabBilinearOperator_of_tendsto {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (μ : ParisiMeasure) (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) :
    bilinearOperatorTendsto (fun i => parisiSlabBilinearOperator β (ν i) hab) l
      (parisiSlabBilinearOperator β μ hab) :=
  bilinearOperatorTendsto_of_mesh_estimate _ (3 * |β| * gaussianAbsMoment)
    (fun μ ν δ hδ hCDF => parisiSlabBilinearOperator_measure_mesh_le β μ ν hab ha hb δ hδ hCDF)
    μ ν hν

/-- The actual bilinear coefficient map is continuous in the weak topology. -/
theorem continuous_parisiSlabBilinearOperator (β : ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    bilinearOperatorContinuous (fun μ : ParisiMeasure => parisiSlabBilinearOperator β μ hab) :=
  bilinearOperatorContinuous_of_mesh_estimate _ (3 * |β| * gaussianAbsMoment)
    (fun μ ν δ hδ hCDF => parisiSlabBilinearOperator_measure_mesh_le β μ ν hab ha hb δ hδ hCDF)

end FRSB
