-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureUniformLogWindowTangent
public import SlowEquilibration.NatLogWindowBand

/-! Uniform two-sided logarithmic-window density bounds for genuine pure
negative-Hessian local maxima. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open scoped Topology ENNReal
set_option maxHeartbeats 500000

theorem sourcePure_localMaxPhysicalIntensity_contact_prefactors
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c / Real.sqrt (n+2 : ℕ) ≤
        (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E)).toReal ∧
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E)).toReal ≤
        C / Real.sqrt (n+2 : ℕ) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let b := Q^2*μ.xi2 Q
  let g := ((p : ℝ)*E-2*Real.sqrt b)/2
  have hGap : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hg : 0 < g := by dsimp [g]; linarith
  have hMark : (p : ℝ)*E ∈ Icc (2*Real.sqrt b+g) ((p : ℝ)*E+1) := by
    dsimp [g]
    constructor <;> linarith
  have hZero : pureMarkedComplexity p hp a ha Q E=0 :=
    sourcePure_contact_complexity_zero p hp a ha h
  obtain ⟨c,C,hc,hC,hPref⟩ := pure_localMax_physical_prefactors
    p hp a ha h.overlap_range.1 (Z := (p : ℝ)*E+1) hg
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hPref] with n hn
  have hBounds := hn E hMark
  rw [hZero] at hBounds
  simp only [mul_zero,Real.exp_zero,mul_one] at hBounds
  have hUpper := hBounds.2.1.trans hBounds.2.2
  have hFinite : pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E) < ∞ :=
    lt_of_le_of_lt hUpper (by simp)
  have hLowerReal := ENNReal.toReal_mono hFinite.ne hBounds.1
  have hUpperReal := ENNReal.toReal_mono (by simp) hUpper
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hS : 0 < Real.sqrt (n+2 : ℕ) := Real.sqrt_pos.mpr hN
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ c*(Real.sqrt (n+2 : ℕ))⁻¹)]
    at hLowerReal
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C*(Real.sqrt (n+2 : ℕ))⁻¹)]
    at hUpperReal
  constructor
  · simpa only [div_eq_mul_inv] using hLowerReal
  · simpa only [div_eq_mul_inv] using hUpperReal

/-- The source pure local-max energy density has its sharp N⁻¹ᐟ²
normalization and contact exponential uniformly throughout any fixed
logarithmic physical-energy window inside the admissible exterior mark. -/
theorem sourcePure_localMaxPhysicalIntensity_log_window_bounds
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z)
    {D : ℝ} (hD : 0 ≤ D) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ σ : ℝ,
      |σ| ≤ D*Real.log (n+2 : ℕ) →
      c*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) ≤
        (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ)).toReal ∧
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ)).toReal ≤
        C*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let δ := min (E-l) (r-E)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  obtain ⟨c,C,hc,hC,hBase⟩ :=
    sourcePure_localMaxPhysicalIntensity_contact_prefactors p hp a ha h
  refine ⟨c*Real.exp (-1),C*Real.exp 1,
    mul_pos hc (Real.exp_pos _),mul_pos hC (Real.exp_pos _),?_⟩
  filter_upwards [hBase,
    sourcePure_localMaxPhysicalIntensity_uniform_log_window_tangent p hp a ha h hD
      (show (0 : ℝ) < 1 by norm_num),
    pureTruncatedLocalMaxDensity_pos_eventually p hp a ha h hg hLeft hRight,
    NatLogWindowScales.log_window_inside_band_eventually D hδ]
    with n hBaseN hUniform hPos hBand
  intro σ hσ
  let N : ℝ := (n+2 : ℕ)
  let F : ℝ := (pureLocalMaxPhysicalIntensity n p hp a ha Q (N*E+σ)).toReal
  let F₀ : ℝ := (pureLocalMaxPhysicalIntensity n p hp a ha Q (N*E)).toReal
  have hN : 0 < N := by dsimp [N]; positivity
  have hS : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hδL : δ ≤ E-l := min_le_left _ _
  have hδR : δ ≤ r-E := min_le_right _ _
  have hδNL := mul_le_mul_of_nonneg_left hδL hN.le
  have hδNR := mul_le_mul_of_nonneg_left hδR hN.le
  have hσbounds := abs_le.mp hσ
  have hInside : N*E+σ ∈ Ioo (N*l) (N*r) := by
    constructor <;> nlinarith [hBand,hδNL,hδNR,hσbounds.1,hσbounds.2]
  have hFpos : 0 < F := by
    have hh := hPos (N*E+σ) hInside
    change 0 < pureTruncatedLocalMaxDensity n p hp a ha Q (N*l) (N*r) (N*E+σ) at hh
    simpa [pureTruncatedLocalMaxDensity,hInside,F] using hh
  have hF₀pos : 0 < F₀ :=
    (div_pos hc hS).trans_le hBaseN.1
  have hErr := hUniform σ hσ
  change |Real.log F-Real.log F₀+β*x*σ| < 1 at hErr
  have hErrBounds := abs_lt.mp hErr
  have hExpLower : Real.exp (Real.log F₀-(β*x)*σ-1) ≤ F := by
    calc
      _ ≤ Real.exp (Real.log F) := Real.exp_le_exp.mpr (by linarith [hErrBounds.1])
      _ = F := Real.exp_log hFpos
  have hExpUpper : F ≤ Real.exp (Real.log F₀-(β*x)*σ+1) := by
    calc
      F = Real.exp (Real.log F) := (Real.exp_log hFpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hErrBounds.2])
  have hExpLId : Real.exp (Real.log F₀-(β*x)*σ-1) =
      Real.exp (-1)*F₀*Real.exp (-(β*x)*σ) := by
    rw [show Real.log F₀-(β*x)*σ-1 = Real.log F₀+(-1)+(-(β*x)*σ) by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hF₀pos]
    ring
  have hExpUId : Real.exp (Real.log F₀-(β*x)*σ+1) =
      Real.exp 1*F₀*Real.exp (-(β*x)*σ) := by
    rw [show Real.log F₀-(β*x)*σ+1 = Real.log F₀+1+(-(β*x)*σ) by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hF₀pos]
    ring
  have hMultLo := mul_le_mul_of_nonneg_left hBaseN.1
    (by positivity : 0 ≤ Real.exp (-1)*Real.exp (-(β*x)*σ))
  have hMultUp := mul_le_mul_of_nonneg_left hBaseN.2
    (by positivity : 0 ≤ Real.exp 1*Real.exp (-(β*x)*σ))
  constructor
  · calc
      (c*Real.exp (-1))*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) =
          Real.exp (-1)*Real.exp (-(β*x)*σ)*(c/Real.sqrt (n+2 : ℕ)) := by ring
      _ ≤ Real.exp (-1)*F₀*Real.exp (-(β*x)*σ) := by convert hMultLo using 1; ring
      _ = Real.exp (Real.log F₀-(β*x)*σ-1) := hExpLId.symm
      _ ≤ F := hExpLower
  · calc
      F ≤ Real.exp (Real.log F₀-(β*x)*σ+1) := hExpUpper
      _ = Real.exp 1*F₀*Real.exp (-(β*x)*σ) := hExpUId
      _ ≤ (C*Real.exp 1)*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) := by
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMultUp

end SlowEquilibration.SphericalMarkedWindows
