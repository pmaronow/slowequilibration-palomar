-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxCenteredShift
public import SlowEquilibration.SourcePureLocalMaxGlobalDensityEnvelope
public import SlowEquilibration.SourcePureLocalMaxLogWindowDensity

/-! A single integrable exponential dominates every density ratio around
any true logarithmically centered pure local-maximum intensity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open scoped Topology
set_option maxHeartbeats 500000

theorem sourcePure_truncatedLocalMax_centered_global_ratio_envelope
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      0 < f n (m n) ∧ ∀ v : ℝ,
        f n (m n+v)/f n (m n) ≤ A*Real.exp (-(β*x)*v) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  let σ : ℕ → ℝ := fun n => m n-(n+2 : ℕ)*E
  let δ := min (E-l) (r-E)
  let D := 1+1/(2*(β*x))
  have hc₀ : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  obtain ⟨hD,hσ⟩ := sourcePure_center_log_shift_bound hc₀ hM m hcenter
  obtain ⟨c,C₁,hc,hC₁,hDensity⟩ := sourcePure_localMaxPhysicalIntensity_log_window_bounds
    p hp a ha h hm hg hLeft hRight hD
  obtain ⟨C,hC,hGlobal⟩ := sourcePure_truncatedLocalMax_global_upper
    p hp a ha h hg hLeft hRight
  let A := C/c
  have hA : 0 < A := div_pos hC hc
  refine ⟨A,hA,?_⟩
  filter_upwards [hσ,hDensity,hGlobal,
    NatLogWindowScales.log_window_inside_band_eventually D hδ]
    with n hn hDen hGlob hBand
  let N : ℝ := (n+2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hS : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hδL : δ ≤ E-l := min_le_left _ _
  have hδR : δ ≤ r-E := min_le_right _ _
  have hδNL := mul_le_mul_of_nonneg_left hδL hN.le
  have hδNR := mul_le_mul_of_nonneg_left hδR hN.le
  have hh := abs_le.mp hn
  have hInside : m n ∈ Ioo (N*l) (N*r) := by
    constructor <;> nlinarith [hBand,hδNL,hδNR,hh.1,hh.2]
  have hEq : f n (m n) = (pureLocalMaxPhysicalIntensity n p hp a ha Q (m n)).toReal := by
    change (Ioo (N*l) (N*r)).indicator
      (fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal) (m n) = _
    rw [Set.indicator_of_mem hInside]
  let B : ℝ := Real.exp (-(β*x)*σ n)/Real.sqrt N
  have hB : 0 < B := div_pos (Real.exp_pos _) hS
  have hmEq : N*E+σ n=m n := by dsimp [σ]; ring
  have hLower : c*B ≤ f n (m n) := by
    have hd := (hDen (σ n) hn).1
    rw [hmEq] at hd
    rw [hEq]
    simpa only [B,div_eq_mul_inv,mul_assoc] using hd
  have hfpos : 0 < f n (m n) := (mul_pos hc hB).trans_le hLower
  refine ⟨hfpos,?_⟩
  intro v
  have hUpper : f n (m n+v) ≤ C*B*Real.exp (-(β*x)*v) := by
    have hg := hGlob (m n+v)
    have he : -(β*x)*((m n+v)-N*E) =
        -(β*x)*σ n+(-(β*x)*v) := by dsimp [σ]; ring
    rw [he,Real.exp_add] at hg
    dsimp [B]
    convert hg using 1
    ring
  apply (div_le_iff₀ hfpos).2
  have hMul := mul_le_mul_of_nonneg_left hLower
    (by positivity : 0 ≤ A*Real.exp (-(β*x)*v))
  calc
    f n (m n+v) ≤ C*B*Real.exp (-(β*x)*v) := hUpper
    _ = (A*Real.exp (-(β*x)*v))*(c*B) := by
      dsimp [A]
      field_simp [hc.ne']
    _ ≤ (A*Real.exp (-(β*x)*v))*f n (m n) := hMul

end SlowEquilibration.SphericalMarkedWindows
