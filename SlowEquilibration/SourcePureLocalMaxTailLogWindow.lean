-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxTailUpper
public import SlowEquilibration.SourcePureLocalMaxLogWindowDensity
public import SlowEquilibration.NatLogWindowBand

/-! Two-sided logarithmic-window upper-tail bounds for the literal
mark-truncated proper-pure negative-Hessian local-maximum intensity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 500000

theorem sourcePure_truncatedLocalMax_tail_log_window
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
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) ((n+2 : ℕ)*E+σ) ∧
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) ((n+2 : ℕ)*E+σ) ≤
        C*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let δ := min (E-l) (r-E)
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  have hD' : 0 ≤ D+1 := by linarith
  obtain ⟨c,C,hc',hC,hDensity⟩ :=
    sourcePure_localMaxPhysicalIntensity_log_window_bounds
      p hp a ha h hm hg hLeft hRight hD'
  obtain ⟨C₂,hC₂,hUpper⟩ := sourcePure_truncatedLocalMax_tail_global_upper
    p hp a ha h (hm.1.trans hm.2) hg hLeft hRight
  refine ⟨c*Real.exp (-(β*x)),C₂/(β*x),
    mul_pos hc' (Real.exp_pos _),div_pos hC₂ hc,?_⟩
  have hLogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  filter_upwards [hDensity,hUpper,
    pureTruncatedLocalMaxDensity_integrable_eventually
      p hp a ha h (hm.1.trans hm.2) hg hLeft hRight,
    NatLogWindowScales.log_window_inside_band_eventually (D+1) hδ,
    hLogTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hUp hi hBand hLog
  intro σ hσ
  let N : ℝ := (n+2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hδL : δ ≤ E-l := min_le_left _ _
  have hδR : δ ≤ r-E := min_le_right _ _
  have hδNL := mul_le_mul_of_nonneg_left hδL hN.le
  have hδNR := mul_le_mul_of_nonneg_left hδR hN.le
  have hσBounds := abs_le.mp hσ
  have hLowerPoint : ∀ v ∈ Icc (0 : ℝ) 1,
      (c*Real.exp (-(β*x)))*Real.exp (-(β*x)*σ)/Real.sqrt N ≤
        f n (N*E+σ+v) := by
    intro v hv
    have hσv : |σ+v| ≤ (D+1)*Real.log (n+2 : ℕ) := by
      calc
        |σ+v| ≤ |σ|+|v| := abs_add_le _ _
        _ ≤ D*Real.log (n+2 : ℕ)+1 := by
          rw [abs_of_nonneg hv.1]
          have hv1 : v ≤ 1 := hv.2
          linarith [hσ,hv1]
        _ ≤ (D+1)*Real.log (n+2 : ℕ) := by nlinarith
    have hInside : N*E+σ+v ∈ Ioo (N*l) (N*r) := by
      have hσvBounds := abs_le.mp hσv
      constructor <;> nlinarith [hBand,hδNL,hδNR,hσvBounds.1,hσvBounds.2]
    have hRaw := (hn (σ+v) hσv).1
    have hExp : Real.exp (-(β*x)*v) ≥ Real.exp (-(β*x)) :=
      Real.exp_le_exp.mpr (by nlinarith [hv.2, hc])
    have hMult := mul_le_mul_of_nonneg_left hExp
      (by positivity : 0 ≤ c*Real.exp (-(β*x)*σ)/Real.sqrt N)
    have hEq : N*E+(σ+v)=N*E+σ+v := by ring
    rw [hEq] at hRaw
    have hRaw' : c*Real.exp (-(β*x)*(σ+v))/Real.sqrt N ≤ f n (N*E+σ+v) := by
      change _ ≤ (Ioo (N*l) (N*r)).indicator
        (fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal) (N*E+σ+v)
      rw [Set.indicator_of_mem hInside]
      exact hRaw
    calc
      (c*Real.exp (-(β*x)))*Real.exp (-(β*x)*σ)/Real.sqrt N =
          (c*Real.exp (-(β*x)*σ)/Real.sqrt N)*Real.exp (-(β*x)) := by ring
      _ ≤ (c*Real.exp (-(β*x)*σ)/Real.sqrt N)*Real.exp (-(β*x)*v) := hMult
      _ = c*Real.exp (-(β*x)*(σ+v))/Real.sqrt N := by
        rw [show -(β*x)*(σ+v)=-(β*x)*σ+(-(β*x)*v) by ring,Real.exp_add]
        ring
      _ ≤ f n (N*E+σ+v) := hRaw'
  have hTailLo := tail_lower_of_absolute_unit_envelope hi
    (fun H => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q (N*l) (N*r) H)
    hLowerPoint
  have hTailHi := hUp (N*E+σ)
  constructor
  · simpa only [f] using hTailLo
  · have hEq : N*E+σ-(n+2 : ℕ)*E=σ := by dsimp [N]; ring
    rw [hEq] at hTailHi
    exact hTailHi

end SlowEquilibration.SphericalMarkedWindows
