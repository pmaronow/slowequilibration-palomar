-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedTailCentering
public import SlowEquilibration.NatLogWindowScales

/-! A sharp square-root density normalization in a logarithmic window
gives the logarithmic correction of the true tail-equals-one centering. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

theorem reference_scale {N c₀ : ℝ} (hN : 0 < N) (hc₀ : 0 < c₀) (t : ℝ) :
    Real.exp (-c₀*(-Real.log N/(2*c₀)+t))/Real.sqrt N=Real.exp (-c₀*t) := by
  have he : -c₀*(-Real.log N/(2*c₀)+t)=Real.log N/2-c₀*t := by
    field_simp [hc₀.ne']
    ring
  rw [he,←Real.log_sqrt hN.le,Real.exp_sub,Real.exp_log (Real.sqrt_pos.mpr hN)]
  have hneg : -c₀*t=-(c₀*t) := by ring
  rw [hneg,Real.exp_neg]
  field_simp

theorem exists_exponential_bracket {c C c₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (hc₀ : 0 < c₀) :
    ∃ M : ℝ,0 < M ∧ C*Real.exp (-c₀*M) ≤ 1 ∧ 1 ≤ c*Real.exp (c₀*M) := by
  let M := max 1 (max (Real.log C/c₀) (-Real.log c/c₀))
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCup : Real.log C/c₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hclo : -Real.log c/c₀ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hCup' : Real.log C ≤ c₀*M := by exact (div_le_iff₀ hc₀).mp hCup |>.trans_eq (mul_comm _ _)
  have hclo' : -Real.log c ≤ c₀*M := by exact (div_le_iff₀ hc₀).mp hclo |>.trans_eq (mul_comm _ _)
  refine ⟨M,hM,?_,?_⟩
  · calc
      C*Real.exp (-c₀*M)=Real.exp (Real.log C-c₀*M) := by
        have hneg : -c₀*M=-(c₀*M) := by ring
        rw [Real.exp_sub,Real.exp_log hC,hneg,Real.exp_neg]
        ring
      _ ≤ 1 := by rw [←Real.exp_zero];exact Real.exp_le_exp.mpr (by linarith)
  · calc
      1=Real.exp (0 : ℝ) := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log c+c₀*M) := Real.exp_le_exp.mpr (by linarith)
      _=c*Real.exp (c₀*M) := by rw [Real.exp_add,Real.exp_log hc]

theorem logarithmic_normalized_center {f : ℕ → ℝ → ℝ} {E₀ c₀ : ℝ} (hc₀ : 0 < c₀)
    (hregular : ∀ᶠ n : ℕ in atTop,Integrable (f n) ∧ Continuous (f n) ∧ ∀ H : ℝ,0 < f n H)
    (hbound : ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ σ : ℝ,
      |σ| ≤ (1/(2*c₀)+1)*Real.log (n+2 : ℕ) →
      c*Real.exp (-c₀*σ)/Real.sqrt (n+2 : ℕ) ≤ tail (f n) ((n+2 : ℕ)*E₀+σ) ∧
      tail (f n) ((n+2 : ℕ)*E₀+σ) ≤ C*Real.exp (-c₀*σ)/Real.sqrt (n+2 : ℕ)) :
    ∃ M : ℝ,0 < M ∧ ∀ᶠ n : ℕ in atTop,∃ m : ℝ,
      tail (f n) m=1 ∧ (∀ y : ℝ,tail (f n) y=1 → y=m) ∧
      |m-((n+2 : ℕ)*E₀-Real.log (n+2 : ℕ)/(2*c₀))| ≤ M := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := hbound
  obtain ⟨M,hM,hCup,hclo⟩ := exists_exponential_bracket hc hC hc₀
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  refine ⟨M,hM,?_⟩
  filter_upwards [hregular,hbounds,hlogTop.eventually (eventually_ge_atTop M)] with n hr hn hlogM
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n+2 : ℕ) := hM.le.trans hlogM
  let σ₀ := -Real.log (n+2 : ℕ)/(2*c₀)
  let r := (n+2 : ℕ)*E₀+σ₀
  have habs : |σ₀|=Real.log (n+2 : ℕ)/(2*c₀) := by
    dsimp [σ₀]
    rw [abs_div,abs_neg,abs_of_nonneg hlog,abs_of_pos (by positivity : 0 < 2*c₀)]
  have hminor : Real.log (n+2 : ℕ)/(2*c₀)+M ≤
      (1/(2*c₀)+1)*Real.log (n+2 : ℕ) := by
    calc
      _ ≤ Real.log (n+2 : ℕ)/(2*c₀)+Real.log (n+2 : ℕ) := by linarith
      _=_ := by ring
  have hleft : |σ₀-M| ≤ (1/(2*c₀)+1)*Real.log (n+2 : ℕ) :=
    (abs_sub _ _).trans (by rw [habs,abs_of_pos hM];exact hminor)
  have hright : |σ₀+M| ≤ (1/(2*c₀)+1)*Real.log (n+2 : ℕ) :=
    (abs_add_le _ _).trans (by rw [habs,abs_of_pos hM];exact hminor)
  have hleftBound := (hn (σ₀-M) hleft).1
  have hrightBound := (hn (σ₀+M) hright).2
  have hscaleLeft := reference_scale hN hc₀ (-M)
  have hscaleRight := reference_scale hN hc₀ M
  have hleftT : 1 ≤ tail (f n) (r-M) := by
    have he : c*Real.exp (-c₀*(σ₀-M))/Real.sqrt (n+2 : ℕ)=c*Real.exp (c₀*M) := by
      dsimp [σ₀]
      rw [mul_div_assoc]
      convert congrArg (fun z : ℝ => c*z) hscaleLeft using 1
      ring
    rw [he] at hleftBound
    have hcancel : (n+2 : ℕ)*E₀+(σ₀-M)=r-M := by dsimp [r];ring
    rw [hcancel] at hleftBound
    exact hclo.trans hleftBound
  have hrightT : tail (f n) (r+M) ≤ 1 := by
    have he : C*Real.exp (-c₀*(σ₀+M))/Real.sqrt (n+2 : ℕ)=C*Real.exp (-c₀*M) := by
      dsimp [σ₀]
      rw [mul_div_assoc]
      exact congrArg (fun z : ℝ => C*z) hscaleRight
    rw [he] at hrightBound
    have hcancel : (n+2 : ℕ)*E₀+(σ₀+M)=r+M := by dsimp [r];ring
    rw [hcancel] at hrightBound
    exact hrightBound.trans hCup
  obtain ⟨m,hm,hu⟩ := exists_unique_normalized_center hr.1 hr.2.1 hr.2.2
    (by linarith : r-M ≤ r+M) hleftT hrightT
  have hmem := normalized_center_mem_Icc hr.1 hr.2.1 hr.2.2 hleftT hrightT hm
  refine ⟨m,hm,hu,?_⟩
  apply abs_le.mpr
  dsimp [r,σ₀] at hmem
  simp only [neg_div] at hmem
  constructor <;> linarith [hmem.1,hmem.2]

end SlowEquilibration.ExpectedTailCentering
