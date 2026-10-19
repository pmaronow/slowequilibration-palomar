-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedLogarithmicCentering
public import SlowEquilibration.SourcePureCompactTailCenterNoContinuity

/-! Logarithmic centering for a nonnegative density that may jump to zero at
compact mark-window endpoints. Positivity is needed only near the bracket. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 400000

theorem compact_logarithmic_normalized_center
    {f : ℕ → ℝ → ℝ} {E₀ c₀ : ℝ} (hc₀ : 0 < c₀)
    (hregular : ∀ᶠ n : ℕ in atTop,
      Integrable (f n) ∧ ∀ H : ℝ, 0 ≤ f n H)
    (hpositive : ∀ D : ℝ, 0 ≤ D → ∀ᶠ n : ℕ in atTop,
      ∀ H ∈ Ioo ((n+2 : ℕ)*E₀-D*Real.log (n+2 : ℕ))
        ((n+2 : ℕ)*E₀+D*Real.log (n+2 : ℕ)), 0 < f n H)
    (hbound : ∀ D : ℝ, 0 ≤ D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ σ : ℝ,
        |σ| ≤ D*Real.log (n+2 : ℕ) →
        c*Real.exp (-c₀*σ)/Real.sqrt (n+2 : ℕ) ≤
          tail (f n) ((n+2 : ℕ)*E₀+σ) ∧
        tail (f n) ((n+2 : ℕ)*E₀+σ) ≤
          C*Real.exp (-c₀*σ)/Real.sqrt (n+2 : ℕ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, ∃ m : ℝ,
      tail (f n) m=1 ∧
      (∀ y : ℝ, tail (f n) y=1 → y=m) ∧
      |m-((n+2 : ℕ)*E₀-Real.log (n+2 : ℕ)/(2*c₀))| ≤ M := by
  let D := 1/(2*c₀)+2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDextra : 0 ≤ D+1 := by linarith
  obtain ⟨c,C,hc,hC,hTail⟩ := hbound D hD
  obtain ⟨M₀,hM₀,hCup,hclo⟩ := exists_exponential_bracket hc hC hc₀
  let M := M₀+1
  have hM : 0 < M := by dsimp [M]; linarith
  have hcloStrict : 1 < c*Real.exp (c₀*M) := by
    have hh : c*Real.exp (c₀*M₀) < c*Real.exp (c₀*M) := by
      apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hc
      dsimp [M]
      nlinarith [hc₀]
    exact hclo.trans_lt hh
  have hCupStrict : C*Real.exp (-c₀*M) < 1 := by
    have hh : C*Real.exp (-c₀*M) < C*Real.exp (-c₀*M₀) := by
      apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) hC
      dsimp [M]
      nlinarith [hc₀]
    exact hh.trans_le hCup
  have hLogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  refine ⟨M,hM,?_⟩
  filter_upwards [hregular,hpositive (D+1) hDextra,hTail,
    hLogTop.eventually (eventually_ge_atTop M)] with n hr hp hn hlogM
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n+2 : ℕ) := hM.le.trans hlogM
  let σ₀ := -Real.log (n+2 : ℕ)/(2*c₀)
  let r := (n+2 : ℕ)*E₀+σ₀
  let left := r-M
  let right := r+M
  have habs : |σ₀|=Real.log (n+2 : ℕ)/(2*c₀) := by
    dsimp [σ₀]
    rw [abs_div,abs_neg,abs_of_nonneg hlog,abs_of_pos (by positivity : 0 < 2*c₀)]
  have hminor : Real.log (n+2 : ℕ)/(2*c₀)+M ≤
      D*Real.log (n+2 : ℕ) := by
    calc
      _ ≤ Real.log (n+2 : ℕ)/(2*c₀)+Real.log (n+2 : ℕ) := by linarith [hlogM]
      _ = (1/(2*c₀)+1)*Real.log (n+2 : ℕ) := by ring
      _ ≤ D*Real.log (n+2 : ℕ) :=
        mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hlog
  have hleftσ : |σ₀-M| ≤ D*Real.log (n+2 : ℕ) :=
    (abs_sub _ _).trans (by rw [habs,abs_of_pos hM]; exact hminor)
  have hrightσ : |σ₀+M| ≤ D*Real.log (n+2 : ℕ) :=
    (abs_add_le _ _).trans (by rw [habs,abs_of_pos hM]; exact hminor)
  have hLeft : 1 < tail (f n) left := by
    have hh := (hn (σ₀-M) hleftσ).1
    have hs := reference_scale hN hc₀ (-M)
    have he : c*Real.exp (-c₀*(σ₀-M))/Real.sqrt (n+2 : ℕ) =
        c*Real.exp (c₀*M) := by
      dsimp [σ₀]
      rw [mul_div_assoc]
      convert congrArg (fun z : ℝ => c*z) hs using 1
      ring
    rw [he] at hh
    have harg : (n+2 : ℕ)*E₀+(σ₀-M)=left := by dsimp [left,r]; ring
    rw [harg] at hh
    exact hcloStrict.trans_le hh
  have hRight : tail (f n) right < 1 := by
    have hh := (hn (σ₀+M) hrightσ).2
    have hs := reference_scale hN hc₀ M
    have he : C*Real.exp (-c₀*(σ₀+M))/Real.sqrt (n+2 : ℕ) =
        C*Real.exp (-c₀*M) := by
      dsimp [σ₀]
      rw [mul_div_assoc]
      exact congrArg (fun z : ℝ => C*z) hs
    rw [he] at hh
    have harg : (n+2 : ℕ)*E₀+(σ₀+M)=right := by dsimp [right,r]; ring
    rw [harg] at hh
    exact hh.trans_lt hCupStrict
  have hleftInside : (n+2 : ℕ)*E₀-(D+1)*Real.log (n+2 : ℕ) < left := by
    have hh := (abs_le.mp hleftσ).1
    dsimp [left,r]
    nlinarith [hM,hlogM]
  have hrightInside : right < (n+2 : ℕ)*E₀+(D+1)*Real.log (n+2 : ℕ) := by
    have hh := (abs_le.mp hrightσ).2
    dsimp [right,r]
    nlinarith [hM,hlogM]
  have hpos : ∀ H ∈ Ioo left right, 0 < f n H := by
    intro H hH
    exact hp H ⟨hleftInside.trans hH.1,hH.2.trans hrightInside⟩
  obtain ⟨m,hm,hu⟩ := exists_unique_normalized_center_compact_support_no_continuity
    hr.1 hr.2 (by dsimp [left,right]; linarith [hM]) hpos hLeft hRight
  have hAnti := tail_antitone_of_nonneg hr.1 hr.2
  refine ⟨m,hm.1,?_,?_⟩
  · intro y hy
    have hyMem : y ∈ Ioo left right := by
      constructor
      · by_contra hNot
        have hle : y ≤ left := le_of_not_gt hNot
        have hh := hAnti hle
        rw [hy] at hh
        linarith [hLeft]
      · by_contra hNot
        have hle : right ≤ y := le_of_not_gt hNot
        have hh := hAnti hle
        rw [hy] at hh
        linarith [hRight]
    exact hu y ⟨hy,hyMem⟩
  apply abs_le.mpr
  dsimp [left,right,r,σ₀] at hm
  simp only [neg_div] at hm
  constructor <;> linarith [hm.2.1,hm.2.2]

end SlowEquilibration.ExpectedTailCentering
