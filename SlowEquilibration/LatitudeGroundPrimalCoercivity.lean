-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundPrimal

/-! Actual sublevel bounds for the one-step primal functional. These give
a compact parameter rectangle for every positive fixed slope; no existence
of a minimizer is assumed. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open Set
set_option maxHeartbeats 600000

theorem primalAtBottom_component_bounds (χ χ₁ : ℝ → ℝ) {α s b : ℝ}
    (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) (hb : 0 < b)
    (hdiff : χ s ≤ χ 1) (hχ₁ : 0 ≤ χ₁ 1) :
    0 ≤ primalAtBottom χ χ₁ α s b ∧
      b*χ₁ 1 ≤ 2*primalAtBottom χ χ₁ α s b ∧
      s/(b+α*(1-s)) ≤ 2*primalAtBottom χ χ₁ α s b ∧
      Real.log ((b+α*(1-s))/b)/α ≤ 2*primalAtBottom χ χ₁ α s b := by
  have hLb : b ≤ b+α*(1-s) := by nlinarith [hs.2]
  have hL : 0 < b+α*(1-s) := hb.trans_le hLb
  have hratio : 1 ≤ (b+α*(1-s))/b := (one_le_div hb).mpr hLb
  have hlog : 0 ≤ Real.log ((b+α*(1-s))/b) := Real.log_nonneg hratio
  have h₁ : 0 ≤ b*χ₁ 1 := mul_nonneg hb.le hχ₁
  have h₂ : 0 ≤ α*(χ 1-χ s) := mul_nonneg hα.le (sub_nonneg.mpr hdiff)
  have h₃ : 0 ≤ s/(b+α*(1-s)) := div_nonneg hs.1 hL.le
  have h₄ : 0 ≤ Real.log ((b+α*(1-s))/b)/α := div_nonneg hlog hα.le
  rw [primalAtBottom_eq]
  constructor
  · positivity
  · constructor
    · linarith
    · constructor <;> linarith

theorem primalAtBottom_sublevel_bounds (χ χ₁ : ℝ → ℝ) {α s b R : ℝ}
    (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) (hb : 0 < b)
    (hdiff : χ s ≤ χ 1) (hχ₁ : 0 < χ₁ 1)
    (hsub : primalAtBottom χ χ₁ α s b ≤ R) :
    0 < R ∧ b ≤ 2*R/χ₁ 1 ∧
      min (1/(4*R)) (α/2)*Real.exp (-2*R*α) ≤ b := by
  obtain ⟨_hP,henergy,hmass,hentropy⟩ := primalAtBottom_component_bounds χ χ₁
    hα hs hb hdiff hχ₁.le
  have hR : 0 < R := by nlinarith [mul_pos hb hχ₁]
  have hupper : b ≤ 2*R/χ₁ 1 := (le_div_iff₀ hχ₁).mpr (by linarith)
  let L := b+α*(1-s)
  have hLb : b ≤ L := by dsimp [L];nlinarith [hs.2]
  have hL : 0 < L := hb.trans_le hLb
  have hmass' : s ≤ 2*R*L := (div_le_iff₀ hL).mp (by
    change s/(b+α*(1-s)) ≤ 2*R
    linarith)
  have hfloor : min (1/(4*R)) (α/2) ≤ L := by
    by_cases hh : 1/2 ≤ s
    · apply (min_le_left _ _).trans
      apply (div_le_iff₀ (show 0 < 4*R by positivity)).mpr
      nlinarith [hmass']
    · apply (min_le_right _ _).trans
      dsimp [L]
      nlinarith [hb,lt_of_not_ge hh]
  have hlog : Real.log (L/b) ≤ 2*R*α := (div_le_iff₀ hα).mp (by
    change Real.log ((b+α*(1-s))/b)/α ≤ 2*R
    linarith)
  have hratio : 0 < L/b := div_pos hL hb
  have hexp : L/b ≤ Real.exp (2*R*α) := by
    calc
      _ = Real.exp (Real.log (L/b)) := (Real.exp_log hratio).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  have hproduct : L ≤ b*Real.exp (2*R*α) := by
    simpa only [mul_comm] using (div_le_iff₀ hb).mp hexp
  have hexpneg : 0 ≤ Real.exp (-2*R*α) := (Real.exp_pos _).le
  have heq : b*Real.exp (2*R*α)*Real.exp (-2*R*α)=b := by
    rw [mul_assoc,←Real.exp_add]
    ring_nf
    simp
  have hlower : L*Real.exp (-2*R*α) ≤ b := by
    simpa only [heq] using mul_le_mul_of_nonneg_right hproduct hexpneg
  refine ⟨hR,hupper,?_⟩
  exact (mul_le_mul_of_nonneg_right hfloor hexpneg).trans hlower

end SlowEquilibration.LatitudeGroundTrial
