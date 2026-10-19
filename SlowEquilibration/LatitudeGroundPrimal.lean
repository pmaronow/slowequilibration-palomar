-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundTrialCalculus

/-! Analytic derivatives of the evaluated literal one-step spherical
ground trial. These are scalar variational statements, independent of
physical pressure or ground-state identification. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
set_option maxHeartbeats 600000

def primal (χ χ₁ : ℝ → ℝ) (L α s : ℝ) : ℝ :=
  ((L-α*(1-s))*χ₁ 1+α*(χ 1-χ s)+s/L+
    Real.log (L/(L-α*(1-s)))/α)/2

theorem functional_eq_primal (χ χ₁ χ₂ : ℝ → ℝ)
    (hχ : ∀ t, HasDerivAt χ (χ₁ t) t)
    (hχ₁ : ∀ t, HasDerivAt χ₁ (χ₂ t) t)
    (hχ₂ : Continuous χ₂) {L α s : ℝ} (hα : 0 < α)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) :
    functional χ₁ χ₂ L α s=primal χ χ₁ L α s := by
  rw [functional_eq χ χ₁ χ₂ hχ hχ₁ hχ₂ hα hs hb]
  unfold primal
  ring

theorem primal_hasDerivAt_height (χ χ₁ : ℝ → ℝ) {L α s : ℝ}
    (hL : 0 < L) (hα : 0 < α) (hb : 0 < L-α*(1-s)) :
    HasDerivAt (fun t => primal χ χ₁ t α s)
      ((χ₁ 1-s/L^2-(1-s)/(L*(L-α*(1-s))))/2) L := by
  have hB := (hasDerivAt_id L).sub_const (α*(1-s))
  have hquot := (hasDerivAt_id L).div hB hb.ne'
  have hlog := (hquot.log (div_ne_zero hL.ne' hb.ne')).div_const α
  have hsdiv := (hasDerivAt_const L s).div (hasDerivAt_id L) hL.ne'
  have hh := ((((hB.mul_const (χ₁ 1)).add_const (α*(χ 1-χ s))).add hsdiv).add hlog).div_const 2
  convert hh using 1
  · ext t
    rfl
  · dsimp only [Pi.sub_apply,Pi.div_apply,Pi.mul_apply,Pi.add_apply,id_eq]
    have hbn : -α+α*s+L ≠ 0 := by
      convert hb.ne' using 1
      ring
    field_simp [hL.ne',hα.ne',hb.ne',hbn]
    ring

theorem primal_hasDerivAt_location (χ χ₁ : ℝ → ℝ) {L α s : ℝ}
    (hχ : HasDerivAt χ (χ₁ s) s) (hL : 0 < L) (hα : 0 < α)
    (hb : 0 < L-α*(1-s)) :
    HasDerivAt (fun t => primal χ χ₁ L α t)
      ((α*(χ₁ 1-χ₁ s-(1-s)/(L*(L-α*(1-s)))))/2) s := by
  have hB := (hasDerivAt_const s L).sub
    (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).const_mul α)
  have hquot := (hasDerivAt_const s L).div hB hb.ne'
  have hlog := (hquot.log (div_ne_zero hL.ne' hb.ne')).div_const α
  have hdiff := ((hasDerivAt_const s (χ 1)).sub hχ).const_mul α
  have hh := ((((hB.mul_const (χ₁ 1)).add hdiff).add
    ((hasDerivAt_id s).div_const L)).add hlog).div_const 2
  convert hh using 1
  · ext t
    rfl
  · dsimp only [Pi.sub_apply,Pi.div_apply,Pi.mul_apply,Pi.add_apply,id_eq]
    have hbn : -α+α*s+L ≠ 0 := by
      convert hb.ne' using 1
      ring
    field_simp [hL.ne',hα.ne',hb.ne',hbn]
    ring

def primalAtBottom (χ χ₁ : ℝ → ℝ) (α s b : ℝ) : ℝ :=
  primal χ χ₁ (b+α*(1-s)) α s

theorem primalAtBottom_eq (χ χ₁ : ℝ → ℝ) (α s b : ℝ) :
    primalAtBottom χ χ₁ α s b=
      (b*χ₁ 1+α*(χ 1-χ s)+s/(b+α*(1-s))+
        Real.log ((b+α*(1-s))/b)/α)/2 := by
  unfold primalAtBottom primal
  rw [show b+α*(1-s)-α*(1-s)=b by ring]

end SlowEquilibration.LatitudeGroundTrial
