-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundPrimalCoercivity

/-! The literal one-step primal has a global minimum at every positive
fixed slope. The parameters are compactified by the proved sublevel
bounds, including the strictly positive bottom height. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open Set
set_option maxHeartbeats 600000

theorem exists_global_primal_minimum (χ χ₁ : ℝ → ℝ) {α : ℝ}
    (hα : 0 < α) (hχ : ContinuousOn χ (Icc (0 : ℝ) 1))
    (hmono : MonotoneOn χ (Icc (0 : ℝ) 1)) (hχ₁ : 0 < χ₁ 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ b > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ c > 0,
        primalAtBottom χ χ₁ α s b ≤ primalAtBottom χ χ₁ α t c := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl,by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num,le_rfl⟩
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1, χ t ≤ χ 1 :=
    fun t ht => hmono ht h1 ht.2
  let R := primalAtBottom χ χ₁ α 0 1+1
  have hR0 : primalAtBottom χ χ₁ α 0 1 ≤ R := by dsimp [R];linarith
  obtain ⟨hR,hupper,hfloor⟩ := primalAtBottom_sublevel_bounds χ χ₁ hα h0
    (show (0 : ℝ) < 1 by norm_num) (hdiff 0 h0) hχ₁ hR0
  let bmin := min (1/(4*R)) (α/2)*Real.exp (-2*R*α)
  let bmax := 2*R/χ₁ 1
  have hbmin : 0 < bmin := by dsimp [bmin]; positivity
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc bmin bmax
  let F : ℝ × ℝ → ℝ := fun p => primalAtBottom χ χ₁ α p.1 p.2
  have hw : (0,1) ∈ S := ⟨h0,hfloor,hupper⟩
  have hsp : ∀ p ∈ S, 0 < p.2 := fun p hp => hbmin.trans_le hp.2.1
  have hL : ∀ p ∈ S, 0 < p.2+α*(1-p.1) := by
    intro p hp
    have hb := hsp p hp
    have hbound := hp.1.2
    nlinarith
  have hLC : Continuous (fun p : ℝ × ℝ => p.2+α*(1-p.1)) := by fun_prop
  have hχC : ContinuousOn (fun p : ℝ × ℝ => χ p.1) S :=
    hχ.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hquot : ContinuousOn (fun p : ℝ × ℝ =>
      (p.2+α*(1-p.1))/p.2) S :=
    hLC.continuousOn.div continuous_snd.continuousOn (fun p hp => (hsp p hp).ne')
  have hlog : ContinuousOn (fun p : ℝ × ℝ =>
      Real.log ((p.2+α*(1-p.1))/p.2)) S :=
    hquot.log (fun p hp => div_ne_zero (hL p hp).ne' (hsp p hp).ne')
  have hF : ContinuousOn F S := by
    dsimp only [F]
    simp only [primalAtBottom_eq]
    exact (((continuous_snd.continuousOn.mul continuousOn_const).add
      (continuousOn_const.mul (continuousOn_const.sub hχC))).add
        (continuous_fst.continuousOn.div hLC.continuousOn
          (fun p hp => (hL p hp).ne'))).add (hlog.div_const α) |>.div_const 2
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn ⟨(0,1),hw⟩ hF
  refine ⟨p.1,hp.1,p.2,hsp p hp,?_⟩
  intro t ht c hc
  by_cases htc : primalAtBottom χ χ₁ α t c ≤ R
  · obtain ⟨_hR',hu,hb⟩ := primalAtBottom_sublevel_bounds χ χ₁ hα ht hc
      (hdiff t ht) hχ₁ htc
    exact hmin (show (t,c) ∈ S from ⟨ht,hb,hu⟩)
  · have hminw : F p ≤ F (0,1) := hmin hw
    have hwR : F (0,1) ≤ R := hR0
    exact (hminw.trans hwR).trans (le_of_not_ge htc)

end SlowEquilibration.LatitudeGroundTrial
