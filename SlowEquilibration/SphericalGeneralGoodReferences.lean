-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralCapCoreCollarTails

/-! A genuine high-probability disorder event supporting the simultaneous
cap, core and collar bounds. The partition tests and annealed concentration
are both instantiated from proved estimates for the physical model. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


theorem general_goodCapCoreCollarEvent_eventually (μ : FiniteMixture)
    {β δ q₁ q₂ w : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hδ : 0 < δ) (hw : 0 < w) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        (goodCapCoreCollarEvent (N := N) (mixtureCoefficients μ) β
          (β^2*μ.xi 1/2) (plantedCoreCost μ β) (plantedCollarGap μ β q₂) δ
          q₁ q₂ (Thresholds.qStar μ.xi β) w (Real.exp (-a * (N : ℝ))))ᶜ ≤
        11 * Real.exp (-a * (N : ℝ)) := by
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  obtain ⟨c,hcpos,hQ⟩ := general_gibbsReference_capCoreCollar_bad_tail μ hβ hβs hc hδ hw
  have hpressure := annealed_logPartition_concentration_eventually_of_pressure_limit μ hβpos
    (general_quenchedPressure_tendsto_annealed_le_static μ hβpos.le hβs) hδ
  let d := δ^2 / (8 * β^2 * μ.xi 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let a := min (c/2) d
  have ha : 0 < a := lt_min (half_pos hcpos) hd
  refine ⟨a,ha,?_⟩
  filter_upwards [hQ,hpressure,eventually_ge_atTop (1 : ℕ)] with N hQN hpN hN
  have hbase := goodCapCoreCollarEvent_failure_le hN (mixtureCoefficients μ) β
    (β^2*μ.xi 1/2) (plantedCoreCost μ β) (plantedCollarGap μ β q₂) δ
    q₁ q₂ (Thresholds.qStar μ.xi β) w (Real.exp_pos (-a * (N : ℝ)))
  have hp : (disorderLaw N μ.maxDegree).real
      {D | δ < |Real.log (partition N β (field (mixtureCoefficients μ) D))/(N : ℝ)-β^2*μ.xi 1/2|} ≤
        2 * Real.exp (-a * (N : ℝ)) := by
    apply hpN.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have he : -(δ^2*(N : ℝ))/(8*β^2*μ.xi 1) = -d*(N : ℝ) := by dsimp [d]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (Nat.cast_nonneg N)
  have hq : (gibbsReferenceLaw (mixtureCoefficients μ) β).real
      (capCoreCollarBadEvent (N := N) (mixtureCoefficients μ) β
        (β^2*μ.xi 1/2) (plantedCoreCost μ β) (plantedCollarGap μ β q₂) δ
        q₁ q₂ (Thresholds.qStar μ.xi β) w) / Real.exp (-a * (N : ℝ)) ≤
        9 * Real.exp (-a * (N : ℝ)) := by
    calc
      _ ≤ (9 * Real.exp (-c * (N : ℝ))) / Real.exp (-a * (N : ℝ)) :=
        div_le_div_of_nonneg_right hQN (Real.exp_pos _).le
      _ = 9 * Real.exp ((-c+a) * (N : ℝ)) := by
        rw [mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 9)
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
        have hca : a ≤ c/2 := min_le_left _ _
        linarith
  exact hbase.trans ((add_le_add hp hq).trans_eq (by ring))

end
end SlowEquilibration.SphericalModel
