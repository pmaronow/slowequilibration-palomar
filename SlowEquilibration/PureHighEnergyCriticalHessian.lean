-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureHighEnergyMaximumConcentration
public import SlowEquilibration.PureHighEnergyBadHessianCount

/-! The all-high-critical-point Hessian bound in manuscript `lem:pc-hessian`.
Failure of the fixed positive margin forces either a bad marked critical
point in a fixed normalized energy window or an excessive original-field
maximum. The determinant-weighted first moment and ground concentration
bound these two events exponentially on one measurable disorder event.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureHighEnergyCriticalHessian

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows SphericalForm
open SphericalGaussianJet
open PairConditionalDeterminantMoments PureStationarity SphericalHessianMarginEvents
open PureHighEnergyMaximumConcentration PureHighEnergyBadHessianCount
open scoped ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma center_one (μ : FiniteMixture) :
    centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
  funext k
  simp [centerCoefficients]

variable (p : ℕ) (hp : 4 ≤ p)

local notation "μp" => (FiniteMixture.pure p (by omega) 1 (by positivity))
local notation "ep" => (pureEnergyConstant p (by omega))
local notation "Δp" => (ep - 2*Real.sqrt (((p : ℝ)-1)/(p : ℝ)))
local notation "κp" => ((p : ℝ)*Δp/4)

/-- Manuscript `lem:pc-hessian`: on one measurable event with exponentially
small complement, every original pure critical point above `N (e_p - τ)`
has the fixed intrinsic Hessian margin `κ = p Δ / 4`. -/
theorem pure_all_high_critical_hessian :
    0 < κp ∧
    ∃ τ a : ℝ, 0 < τ ∧ τ ≤ Δp/4 ∧ 0 < a ∧
      (∀ n : ℕ,
        MeasurableSet (highCriticalMarginEvent n μp ep τ κp)) ∧
      ∀ᶠ n : ℕ in atTop,
        (disorderLaw (n+2) (μp).maxDegree).real
          (highCriticalMarginEvent n μp ep τ κp)ᶜ ≤
        Real.exp (-a*(n+2 : ℕ)) := by
  classical
  obtain ⟨hκ, τ, b, hτ, hτΔ, hb, hMean⟩ := pure_high_window_bad_margin_mean p hp
  let a := min b (τ^2/8) / 2
  have ha : 0 < a := by
    exact half_pos (lt_min hb (by positivity))
  have hab : 2*a ≤ b := by
    dsimp [a]
    linarith [min_le_left b (τ^2/8)]
  have haτ : 2*a ≤ τ^2/8 := by
    dsimp [a]
    linarith [min_le_right b (τ^2/8)]
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hTail : Tendsto (fun n : ℕ => 3*Real.exp (-a*(n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop ha)
    simpa only [Function.comp_def, neg_mul, mul_zero] using h.const_mul 3
  have hAbsorb : ∀ᶠ n : ℕ in atTop, 3*Real.exp (-a*(n+2 : ℕ)) ≤ 1 :=
    (hTail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ h => h.le)
  refine ⟨hκ, τ, a, hτ, hτΔ, ha,
    fun n => highCriticalMarginEvent_measurable n μp ep τ κp, ?_⟩
  filter_upwards [hMean, pure_original_ground_concentration p hp hτ, hAbsorb]
    with n hn hGround hAbs
  let c := mixtureCoefficients μp
  let C := actualValueWindowCount (n+1) c (Icc (ep-τ) (ep+τ))
    (hessianMarginFailureMark c κp)
  let T := {J : Disorder (n+2) (μp).maxDegree |
    |sourceSphereMaximum n μp 1 J/(n+2 : ℕ)-ep| > τ}
  have hC : AEMeasurable C (disorderLaw (n+2) (μp).maxDegree) := by
    simpa only [center_one] using
      (actual_value_window_kacRice (n+1) (by omega) μp (Q := 1) (by positivity)
        (Icc (ep-τ) (ep+τ)) measurableSet_Icc
        (hessianMarginFailureMark c κp) (hessianMarginFailureMark_measurable c κp)).1
  have hSub : (highCriticalMarginEvent n μp ep τ κp)ᶜ ⊆
      {J | 1 ≤ C J} ∪ T := by
    intro J hJ
    by_cases hJT : J ∈ T
    · exact Or.inr hJT
    · apply Or.inl
      change ¬ (∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        surfaceGradient (field c J) u = 0 →
        (n+2 : ℕ)*(ep-τ) ≤ field c J u → sourceHessianMargin c κp J u) at hJ
      push Not at hJ
      obtain ⟨u, hu, hCrit, hHigh, hBad⟩ := hJ
      have hNr : (0 : ℝ) < (n+2 : ℕ) := by positivity
      have hUpper : sourceSphereMaximum n μp 1 J/(n+2 : ℕ) ≤ ep+τ := by
        have hNear : |sourceSphereMaximum n μp 1 J/(n+2 : ℕ)-ep| ≤ τ :=
          le_of_not_gt hJT
        linarith [(abs_le.mp hNear).2]
      obtain ⟨v, _, _, hMax, hValue⟩ := sourceSphereMaximum_attained n μp 1 J
      rw [center_one] at hMax hValue
      have huMax : field c J u ≤ sourceSphereMaximum n μp 1 J := by
        rw [hValue]
        exact hMax hu
      have hWindow : actualValue c J u ∈ Icc (ep-τ) (ep+τ) := by
        constructor
        · exact (le_div_iff₀ hNr).mpr (by simpa only [mul_comm] using hHigh)
        · exact (div_le_div_of_nonneg_right huMax hNr.le).trans hUpper
      have hOne := ENNReal.le_tsum
        (f := fun x : {x : Vector (n+2) | ‖x‖^2 = (n+2 : ℕ) ∧
          surfaceGradient (field c J) x = 0 ∧ actualValue c J x ∈ Icc (ep-τ) (ep+τ)} =>
          hessianMarginFailureMark c κp J x) ⟨u, hu, hCrit, hWindow⟩
      simpa only [hessianMarginFailureMark, ite_eq_right hBad,
        actualValueWindowCount, C, mem_ofPred_eq] using hOne
  have hCountMass : disorderLaw (n+2) (μp).maxDegree {J | 1 ≤ C J} ≤
      ENNReal.ofReal (Real.exp (-b*(n+2 : ℕ))) := by
    have hMarkov := mul_meas_ge_le_lintegral₀ hC 1
    calc
      _ ≤ ∫⁻ J, C J ∂disorderLaw (n+2) (μp).maxDegree := by
        simpa only [one_mul] using hMarkov
      _ ≤ _ := hn
  have hCountReal : (disorderLaw (n+2) (μp).maxDegree).real {J | 1 ≤ C J} ≤
      Real.exp (-b*(n+2 : ℕ)) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hCountMass).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  have hProb : (disorderLaw (n+2) (μp).maxDegree).real
      (highCriticalMarginEvent n μp ep τ κp)ᶜ ≤
      Real.exp (-b*(n+2 : ℕ)) + 2*Real.exp (-(n+2 : ℕ)*τ^2/8) := by
    exact (measureReal_mono hSub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hCountReal hGround))
  have hRate₁ : -b*(n+2 : ℕ) ≤ -a*(n+2 : ℕ) + -a*(n+2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hab (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
    linarith
  have hRate₂ : -(n+2 : ℕ)*τ^2/8 ≤ -a*(n+2 : ℕ) + -a*(n+2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right haτ (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
    nlinarith
  apply hProb.trans
  calc
    _ ≤ Real.exp (-a*(n+2 : ℕ) + -a*(n+2 : ℕ)) +
        2*Real.exp (-a*(n+2 : ℕ) + -a*(n+2 : ℕ)) := by
      exact add_le_add (Real.exp_le_exp.mpr hRate₁)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hRate₂) (by norm_num))
    _ = (3*Real.exp (-a*(n+2 : ℕ))) * Real.exp (-a*(n+2 : ℕ)) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (-a*(n+2 : ℕ)) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hAbs (Real.exp_pos _).le

end SlowEquilibration.PureHighEnergyCriticalHessian
