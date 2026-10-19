-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSQuadraticEnvelope

@[expose] public section

open Set Filter MeasureTheory
open SlowEquilibration.CrisantiSommers
open SlowEquilibration.CSCompactAttainment
open SlowEquilibration.CSStability
open SlowEquilibration.CSParisiMeasure
open SlowEquilibration.QuadraticEnvelope
open scoped Topology NNReal

namespace SlowEquilibration.CSVariationalTemperatureDerivative

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The actual finite-mixture Crisanti--Sommers minimum has the temperature
derivative specified by its unique minimizing probability law. -/
theorem variationalValue_hasDerivAt (μ : FiniteMixture) (β : ℝ) :
    HasDerivAt (variationalValue μ)
      (β * (μ.xi 1 - ∫ r, μ.xi r ∂(canonicalMinimizer μ β).law)) β := by
  let L := mixtureLipschitzConstant μ
  have hL : LipschitzOnWith L μ.xi (Icc (0 : ℝ) 1) := mixture_xi_lipschitzOn μ
  obtain ⟨q, hq, hcoef⟩ := exists_uniform_cutoff (|β| + 1) L
  have hcont : ContinuousOn μ.xi (Ico (0 : ℝ) 1) :=
    fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  have hsmallβ : |β - β| < 1 := by norm_num
  have hcut (t : ℝ) (ht : |t - β| < 1) :
      HasCutoff (canonicalMinimizer μ t).law q := by
    have habs : |t| < |β| + 1 := by
      calc
        |t| = |(t - β) + β| := by ring
        _ ≤ |t - β| + |β| := abs_add_le _ _
        _ < |β| + 1 := by linarith
    have hsq : t ^ 2 ≤ (|β| + 1) ^ 2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg t) habs.le 2
      nlinarith [hh, sq_abs t]
    have hh : t ^ 2 * (L : ℝ) ≤ (|β| + 1) ^ 2 * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hsq L.coe_nonneg
    exact canonicalMinimizer_hasCutoff_of_lipschitz μ t L hL
      hq.1.le hq.2 (hh.trans hcoef)
  let m : ℝ → ProbabilityMeasure (CutoffSpace q) := fun t =>
    if ht : |t - β| < 1 then liftLaw (canonicalMinimizer μ t).law (hcut t ht)
    else liftLaw (canonicalMinimizer μ β).law (hcut β hsmallβ)
  have hmβ : m β = liftLaw (canonicalMinimizer μ β).law (hcut β hsmallβ) := by
    simp only [m, dite_eq_left hsmallβ]
  have hmt (t : ℝ) (ht : |t - β| < 1) :
      m t = liftLaw (canonicalMinimizer μ t).law (hcut t ht) := by
    simp only [m, dite_eq_left ht]
  let a : ProbabilityMeasure (CutoffSpace q) → ℝ :=
    fun ν => (μ.xi 1 - ∫ r, μ.xi r ∂law ν) / 2
  let b : ProbabilityMeasure (CutoffSpace q) → ℝ :=
    fun ν => ((∫ t in (0 : ℝ)..q, (xHat (law ν) t)⁻¹) + Real.log (1 - q)) / 2
  have ha : Continuous a := by
    exact (continuous_const.sub (continuous_energy_integral hq.2 μ.xi hcont)).div_const 2
  have hb : Continuous b := by
    exact ((continuous_entropy_integral hq.1.le hq.2).add_const
      (Real.log (1 - q))).div_const 2
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((isCompact_range ha).isBounded)
  have hC' : ∀ ν, |a ν| ≤ C := by
    intro ν
    simpa only [Real.norm_eq_abs] using hC (a ν) ⟨ν, rfl⟩
  have hobj (t : ℝ) (ν : ProbabilityMeasure (CutoffSpace q)) :
      objective a b t ν = functional t μ.xi (law ν) q := by
    dsimp [objective, a, b, functional]
    ring
  have hnear : ∀ᶠ t in 𝓝 β, |t - β| < 1 := by
    have hc : ContinuousAt (fun t : ℝ => |t - β|) β :=
      (continuousAt_id.sub continuousAt_const).abs
    have ht : Tendsto (fun t : ℝ => |t - β|) (𝓝 β) (𝓝 0) := by
      simpa only [sub_self, abs_zero] using hc.tendsto
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hminimal (t : ℝ) (ht : |t - β| < 1)
      (ν : ProbabilityMeasure (CutoffSpace q)) :
      objective a b t (m t) ≤ objective a b t ν := by
    let ζν : Admissible := ⟨law ν, inferInstance,
      ⟨q, law_hasCutoff hq.1.le hq.2 ν⟩⟩
    have hh := canonicalMinimizer_isMinimizer μ t ζν
    rw [(canonicalMinimizer μ t).value_eq t μ.xi (hcut t ht),
      ζν.value_eq t μ.xi (law_hasCutoff hq.1.le hq.2 ν)] at hh
    rw [hobj, hobj, hmt t ht, law_liftLaw]
    exact hh
  have hmin : ∀ᶠ t in 𝓝 β, ∀ ν,
      objective a b t (m t) ≤ objective a b t ν := by
    filter_upwards [hnear] with t ht ν
    exact hminimal t ht ν
  have hminβ : ∀ ν, objective a b β (m β) ≤ objective a b β ν :=
    hminimal β hsmallβ
  have hunique : ∀ ν, objective a b β ν ≤ objective a b β (m β) → ν = m β := by
    intro ν hν
    rw [hobj, hmβ, hobj, law_liftLaw] at hν
    rw [hmβ]
    exact canonical_fixedCutoff_unique μ β (hcut β hsmallβ) ν
      (by simpa only [law_liftLaw] using hν)
  have hderiv := hasDerivAt_minimum a b ha hb C hC' m β hmin hminβ hunique
  have heq : (fun t => objective a b t (m t)) =ᶠ[𝓝 β] variationalValue μ := by
    filter_upwards [hnear] with t ht
    rw [hobj, hmt t ht, law_liftLaw]
    exact ((canonicalMinimizer μ t).value_eq t μ.xi (hcut t ht)).symm
  have hh := hderiv.congr_of_eventuallyEq heq.symm
  convert hh using 1
  rw [hmβ]
  simp only [a, law_liftLaw]
  ring

end
end SlowEquilibration.CSVariationalTemperatureDerivative
