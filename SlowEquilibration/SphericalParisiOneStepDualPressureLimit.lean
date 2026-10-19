-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiOneStepPressureNormalization
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Genuine thermodynamic dual one-step pressure upper. The actual finite
Gaussian REM lower and its exponential label count are evaluated internally.
No spherical pressure limit, ground formula or desired upper is an input. -/

namespace SlowEquilibration.SphericalParisiOneStepDualPressureLimit
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledOriginalEndpoint SphericalParisiGaussianREM
open SphericalParisiOneStepPressureNormalization SphericalParisiOneStepDualScalar SphericalParisiLabeledBregman
open scoped Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- True dual pressure upper for every actual positive-dimension unit-sphere
probability reference family, at each fixedbeta>=alpha>0. The REM parameter
and finite label count are chosen constructively inside the proof. -/
theorem eventual_spin_pressure_oneStepDual_upper (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    (μ : (N : ℕ) → Measure (UnitSphere N)) (hμ : ∀ N,0 < N → IsProbabilityMeasure (μ N))
    {α β κ q : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,originalSpinPressure (μ N) d c β/(β*(N : ℝ)) ≤ oneStepDual d c α q κ+ε := by
  let B := covarianceBudget c
  let Δ := theta d c 1-theta d c q
  let F := 1/α-1/β
  have hβ : 0 < β := hα.trans_le hαβ
  have hB : 0 ≤ B := covarianceBudget_nonnegative c hc
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (theta_monotone_positive d c hc hd hq hq1)
  have hF : 0 ≤ F := sub_nonneg.mpr (one_div_le_one_div_of_le hα hαβ)
  let e := min (1/2 : ℝ) (ε/(6*(β*B+1)))
  have he : 0 < e := lt_min (by norm_num) (div_pos hε (by positivity))
  have he1 : e ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have heSmall : β*B*e ≤ ε/6 := by
    have H := (le_div_iff₀ (show 0 < 6*(β*B+1) by positivity)).mp (min_le_right (1/2 : ℝ) (ε/(6*(β*B+1))))
    nlinarith
  obtain ⟨V,hV,hUpper⟩ := exists_actual_normalized_one_step_pressure_upper he he1 he
  let δ := ε/(6*(F+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδSmall : F*δ ≤ ε/6 := by
    have H : 6*(F+1)*δ=ε := by unfold δ;field_simp
    nlinarith
  let γ := α^2*Δ/2+δ
  have hγ : 0 < γ := add_pos_of_nonneg_of_pos (by positivity) hδ
  let u := α*Real.sqrt Δ
  let lam := β*Real.sqrt Δ
  have hu : 0 ≤ u := mul_nonneg hα.le (Real.sqrt_nonneg _)
  have hlam : 0 ≤ lam := mul_nonneg hβ.le (Real.sqrt_nonneg _)
  have huSq : u^2=α^2*Δ := by unfold u;rw [mul_pow,Real.sq_sqrt hΔ]
  have hRate : u^2/2 < γ := by rw [huSq];unfold γ;linarith
  have hRem := eventual_rem_lower hlam hu hRate (β*ε/6) (by positivity)
  let C := 2*V^2/β+F*Real.log 2
  have hDecay : ∀ᶠ N : ℕ in atTop,C/(N : ℝ) < ε/6 :=
    (tendsto_const_div_atTop_nhds_zero_nat C).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/6))
  have hA : 0 ≤ xi1 d c 1-xi1 d c q := sub_nonneg.mpr (xi1_monotone_positive d c hc hq hq1)
  have hκ : 0 < κ := by linarith [mul_nonneg hα.le hA]
  have hDual := moment_dual_sub_theta_eq d c hα hκ hmargin
  filter_upwards [hRem,hDecay,eventually_gt_atTop (0 : ℕ)] with N hRemN hDecayN hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have : IsProbabilityMeasure (μ N) := hμ N hN
  let k := labelCount γ N
  let : NeZero k := ⟨(labelCount_pos γ N).ne'⟩
  let R := ∫ y,remLogAverage N k lam y ∂SYK.standardGaussianMeasureOnEuclidean (Fin k)
  have HU := hUpper N k hN (μ N) σ d c hc hd β α κ q V hα hαβ hq hq1 le_rfl hmargin
  change originalSpinPressure (μ N) d c β/(β*(N : ℝ))+R/(β*(N : ℝ)) ≤
    oneStepMomentDual κ α (xi1 d c q) (xi1 d c 1-xi1 d c q)+
      F*Real.log (k : ℝ)/(N : ℝ)+2*V^2/(β*(N : ℝ))+β*B*(e+e)/2 at HU
  have hCount := labelCount_log_upper hγ.le N
  have hEntropy : F*Real.log (k : ℝ)/(N : ℝ) ≤ F*γ+F*Real.log 2/(N : ℝ) := by
    have H := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCount hF) hNr.le
    apply H.trans_eq
    field_simp
  have hR : α*Δ-α^2*Δ/(2*β)-ε/6 ≤ R/(β*(N : ℝ)) := by
    have H := div_le_div_of_nonneg_right hRemN hβ.le
    have hProd : lam*u=β*α*Δ := by
      unfold lam u
      calc
        _ = β*α*(Real.sqrt Δ*Real.sqrt Δ) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hΔ]
    have hLeft : (lam*u-u^2/2-β*ε/6)/β=α*Δ-α^2*Δ/(2*β)-ε/6 := by
      rw [hProd,huSq]
      field_simp
    rw [hLeft] at H
    apply H.trans_eq
    change (R/(N : ℝ))/β=R/(β*(N : ℝ))
    field_simp
  have hCancel : F*γ-α*Δ+α^2*Δ/(2*β)=-α*Δ/2+F*δ := by
    unfold F γ
    field_simp
    ring
  have hC : 2*V^2/(β*(N : ℝ))+F*Real.log 2/(N : ℝ)=C/(N : ℝ) := by
    unfold C
    field_simp
  have hPosError : β*B*(e+e)/2=β*B*e := by ring
  rw [hPosError] at HU
  have hBound : originalSpinPressure (μ N) d c β/(β*(N : ℝ)) ≤
      oneStepMomentDual κ α (xi1 d c q) (xi1 d c 1-xi1 d c q)-α*Δ/2+F*δ+C/(N : ℝ)+ε/6+β*B*e := by
    have hAlg : F*γ+F*Real.log 2/(N : ℝ)+2*V^2/(β*(N : ℝ))-
        (α*Δ-α^2*Δ/(2*β)-ε/6)=-α*Δ/2+F*δ+C/(N : ℝ)+ε/6 := by
      linarith [hCancel,hC]
    linarith [HU,hR,hEntropy,hAlg]
  change oneStepMomentDual κ α (xi1 d c q) (xi1 d c 1-xi1 d c q)-α*Δ/2=oneStepDual d c α q κ at hDual
  rw [hDual] at hBound
  linarith [hBound,hδSmall,hDecayN,heSmall]

end
end SlowEquilibration.SphericalParisiOneStepDualPressureLimit
