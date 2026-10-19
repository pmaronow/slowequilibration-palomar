-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiOneStepPressureUpper

@[expose] public section

/-! Exact dimension/inverse-temperature normalization of the actual finite
one-step pressure inequality. The true iid Gaussian REM term remains
explicit; no REM or spherical pressure limit is supplied. -/

namespace SlowEquilibration.SphericalParisiOneStepPressureNormalization
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledOriginalEndpoint SphericalParisiGaussianREM
open SphericalParisiOneStepPressureUpper SphericalParisiOneStepDualScalar
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def oneStepMomentDual (κ α a0 a : ℝ) : ℝ :=
  κ/2-Real.log (1-α*a/κ)/(2*α)+a0/(2*(κ-α*a))

theorem actual_trial_expression_normalized {N k : ℕ} (hN : 0 < N)
    {β α κ a0 a : ℝ} (hβ : 0 < β) (hα : 0 < α) (hκ : 0 < κ)
    (hmargin : 0 < κ-α*a) :
    trialQuadraticExpression N k β a0 a (α/β) (κ*Real.sqrt (N : ℝ))/((β*(N : ℝ)))=
      oneStepMomentDual κ α a0 a+(1/α-1/β)*Real.log (k : ℝ)/(N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hm : (α/β)*(β*Real.sqrt (N : ℝ))=α*Real.sqrt (N : ℝ) := by field_simp
  have hf : κ*Real.sqrt (N : ℝ)-(α/β)*(β*Real.sqrt (N : ℝ))*a=
      Real.sqrt (N : ℝ)*(κ-α*a) := by rw [hm];ring
  have he : 1-((α/β)*(β*Real.sqrt (N : ℝ)))*a/(κ*Real.sqrt (N : ℝ))=1-α*a/κ := by
    rw [hm]
    field_simp
  unfold trialQuadraticExpression oneStepMomentDual
  rw [he,hf]
  field_simp [hβ.ne',hα.ne',hκ.ne',hs.ne',hNr.ne',hmargin.ne']
  rw [Real.sq_sqrt hNr.le]
  ring

/-- The normalized determinant trial minus its scalar correction is the
literal one-step dual functional, with a positive Gaussian moment margin. -/
theorem moment_dual_sub_theta_eq {σ : Type*} [Fintype σ] (d : σ → ℕ) (c : σ → ℝ)
    {α q κ : ℝ} (_hα : 0 < α) (hκ : 0 < κ)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q)) :
    oneStepMomentDual κ α (xi1 d c q) (xi1 d c 1-xi1 d c q)-
      α*(theta d c 1-theta d c q)/2=oneStepDual d c α q κ := by
  have hz : 0 < 1-α*(xi1 d c 1-xi1 d c q)/κ := by
    rw [sub_div' hκ.ne',one_mul]
    exact div_pos hmargin hκ
  have hRatio : κ/(κ-α*(xi1 d c 1-xi1 d c q))=
      (1-α*(xi1 d c 1-xi1 d c q)/κ)⁻¹ := by field_simp
  unfold oneStepDual oneStepMomentDual
  rw [hRatio,Real.log_inv]
  ring

/-- Exact true physical finite normalized upper, with m=alpha/beta.
Only primitive finite covariance positivity and an actual positive trial
margin are required. The independent iid scalar REM is its real integral. -/
theorem exists_actual_normalized_one_step_pressure_upper {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ V : ℝ,1 ≤ V ∧
      ∀ (N k : ℕ),0 < N → ∀ [NeZero k]
        (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ]
        (σ : Type*) [Fintype σ] [DecidableEq σ]
        (d : σ → ℕ) (c : σ → ℝ),
        (∀ i,0 ≤ c i) → (∀ i,1 ≤ d i) →
        ∀ (β α κ q v : ℝ),0 < α → α ≤ β → 0 ≤ q → q ≤ 1 → V ≤ v →
          0 < κ-α*(xi1 d c 1-xi1 d c q) →
        originalSpinPressure μ d c β/(β*(N : ℝ))+
          (∫ y,remLogAverage N k (β*Real.sqrt (theta d c 1-theta d c q)) y
            ∂SYK.standardGaussianMeasureOnEuclidean (Fin k))/(β*(N : ℝ)) ≤
          oneStepMomentDual κ α (xi1 d c q) (xi1 d c 1-xi1 d c q)+
            (1/α-1/β)*Real.log (k : ℝ)/(N : ℝ)+2*v^2/(β*(N : ℝ))+
            β*SphericalParisiLabeledBregman.covarianceBudget c*(ε+η)/2 := by
  obtain ⟨V,hV,H⟩ := exists_actual_finite_one_step_pressure_upper hε hε1 hη
  refine ⟨V,hV,?_⟩
  intro N k hN _ μ _ σ _ _ d c hc hd β α κ q v hα hαβ hq hq1 hv hmargin
  have hβ : 0 < β := hα.trans_le hαβ
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hA : 0 ≤ xi1 d c 1-xi1 d c q := sub_nonneg.mpr (xi1_monotone_positive d c hc hq hq1)
  have hκ : 0 < κ := by linarith [mul_nonneg hα.le hA]
  have hm : 0 < α/β := div_pos hα hβ
  have hm1 : α/β ≤ 1 := (div_le_one hβ).mpr hαβ
  have hmf : κ*Real.sqrt (N : ℝ)-(α/β)*(β*Real.sqrt (N : ℝ))*(xi1 d c 1-xi1 d c q)=
      Real.sqrt (N : ℝ)*(κ-α*(xi1 d c 1-xi1 d c q)) := by field_simp
  have hMoment : 0 < κ*Real.sqrt (N : ℝ)-(α/β)*(β*Real.sqrt (N : ℝ))*(xi1 d c 1-xi1 d c q) := by
    rw [hmf]
    exact mul_pos hs hmargin
  have HU := H N k μ σ d c hc hd β q v (α/β) (κ*Real.sqrt (N : ℝ))
    hβ.le hq hq1 hv hm hm1 (mul_pos hκ hs) hMoment
  have HD := div_le_div_of_nonneg_right HU (mul_pos hβ hNr).le
  rw [add_div,add_div,add_div,
    actual_trial_expression_normalized hN hβ hα hκ hmargin] at HD
  apply HD.trans_eq
  field_simp [hβ.ne',hNr.ne']

end
end SlowEquilibration.SphericalParisiOneStepPressureNormalization
