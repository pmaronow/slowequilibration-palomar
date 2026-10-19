-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSLinearEnvelope
public import SlowEquilibration.CSGeneralCovarianceStability

@[expose] public section
noncomputable section

namespace SlowEquilibration.CSCovarianceDirectionalDerivative

open Set Filter MeasureTheory CrisantiSommers CSCompactAttainment
open CSGeneralCovarianceStability CSStability
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The actual ordinary CS optimum has the expected covariance-direction
derivative for any locally minimizing family on a common cutoff. The cutoff
and global minimizer conditions are stated explicitly; subsequent results
obtain them from compact attainment and uniform truncation. -/
theorem hasDerivAt_monomial_covariance_minimum
    (β Q : ℝ) (η : ℝ → ℝ) (k : ℕ) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (hη : ContinuousOn η (Ico (0 : ℝ) 1))
    (ζ : ℝ → Admissible)
    (hq : ∀ t, HasCutoff (ζ t).law Q)
    (hmin : ∀ t ∈ Ioo (-1 : ℝ) 1,
      (ζ t).IsMinimizer β (fun r => η r+t*r^k)) :
    HasDerivAt (fun t => (ζ t).value β (fun r => η r+t*r^k))
      ((β^2/2)*(1-∫ r, r^k ∂(ζ 0).law)) 0 := by
  let E := ProbabilityMeasure (CutoffSpace Q)
  let a : E → ℝ := fun ν => (β^2/2)*(1-∫ r, r^k ∂law ν)
  let b : E → ℝ := fun ν => functional β η (law ν) Q
  let m : ℝ → E := fun t => liftLaw (ζ t).law (hq t)
  have hηQ : ContinuousOn η (Icc (0 : ℝ) Q) :=
    hη.mono (fun r hr => ⟨hr.1, hr.2.trans_lt hQ1⟩)
  have ha : Continuous a := by
    dsimp [a]
    exact (continuous_const.sub (continuous_energy_integral hQ1
      (fun r : ℝ => r^k) (continuous_id.pow k).continuousOn)).const_mul (β^2/2)
  have hb : Continuous b := continuous_functional hQ0 hQ1 β η hη
  obtain ⟨C, hC⟩ := (isCompact_range ha).isBounded.exists_norm_le
  have hC' (ν : E) : |a ν| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (a ν) ⟨ν, rfl⟩
  have hshift (t : ℝ) (ν : E) :
      CSLinearEnvelope.objective a b t ν =
        functional β (fun r => η r+t*r^k) (law ν) Q := by
    have hc := functional_amplitude_shift β t η (law ν)
      (law_hasCutoff hQ0 hQ1 ν) hηQ k
    dsimp [CSLinearEnvelope.objective, a, b]
    rw [hc]
    ring
  have hmin' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ ν : E,
      CSLinearEnvelope.objective a b t (m t) ≤
        CSLinearEnvelope.objective a b t ν := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht ν
    rw [hshift t (m t), hshift t ν]
    let τ : Admissible := ⟨law ν, inferInstance,
      ⟨Q, law_hasCutoff hQ0 hQ1 ν⟩⟩
    have hm := hmin t ht τ
    rw [(ζ t).value_eq β _ (hq t), τ.value_eq β _ (law_hasCutoff hQ0 hQ1 ν)] at hm
    simpa only [m, law_liftLaw] using hm
  have hmin0 : (ζ 0).IsMinimizer β η := by
    simpa only [zero_mul, add_zero] using hmin 0 (by norm_num)
  have hmin0' (ν : E) :
      CSLinearEnvelope.objective a b 0 (m 0) ≤
        CSLinearEnvelope.objective a b 0 ν :=
    (Filter.Eventually.self_of_nhds hmin') ν
  have hunique (ν : E)
      (hν : CSLinearEnvelope.objective a b 0 ν ≤
        CSLinearEnvelope.objective a b 0 (m 0)) : ν = m 0 := by
    apply fixedCutoff_unique (ζ 0) β η hη hmin0 (hq 0)
    simpa only [CSLinearEnvelope.objective, zero_mul, zero_add, b, m,
      law_liftLaw] using hν
  have hd := CSLinearEnvelope.hasDerivAt_minimum a b ha hb C hC' m 0
    hmin' hmin0' hunique
  convert hd using 1
  · ext t
    rw [hshift t (m t)]
    simp only [m, law_liftLaw]
    exact (ζ t).value_eq β _ (hq t)
  · simp only [a, m, law_liftLaw]

/-- Select actual global minimizers for the locally perturbed covariance.
The arbitrary outside-neighborhood branch gives a total Lean function while
preserving the derivative at zero. -/
def locallyPerturbedMinimizer (β : ℝ) (η : ℝ → ℝ) (k : ℕ) (L : ℝ≥0)
    (hL0 : LipschitzOnWith L η (Icc (0 : ℝ) 1))
    (hL : ∀ t ∈ Ioo (-1 : ℝ) 1,
      LipschitzOnWith L (fun r => η r+t*r^k) (Icc (0 : ℝ) 1))
    (t : ℝ) : Admissible :=
  if ht : t ∈ Ioo (-1 : ℝ) 1 then
    lipschitzMinimizer β (fun r => η r+t*r^k) L (hL t ht)
  else lipschitzMinimizer β η L hL0

/-- Compact attainment and the uniform entropy cutoff discharge the
fixed-cutoff premises of the monomial covariance envelope theorem. -/
theorem hasDerivAt_actual_monomial_covariance_minimum
    (β : ℝ) (η : ℝ → ℝ) (k : ℕ) (L : ℝ≥0)
    (hL0 : LipschitzOnWith L η (Icc (0 : ℝ) 1))
    (hL : ∀ t ∈ Ioo (-1 : ℝ) 1,
      LipschitzOnWith L (fun r => η r+t*r^k) (Icc (0 : ℝ) 1)) :
    HasDerivAt
      (fun t => (locallyPerturbedMinimizer β η k L hL0 hL t).value β
        (fun r => η r+t*r^k))
      ((β^2/2)*(1-∫ r, r^k ∂
        (locallyPerturbedMinimizer β η k L hL0 hL 0).law)) 0 := by
  let ζ := locallyPerturbedMinimizer β η k L hL0 hL
  obtain ⟨Q,hQ,hcoef⟩ := exists_uniform_cutoff β L
  have hq (t : ℝ) : HasCutoff (ζ t).law Q := by
    by_cases ht : t ∈ Ioo (-1 : ℝ) 1
    · simpa only [ζ, locallyPerturbedMinimizer, dite_eq_left ht] using
        minimizer_hasCutoff_of_lipschitz
          (lipschitzMinimizer β (fun r => η r+t*r^k) L (hL t ht)) β
          (fun r => η r+t*r^k)
          (lipschitzMinimizer_isMinimizer β (fun r => η r+t*r^k) L (hL t ht))
          L (hL t ht) hQ.1.le hQ.2 hcoef
    · simpa only [ζ, locallyPerturbedMinimizer, dite_eq_right ht] using
        minimizer_hasCutoff_of_lipschitz
          (lipschitzMinimizer β η L hL0) β η
          (lipschitzMinimizer_isMinimizer β η L hL0)
          L hL0 hQ.1.le hQ.2 hcoef
  have hm (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      (ζ t).IsMinimizer β (fun r => η r+t*r^k) := by
    simpa only [ζ, locallyPerturbedMinimizer, dite_eq_left ht] using
      lipschitzMinimizer_isMinimizer β (fun r => η r+t*r^k) L (hL t ht)
  exact hasDerivAt_monomial_covariance_minimum β Q η k hQ.1.le hQ.2
    (hL0.continuousOn.mono (fun r hr => ⟨hr.1,hr.2.le⟩)) ζ hq hm

end SlowEquilibration.CSCovarianceDirectionalDerivative
