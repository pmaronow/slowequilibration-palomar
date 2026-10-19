module
public import FRSB.ParisiMeasureTopology
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Continuity and actual attainment of the Parisi variational functional.
No minimizer, PDE continuity, or control representation is supplied as a premise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FRSB
open Paper

/-- CDF distance is symmetric. -/
theorem parisiCDFDistance_symm (μ ν : ParisiMeasure) :
    parisiCDFDistance μ ν = parisiCDFDistance ν μ := by
  unfold parisiCDFDistance
  apply intervalIntegral.integral_congr
  intro s _
  exact abs_sub_comm _ _

/-- A bounded multiplier preserves the integrated CDF difference bound. -/
theorem parisiCDF_integral_multiplier_sub_le (μ ν : ParisiMeasure)
    (a : ℝ → ℝ) (ha : Measurable a) (hb : ∀ s, ‖a s‖ ≤ 1) :
    ‖(∫ s in (0 : ℝ)..1, parisiCDF μ s * a s) -
      (∫ s in (0 : ℝ)..1, parisiCDF ν s * a s)‖ ≤ parisiCDFDistance μ ν := by
  have hi (ρ : ParisiMeasure) :
      IntervalIntegrable (fun s => parisiCDF ρ s * a s) volume (0 : ℝ) 1 := by
    apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
      ((parisiCDF_measurable ρ).mul ha).aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      change ‖parisiCDF ρ s * a s‖ ≤ 1
      rw [norm_mul, Real.norm_of_nonneg (parisiCDF_nonneg ρ s)]
      exact (mul_le_mul_of_nonneg_left (hb s) (parisiCDF_nonneg ρ s)).trans
        (by simpa only [mul_one] using parisiCDF_le_one ρ s)
  rw [← intervalIntegral.integral_sub (hi μ) (hi ν)]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun s _ => ?_)
    (parisiCDF_abs_diff_intervalIntegrable μ ν 0 1)
  rw [← sub_mul, norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hb s) (abs_nonneg _)).trans_eq (mul_one _)

/-- Uniform control-drift stability in the actual integrated CDF distance. -/
theorem parisiControlDrift_measure_sub_le {Ω : Type*} (β : ℝ)
    (μ ν : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : ∀ ω, Measurable (fun s => A s ω)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlDrift β μ A ω - parisiControlDrift β ν A ω‖ ≤
      β ^ 2 * parisiCDFDistance μ ν := by
  unfold parisiControlDrift
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (sq_nonneg β)]
  exact mul_le_mul_of_nonneg_left
    (parisiCDF_integral_multiplier_sub_le μ ν (fun s => A s ω) (hA ω) (fun s => hb s ω))
    (sq_nonneg β)

/-- Uniform control-cost stability in the actual integrated CDF distance. -/
theorem parisiControlCost_measure_sub_le {Ω : Type*} (β : ℝ)
    (μ ν : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : ∀ ω, Measurable (fun s => A s ω)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlCost β μ A ω - parisiControlCost β ν A ω‖ ≤
      β ^ 2 / 2 * parisiCDFDistance μ ν := by
  unfold parisiControlCost
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply parisiCDF_integral_multiplier_sub_le μ ν (fun s => A s ω ^ 2)
    ((hA ω).pow_const 2)
  intro s
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hb s ω)

/-- The bound is pathwise, so unbounded Gaussian endpoint noise cancels. -/
theorem parisiControlPayoff_measure_sub_le {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (μ ν : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : ∀ ω, Measurable (fun s => A s ω)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlPayoff β h B A μ ω - parisiControlPayoff β h B A ν ω‖ ≤
      (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ ν := by
  have hlog := lipschitzWith_logcosh.dist_le_mul
    (h + β * B ω + parisiControlDrift β μ A ω)
    (h + β * B ω + parisiControlDrift β ν A ω)
  simp only [dist_eq_norm, NNReal.coe_one, one_mul, add_sub_add_left_eq_sub] at hlog
  have hd := parisiControlDrift_measure_sub_le β μ ν A hA hb ω
  have hc := parisiControlCost_measure_sub_le β μ ν A hA hb ω
  unfold parisiControlPayoff
  rw [show (Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω)) -
      parisiControlCost β μ A ω) -
      (Real.log (Real.cosh (h + β * B ω + parisiControlDrift β ν A ω)) -
      parisiControlCost β ν A ω) =
      (Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω)) -
      Real.log (Real.cosh (h + β * B ω + parisiControlDrift β ν A ω))) -
      (parisiControlCost β μ A ω - parisiControlCost β ν A ω) by ring]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Expected control objectives satisfy the same uniform CDF-distance bound. -/
theorem parisiControlObjective_measure_sub_le (β h : ℝ) (μ ν : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    ‖parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ -
      parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A ν‖ ≤
      (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ ν := by
  have hi (ρ : ParisiMeasure) := integrable_parisiControlPayoff canonicalBrownianMeasure
    β h (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one A hA.measurable hA.bounded ρ
  unfold parisiControlObjective
  rw [← integral_sub (hi μ) (hi ν)]
  have hh := norm_integral_le_of_norm_le_const
    (μ := canonicalBrownianMeasure)
    (C := (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ ν)
    (Eventually.of_forall fun ω => parisiControlPayoff_measure_sub_le β h
      (canonicalBrownian 1) μ ν A
      (fun ω => hA.measurable.comp (measurable_id.prodMk measurable_const)) hA.bounded ω)
  simpa using hh

/-- The actual constructed PDE value is Lipschitz in integrated CDF distance. -/
theorem parisiPotential_initial_measure_sub_le (β h : ℝ) (μ ν : ParisiMeasure) :
    ‖parisiPotential β μ (0, h) - parisiPotential β ν (0, h)‖ ≤
      (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ ν := by
  by_cases hβ : β = 0
  · subst β
    simp only [parisiPotential_zero, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, le_refl]
  · have hup (ρ σ : ParisiMeasure) :
        parisiPotential β ρ (0, h) - parisiPotential β σ (0, h) ≤
          (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance ρ σ := by
      let A := selectedParisiControl β h hβ ρ
      have hA := isParisiAdmissibleControl_selectedParisiControl β h hβ ρ
      have he := parisiControlObjective_selected_eq_potential β h hβ ρ
      have hl := parisiControlObjective_le_potential β h hβ σ A hA
      have hb := parisiControlObjective_measure_sub_le β h ρ σ A hA
      have hreal := le_abs_self
        (parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A ρ -
        parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A σ)
      rw [← Real.norm_eq_abs] at hreal
      change parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A ρ = _ at he
      linarith
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hh := hup ν μ
      rw [parisiCDFDistance_symm ν μ] at hh
      linarith
    · exact hup μ ν

/-- The exact paper functional is Lipschitz in integrated CDF distance. -/
theorem parisiPDEFunctional_measure_sub_le (β h : ℝ) (μ ν : ParisiMeasure) :
    ‖parisiPDEFunctional β h μ - parisiPDEFunctional β h ν‖ ≤
      2 * β ^ 2 * parisiCDFDistance μ ν := by
  have hp := parisiPotential_initial_measure_sub_le β h μ ν
  have hc := parisiCorrection_sub_le β μ ν
  unfold parisiPDEFunctional parisiFunctional
  rw [show (Real.log 2 + parisiPotential β μ (0, h) -
      β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, s * parisiCDF μ s) -
      (Real.log 2 + parisiPotential β ν (0, h) -
      β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, s * parisiCDF ν s) =
      (parisiPotential β μ (0, h) - parisiPotential β ν (0, h)) -
      (β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF μ s) -
      β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF ν s)) by ring]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Weak continuity is proved for the actual PDE functional. -/
theorem continuous_parisiPDEFunctional (β h : ℝ) :
    Continuous (parisiPDEFunctional β h) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun ν => norm_nonneg _)
    (parisiPDEFunctional_measure_sub_le β h · μ)
  simpa only [mul_zero, id_eq] using
    (tendsto_const_nhds (x := 2 * β ^ 2)).mul
      (tendsto_parisiCDFDistance_of_tendsto (μ := μ) tendsto_id)

/-- An actual minimizing overlap measure exists for every beta and field. -/
theorem exists_parisi_minimizer (β h : ℝ) :
    ∃ μ : ParisiMeasure, ∀ ν : ParisiMeasure,
      parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν := by
  obtain ⟨μ, _, hμ⟩ := (isCompact_univ : IsCompact (univ : Set ParisiMeasure)).exists_isMinOn
    (show (univ : Set ParisiMeasure).Nonempty from ⟨diracOverlap 0 (by norm_num), mem_univ _⟩)
    (continuous_parisiPDEFunctional β h).continuousOn
  exact ⟨μ, fun ν => hμ (mem_univ ν)⟩

/-- A selected actual minimizer. Uniqueness is not inferred from existence. -/
def parisiMinimizer (β h : ℝ) : ParisiMeasure :=
  Classical.choose (exists_parisi_minimizer β h)

theorem parisiMinimizer_minimal (β h : ℝ) (ν : ParisiMeasure) :
    parisiPDEFunctional β h (parisiMinimizer β h) ≤ parisiPDEFunctional β h ν :=
  Classical.choose_spec (exists_parisi_minimizer β h) ν

/-- The selected minimizing value equals the genuine variational infimum. -/
theorem parisiMinimizer_value (β h : ℝ) :
    parisiPDEFunctional β h (parisiMinimizer β h) = parisiPDEValue β h := by
  have hb : BddBelow {r : ℝ | ∃ μ : ParisiMeasure, r = parisiPDEFunctional β h μ} := by
    refine ⟨parisiPDEFunctional β h (parisiMinimizer β h), ?_⟩
    rintro r ⟨μ, rfl⟩
    exact parisiMinimizer_minimal β h μ
  unfold parisiPDEValue
  apply le_antisymm
  · apply le_csInf (parisiPDESet_nonempty β h)
    rintro r ⟨μ, rfl⟩
    exact parisiMinimizer_minimal β h μ
  · exact csInf_le hb ⟨parisiMinimizer β h, rfl⟩

end FRSB
