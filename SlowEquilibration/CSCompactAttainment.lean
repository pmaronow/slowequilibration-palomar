-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTruncation
public import SlowEquilibration.MixtureThresholds
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Compact attainment of the actual Crisanti--Sommers functional

Probability laws on a closed cutoff interval carry Mathlib's weak topology.
Prokhorov compactness and weak continuity of test integrals give continuity of
the ordinary functional; reciprocal entropy uses the uniform lower bound
`xHat ≥ 1-Q` and dominated convergence. Actual minimizers are obtained by the
extreme value theorem, and uniform truncation promotes fixed-cutoff attainment
to the full admissible variational class.
-/

namespace SlowEquilibration.CSCompactAttainment

open MeasureTheory Set Filter CrisantiSommers
open scoped Topology NNReal

/-- The actual compact state space at a fixed support cutoff. -/
abbrev CutoffSpace (Q : ℝ) := Icc (0 : ℝ) Q

/-- Push forward a probability law on the compact interval into the ordinary
real-valued measure used by the manuscript's functional. -/
noncomputable def law {Q : ℝ} (ν : ProbabilityMeasure (CutoffSpace Q)) : Measure ℝ :=
  (ν : Measure (CutoffSpace Q)).map (fun r => r.val)

instance law_isProbability {Q : ℝ} (ν : ProbabilityMeasure (CutoffSpace Q)) :
    IsProbabilityMeasure (law ν) := by
  unfold law
  infer_instance

/-- Every pushed-forward compact probability law has the prescribed cutoff. -/
theorem law_hasCutoff {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (ν : ProbabilityMeasure (CutoffSpace Q)) : HasCutoff (law ν) Q := by
  refine ⟨hQ0, hQ1, ?_⟩
  unfold law
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (p := fun r => r ∈ Icc (0 : ℝ) Q) measurableSet_Icc).mpr
  exact Eventually.of_forall (fun r => r.property)

/-- The real integral of every test function is the actual subtype integral;
closed-embedding transport avoids any irrelevant regularity outside the cutoff. -/
theorem integral_law {Q : ℝ} (ν : ProbabilityMeasure (CutoffSpace Q)) (f : ℝ → ℝ) :
    (∫ r, f r ∂law ν) = ∫ r : CutoffSpace Q, f r.val ∂ν := by
  unfold law
  exact isClosed_Icc.isClosedEmbedding_subtypeVal.integral_map f

/-- Weak continuity of the actual energy integral for a continuous covariance
on the physical overlap interval. -/
theorem continuous_energy_integral {Q : ℝ} (hQ1 : Q < 1)
    (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1)) :
    Continuous (fun ν : ProbabilityMeasure (CutoffSpace Q) => ∫ r, η r ∂law ν) := by
  have hcont : Continuous (fun r : CutoffSpace Q => η r.val) :=
    (hη.mono (fun r hr => ⟨hr.1, hr.2.trans_lt hQ1⟩)).domRestrict
  let test : C(CutoffSpace Q, ℝ) := ⟨fun r => η r.val, hcont⟩
  convert ProbabilityMeasure.continuous_integral_continuousMap test using 1
  ext ν
  exact integral_law ν η

/-- For every fixed overlap, the actual hatted function is weakly continuous
as a function of the compact probability law. -/
theorem continuous_xHat {Q : ℝ} (t : ℝ) :
    Continuous (fun ν : ProbabilityMeasure (CutoffSpace Q) => xHat (law ν) t) := by
  let test : C(CutoffSpace Q, ℝ) :=
    ⟨fun r => 1 - max t r.val, by fun_prop⟩
  convert ProbabilityMeasure.continuous_integral_continuousMap test using 1
  ext ν
  exact integral_law ν (fun r => 1 - max t r)

/-- Uniform positivity gives weak continuity of the actual reciprocal entropy
integral by dominated convergence on the fixed interval. -/
theorem continuous_entropy_integral {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) :
    Continuous (fun ν : ProbabilityMeasure (CutoffSpace Q) =>
      ∫ t in (0 : ℝ)..Q, (xHat (law ν) t)⁻¹) := by
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ => (1 - Q)⁻¹)
  · intro ν
    exact ((xHat_continuous (law ν) (law_hasCutoff hQ0 hQ1 ν)).measurable.inv).aestronglyMeasurable
  · intro ν
    filter_upwards [] with t ht
    rw [uIoc_of_le hQ0] at ht
    have hcut := law_hasCutoff hQ0 hQ1 ν
    have hxpos := xHat_pos (law ν) hcut (ht.2.trans_lt hQ1)
    have hbound := xHat_ge_one_sub_cutoff (law ν) hcut ht.2
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hxpos.le)]
    exact inv_anti₀ (sub_pos.mpr hQ1) hbound
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht
    rw [uIoc_of_le hQ0] at ht
    apply (continuous_xHat t).inv₀
    intro ν
    exact (xHat_pos (law ν) (law_hasCutoff hQ0 hQ1 ν) (ht.2.trans_lt hQ1)).ne'

/-- The actual ordinary functional is continuous on the compact space of
probability measures at a fixed cutoff. -/
theorem continuous_functional {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1)) :
    Continuous (fun ν : ProbabilityMeasure (CutoffSpace Q) => functional β η (law ν) Q) := by
  unfold functional
  exact (((continuous_const.sub (continuous_energy_integral hQ1 η hη)).const_mul (β ^ 2)).add
    (continuous_entropy_integral hQ0 hQ1)).add_const (Real.log (1 - Q)) |>.div_const 2

/-- Lift an actual real probability law supported in the cutoff interval back
to a probability measure on that compact subtype. -/
noncomputable def liftLaw {Q : ℝ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hq : HasCutoff ν Q) : ProbabilityMeasure (CutoffSpace Q) :=
  ⟨ν.comap (fun r : CutoffSpace Q => r.val),
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
      (hq.2.2.mono (fun r hr => ⟨⟨r, hr⟩, rfl⟩))⟩

/-- The lifting represents precisely the original ordinary real law. -/
theorem law_liftLaw {Q : ℝ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hq : HasCutoff ν Q) : law (liftLaw ν hq) = ν := by
  change Measure.map (Subtype.val : CutoffSpace Q → ℝ)
    (ν.comap (Subtype.val : CutoffSpace Q → ℝ)) = ν
  rw [map_comap_subtype_coe measurableSet_Icc,
    Measure.restrict_eq_self_of_ae_mem hq.2.2]

/-- Actual attainment at a prescribed cutoff, over all ordinary admissible
laws with that cutoff, derived from compactness and continuity. -/
theorem exists_minimizer_fixedCutoff {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1)) :
    ∃ ζ : Admissible, HasCutoff ζ.law Q ∧
      ∀ ν : Admissible, HasCutoff ν.law Q → ζ.value β η ≤ ν.value β η := by
  let zero : CutoffSpace Q := ⟨0, ⟨le_rfl, hQ0⟩⟩
  let candidate : ProbabilityMeasure (CutoffSpace Q) :=
    ⟨Measure.dirac zero, inferInstance⟩
  have hnonempty : (univ : Set (ProbabilityMeasure (CutoffSpace Q))).Nonempty :=
    ⟨candidate, mem_univ _⟩
  obtain ⟨ν₀, _, hmin⟩ := isCompact_univ.exists_isMinOn hnonempty
    (continuous_functional hQ0 hQ1 β η hη).continuousOn
  let ζ : Admissible := ⟨law ν₀, inferInstance, ⟨Q, law_hasCutoff hQ0 hQ1 ν₀⟩⟩
  refine ⟨ζ, law_hasCutoff hQ0 hQ1 ν₀, ?_⟩
  intro ν hν
  have h := hmin (mem_univ (liftLaw ν.law hν))
  change functional β η (law ν₀) Q ≤ functional β η (law (liftLaw ν.law hν)) Q at h
  rw [law_liftLaw ν.law hν] at h
  rw [ζ.value_eq β η (law_hasCutoff hQ0 hQ1 ν₀), ν.value_eq β η hν]
  exact h

/-- Uniform support truncation promotes compact fixed-cutoff attainment to
actual minimizer existence in the full admissible class. No minimizer-existence
premise is used. -/
theorem exists_minimizer_of_lipschitz (β : ℝ) (η : ℝ → ℝ) (L : ℝ≥0)
    (hη : LipschitzOnWith L η (Icc (0 : ℝ) 1)) :
    ∃ ζ : Admissible, ζ.IsMinimizer β η := by
  obtain ⟨Q, hQ, hcoef⟩ := exists_uniform_cutoff β L
  have hcont : ContinuousOn η (Ico 0 1) :=
    hη.continuousOn.mono (fun r hr => ⟨hr.1, hr.2.le⟩)
  obtain ⟨ζ, hζQ, hminimum⟩ := exists_minimizer_fixedCutoff hQ.1.le hQ.2 β η hcont
  refine ⟨ζ, ?_⟩
  intro ν
  let νT : Admissible :=
    ⟨truncate ν.law Q, inferInstance,
      ⟨Q, truncate_hasCutoff ν.law ν.hasCutoff hQ.1.le hQ.2⟩⟩
  have hcut : HasCutoff νT.law Q :=
    truncate_hasCutoff ν.law ν.hasCutoff hQ.1.le hQ.2
  have hminT := hminimum νT hcut
  have htruncate := functional_truncate_le β η ν.law ν.hasCutoff hQ.1.le hQ.2 L hη hcoef
  rw [νT.value_eq β η hcut] at hminT
  rw [ν.value_eq β η ν.hasCutoff]
  exact hminT.trans htruncate

/-- A finite deterministic derivative bound for the canonical polynomial. -/
noncomputable def mixtureLipschitzConstant (μ : FiniteMixture) : ℝ≥0 :=
  ⟨∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ),
    Finset.sum_nonneg (fun p _ => mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))⟩

/-- The actual finite covariance polynomial is Lipschitz on `[0,1]`, with
its coefficient-derived constant. -/
theorem mixture_xi_lipschitzOn (μ : FiniteMixture) :
    LipschitzOnWith (mixtureLipschitzConstant μ) μ.xi (Icc (0 : ℝ) 1) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun r _ => (μ.hasDerivAt_xi r).differentiableAt) ?_ (convex_Icc 0 1)
  intro r hr
  apply NNReal.coe_le_coe.mp
  change ‖deriv μ.xi r‖ ≤ ∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ)
  rw [(μ.hasDerivAt_xi r).deriv, Real.norm_eq_abs]
  have hnonneg : 0 ≤ μ.xi1 r := by
    unfold FiniteMixture.xi1
    exact Finset.sum_nonneg (fun p _ => mul_nonneg
      (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p)) (pow_nonneg hr.1 _))
  rw [abs_of_nonneg hnonneg]
  unfold FiniteMixture.xi1
  apply Finset.sum_le_sum
  intro p hp
  have hpow : r ^ (p - 1) ≤ 1 := pow_le_one₀ hr.1 hr.2
  calc
    _ ≤ (μ.coeff p * (p : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
    _ = _ := mul_one _

/-- Actual Crisanti--Sommers minimizer existence for every canonical finite
mixture and every real inverse-temperature parameter. -/
theorem exists_minimizer_finiteMixture (μ : FiniteMixture) (β : ℝ) :
    ∃ ζ : Admissible, ζ.IsMinimizer β μ.xi :=
  exists_minimizer_of_lipschitz β μ.xi (mixtureLipschitzConstant μ)
    (mixture_xi_lipschitzOn μ)

end SlowEquilibration.CSCompactAttainment
