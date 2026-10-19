module

public import SphericalAging.PredictableDriftTime
public import SphericalAging.VectorIto
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-! Pathwise zero uniqueness for the actual bounded linear radial stochastic
equation. The stochastic term is the constructed full-filtration vector Itô
operator. Its energy estimate and the deterministic integral Grönwall step
are proved, rather than supplied as assumptions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RadialUniqueness
open HardSphereDynamics PredictableDriftTime
open FourPapersCommon.FilteredBrownian
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def meanSquare (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ := ∫ omega, Z t omega ^ 2 ∂P

omit [IsProbabilityMeasure P] in
theorem meanSquare_nonneg (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : 0 ≤ meanSquare (P := P) Z t :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem bounded_memLp (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z) (L : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (t : ℝ≥0) : MemLp (Z t) 2 P :=
  MemLp.of_bound ((hZa t).mono (F.le t)).aestronglyMeasurable L
    (hbound.mono (fun _ h => h t))

theorem meanSquare_continuous (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) : Continuous (meanSquare (P := P) Z) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (L : ℝ)^2)
  · intro n
    exact (((hZa (u n)).mono (F.le _)).aestronglyMeasurable).pow 2
  · exact integrable_const _
  · intro n
    filter_upwards [hbound] with omega homega
    simpa only [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).2 (homega (u n))
  · filter_upwards [hZc] with omega homega
    exact ((homega.tendsto t).comp hu).pow 2

/-- The genuine deterministic integral Grönwall implication used after the
stochastic energy estimate. -/
 theorem continuous_integral_gronwall_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x) (T C : ℝ)
    (hineq : ∀ x ∈ Icc 0 T, f x ≤ C * ∫ s in (0 : ℝ)..x, f s) :
    ∀ x ∈ Icc 0 T, f x = 0 := by
  let G : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, f s
  have hGc : Continuous G := (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hGd : ∀ x, HasDerivAt G (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hGn : ∀ x ∈ Icc 0 T, 0 ≤ G x := fun x hx =>
    intervalIntegral.integral_nonneg hx.1 (fun s _ => hnonneg s)
  have hGzero : ∀ x ∈ Icc 0 T, G x = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hGc.continuousOn
      (fun x _ => (hGd x).hasDerivWithinAt) (by simp [G])
    intro x hx
    simpa only [Real.norm_of_nonneg (hnonneg x), Real.norm_of_nonneg (hGn x ⟨hx.1, hx.2.le⟩)]
      using hineq x ⟨hx.1, hx.2.le⟩
  intro x hx
  have hi := hineq x hx
  change f x ≤ C * G x at hi
  rw [hGzero x hx, mul_zero] at hi
  exact le_antisymm hi (hnonneg x)

theorem timeCut_memLp (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (t : ℝ≥0) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut Z t) 2
      (nonnegativeLebesgueMeasure.prod P) := by
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (L : ℝ)
    (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle t))
  apply hg.mono' ((FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut
    F Z hZa hZc t).mono (predictable_le_prod F))
  have hae := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hbound
  filter_upwards [hae] with q hq
  by_cases hqt : q.1 ∈ Ioc 0 t
  · simpa [FourPapersCommon.continuousAdaptedTimeCut, hqt,
      FourPapersCommon.FilteredBrownian.predictableTimeFrame, hqt, Real.norm_eq_abs, abs_of_nonneg L.coe_nonneg] using hq q.1
  · simp [FourPapersCommon.continuousAdaptedTimeCut, hqt]

@[expose] def energy (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) t, meanSquare (P := P) Z s ∂nonnegativeLebesgueMeasure

theorem energy_nonneg (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : 0 ≤ energy (P := P) Z t :=
  integral_nonneg (fun s => meanSquare_nonneg Z s)

theorem integral_sq_timeCut (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (t : ℝ≥0) :
    (∫ q, FourPapersCommon.continuousAdaptedTimeCut Z t q ^ 2
      ∂nonnegativeLebesgueMeasure.prod P) = energy (P := P) Z t := by
  rw [integral_prod _ (timeCut_memLp Z hZa hZc L hbound t).integrable_sq]
  rw [energy, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun s => by
    by_cases hs : s ∈ Ioc 0 t
    · simp only [FourPapersCommon.continuousAdaptedTimeCut, hs, if_pos,
        indicator_of_mem, meanSquare]
    · simp [FourPapersCommon.continuousAdaptedTimeCut, hs])

omit [IsProbabilityMeasure P] in
theorem predictable_norm_sq (U : PredictableProcessL2 F P) :
    ‖U‖^2 = ∫ q, (U : TimeProcessL2 P) q ^ 2 ∂nonnegativeLebesgueMeasure.prod P := by
  change ‖(U : TimeProcessL2 P)‖^2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun q => by simp only [RCLike.inner_apply, conj_trivial, pow_two])

theorem restricted_norm_sq_le_energy (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L M : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (T t : ℝ≥0) (ht : t ≤ T)
    (U : PredictableProcessL2 F P)
    (hU : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖) :
    ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U‖^2 ≤ (M : ℝ)^2 * energy (P := P) Z t := by
  rw [predictable_norm_sq, ← integral_sq_timeCut Z hZa hZc L hbound t, ← integral_const_mul]
  apply integral_mono_ae (Lp.memLp (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U : TimeProcessL2 P)).integrable_sq
    ((timeCut_memLp Z hZa hZc L hbound t).integrable_sq.const_mul _)
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t U, hU] with q hq hUq
  by_cases hqt : q.1 ∈ Ioc 0 t
  · have hb := hUq ⟨hqt.1, hqt.2.trans ht⟩
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg M.coe_nonneg (norm_nonneg _))).2 hb
    simpa only [hq, FourPapersCommon.FilteredBrownian.predictableTimeFrame, mem_prod, mem_univ, and_true, hqt,
      indicator_of_mem, FourPapersCommon.continuousAdaptedTimeCut, if_pos,
      Real.norm_eq_abs, sq_abs, mul_pow] using hs
  · simp [hq, FourPapersCommon.FilteredBrownian.predictableTimeFrame, hqt, FourPapersCommon.continuousAdaptedTimeCut]

theorem integral_sq_driftVersion_le (A : PredictableProcessL2 F P) (t : ℝ≥0) :
    (∫ omega, driftVersion A t t omega ^ 2 ∂P) ≤
      (t : ℝ) * ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := by
  have hcut : (∫ q, cutRepresentative A t q ^ 2 ∂nonnegativeLebesgueMeasure.prod P) =
      ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := by
    rw [predictable_norm_sq]
    apply integral_congr_ae
    filter_upwards [representative_ae A, FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t A] with q hq hqt
    by_cases hmem : q ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame t
    · simp [cutRepresentative, hmem, hq, hqt]
    · simp [cutRepresentative, hmem, hqt]
  calc
    _ ≤ ∫ omega, (t : ℝ) * ∫ s, cutRepresentative A t (s, omega)^2
        ∂nonnegativeLebesgueMeasure ∂P :=
      integral_mono_ae (driftVersion_memLp A t t).integrable_sq
        ((cutRepresentative_memLp A t).integrable_sq.integral_prod_right.const_mul _)
        (driftVersion_sq_le_ae A t t)
    _ = (t : ℝ) * ∫ q, cutRepresentative A t q ^ 2 ∂nonnegativeLebesgueMeasure.prod P := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod_symm _ (cutRepresentative_memLp A t).integrable_sq).symm
    _ = _ := by rw [hcut]

/-- The energy inequality is derived from the actual drift primitive and
the actual matrix Brownian integral, with bounded linear coefficients. -/
theorem linear_equation_energy (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L M K : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (T : ℝ≥0)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖)
    (hU : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖)
    (heq : ∀ t, t ≤ T → ∀ᵐ omega ∂P, Z t omega = driftVersion A t t omega +
      (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega) (t : ℝ≥0) (ht : t ≤ T) :
    meanSquare (P := P) Z t ≤
      (2 * (T : ℝ) * (M : ℝ)^2 + 2 * N * (K : ℝ)^2) * energy (P := P) Z t := by
  have hdrift := integral_sq_driftVersion_le A t
  have hAenergy := restricted_norm_sq_le_energy Z hZa hZc L M hbound T t ht A hA
  have hnoise : (∫ omega, (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega ^ 2 ∂P) ≤
      (N : ℝ) * (K : ℝ)^2 * energy (P := P) Z t := by
    rw [PredictableItoTime.integral_sq_toLp _ (Lp.memLp _), Lp.toLp_coeFn,
      VectorIto.vectorProcessLp_norm_sq]
    calc
      _ ≤ ∑ j : Fin N, (K : ℝ)^2 * energy (P := P) Z t :=
        Finset.sum_le_sum (fun j _ =>
          restricted_norm_sq_le_energy Z hZa hZc L K hbound T t ht (U j) (hU j))
      _ = _ := by simp; ring
  have hbasic : meanSquare (P := P) Z t ≤
      2 * (∫ omega, driftVersion A t t omega ^ 2 ∂P) +
      2 * (∫ omega, (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega ^ 2 ∂P) := by
    calc
      _ ≤ ∫ omega, 2 * driftVersion A t t omega ^ 2 +
          2 * (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega ^ 2 ∂P := by
        apply integral_mono_ae (bounded_memLp Z hZa L hbound t).integrable_sq
          (((driftVersion_memLp A t t).integrable_sq.const_mul 2).add
            ((Lp.memLp (VectorIto.vectorProcessLp D U t)).integrable_sq.const_mul 2))
        filter_upwards [heq t ht] with omega homega
        dsimp only [Pi.add_apply]
        rw [homega]
        nlinarith [sq_nonneg (driftVersion A t t omega -
          (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega)]
      _ = _ := by rw [integral_add, integral_const_mul, integral_const_mul]
                  · exact (driftVersion_memLp A t t).integrable_sq.const_mul 2
                  · exact (Lp.memLp (VectorIto.vectorProcessLp D U t)).integrable_sq.const_mul 2
  have hd : (∫ omega, driftVersion A t t omega ^ 2 ∂P) ≤
      (T : ℝ) * (M : ℝ)^2 * energy (P := P) Z t := by
    calc
      _ ≤ (t : ℝ) * ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := hdrift
      _ ≤ (t : ℝ) * ((M : ℝ)^2 * energy (P := P) Z t) :=
        mul_le_mul_of_nonneg_left hAenergy t.coe_nonneg
      _ ≤ (T : ℝ) * ((M : ℝ)^2 * energy (P := P) Z t) :=
        mul_le_mul_of_nonneg_right (show (t : ℝ) ≤ T from ht)
          (mul_nonneg (sq_nonneg _) (energy_nonneg Z t))
      _ = _ := by ring
  nlinarith

omit [IsProbabilityMeasure P] in
theorem energy_eq_real_integral (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    energy (P := P) Z t = ∫ s in (0 : ℝ)..(t : ℝ), meanSquare (P := P) Z s.toNNReal := by
  simpa only [primitive, energy] using primitive_eq_real_intervalIntegral
    (fun q : ℝ≥0 × Unit => meanSquare (P := P) Z q.1) t ()

/-- A zero-initial bounded linear full-filtration SDE is identically zero
up to the deterministic horizon, simultaneously at all times. This is the
analytic uniqueness step for the stopped sphere-radius defect. -/
theorem bounded_linear_equation_zero (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L M K : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (T : ℝ≥0)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖)
    (hU : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖)
    (heq : ∀ t, t ≤ T → ∀ᵐ omega ∂P, Z t omega = driftVersion A t t omega +
      (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → Z t omega = 0 := by
  let f : ℝ → ℝ := fun x => meanSquare (P := P) Z x.toNNReal
  have hfc : Continuous f := (meanSquare_continuous Z hZa hZc L hbound).comp continuous_real_toNNReal
  have hfzero : ∀ x ∈ Icc 0 (T : ℝ), f x = 0 := by
    apply continuous_integral_gronwall_zero f hfc (fun x => meanSquare_nonneg Z _)
      T (2 * (T : ℝ) * (M : ℝ)^2 + 2 * N * (K : ℝ)^2)
    intro x hx
    have hxt : x.toNNReal ≤ T := by simpa only [Real.toNNReal_coe] using (Real.toNNReal_le_toNNReal hx.2)
    have hi := linear_equation_energy D Z hZa hZc L M K hbound T A U hA hU heq x.toNNReal hxt
    rw [energy_eq_real_integral, Real.coe_toNNReal _ hx.1] at hi
    exact hi
  have hfixed : ∀ t, t ≤ T → Z t =ᵐ[P] (fun _ => (0 : ℝ)) := by
    intro t ht
    have hmean : meanSquare (P := P) Z t = 0 := by
      simpa only [f, Real.toNNReal_coe] using hfzero t ⟨t.coe_nonneg, ht⟩
    have hsq : (fun omega => Z t omega ^ 2) =ᵐ[P] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
        (bounded_memLp Z hZa L hbound t).integrable_sq).mp hmean
    filter_upwards [hsq] with omega homega
    exact sq_eq_zero_iff.mp homega
  have hstopcts : ∀ᵐ omega ∂P, Continuous (fun t : ℝ≥0 => Z (min t T) omega) :=
    hZc.mono (fun omega homega => homega.comp (continuous_id.min continuous_const))
  have hstopzero := PredictableItoTime.continuous_processes_ae_eq_of_fixedTime hstopcts
    (P := P) (.of_forall (fun _ => continuous_const))
    (fun t => hfixed (min t T) (min_le_right _ _))
  filter_upwards [hstopzero] with omega homega
  intro t ht
  simpa only [min_eq_left ht] using homega t

end SphericalAging.RadialUniqueness
