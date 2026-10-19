module

public import SphericalAging.PredictableItoTime
public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! The deterministic Volterra operator in the same predictable product L²
space used for the Itô operator. No adaptedness or integrability of a putative
solution is supplied as an existence hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PredictableDriftTime
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- A globally strongly predictable representative of the actual L² class. -/
@[expose] def representative (U : PredictableProcessL2 F P) : ℝ≥0 × Ω → ℝ :=
  (lpMeas.aestronglyMeasurable U).mk (U : TimeProcessL2 P)

theorem representative_stronglyMeasurable (U : PredictableProcessL2 F P) :
    StronglyMeasurable[F.predictable] (representative U) :=
  (lpMeas.aestronglyMeasurable U).stronglyMeasurable_mk

theorem representative_ae (U : PredictableProcessL2 F P) :
    representative U =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : TimeProcessL2 P) :=
  ((lpMeas.aestronglyMeasurable U).ae_eq_mk).symm

@[expose] def primitive (H : ℝ≥0 × Ω → ℝ) (t : ℝ≥0) (omega : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) t, H (s, omega) ∂nonnegativeLebesgueMeasure

/-- Deterministic integration up to time `t` preserves the full filtration. -/
theorem primitive_stronglyAdapted (H : ℝ≥0 × Ω → ℝ)
    (hH : StronglyMeasurable[F.predictable] H) : StronglyAdapted F (primitive H) := by
  have hprog : IsStronglyProgressive F (fun t omega => H (t, omega)) :=
    (show IsStronglyPredictable F (fun t omega => H (t, omega)) from hH).isStronglyProgressive
  intro t
  letI : MeasurableSpace Ω := F t
  have hpair : Measurable (fun p : ℝ≥0 × Ω =>
      ((⟨min p.1 t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic t), p.2)) :=
    ((measurable_fst.min measurable_const).subtype_mk).prodMk measurable_snd
  have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω => H (min p.1 t, p.2)) :=
    (hprog t).comp_measurable hpair
  have hcut := hm.indicator ((measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ≥0) t)).preimage measurable_fst)
  have hi := hcut.integral_prod_left' (μ := nonnegativeLebesgueMeasure)
  convert hi using 1
  funext omega
  rw [primitive, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun s => by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) t
    · simp [hs, min_eq_left hs.2]
    · simp [hs])

omit [IsProbabilityMeasure P] in
theorem integral_sq_le_measure_mul_integral_sq {A : Type*} [MeasurableSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (f : A → ℝ) (hf : MemLp f 2 mu) :
    (∫ x, f x ∂mu)^2 ≤ mu.real univ * ∫ x, f x^2 ∂mu := by
  have h1 : MemLp (fun _ : A => (1 : ℝ)) 2 mu := memLp_const 1
  have hi : inner ℝ (h1.toLp (fun _ : A => (1 : ℝ))) (hf.toLp f) = ∫ x, f x ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, hf.coeFn_toLp] with x hx1 hxf
    simp only [RCLike.inner_apply, conj_trivial, hx1, hxf, one_mul, mul_one]
  have hn1 : ‖h1.toLp (fun _ : A => (1 : ℝ))‖^2 = mu.real univ := by
    rw [← SphericalAging.PredictableItoTime.integral_sq_toLp]
    simp
  have hnf := SphericalAging.PredictableItoTime.integral_sq_toLp f hf
  have hc := norm_inner_le_norm (𝕜 := ℝ) (h1.toLp (fun _ : A => (1 : ℝ))) (hf.toLp f)
  rw [hi] at hc
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hc
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, hn1, ← hnf] using hs

/-- Any integrable path has a continuous deterministic primitive. The
endpoint null-set is handled for the actual nonnegative Lebesgue measure. -/
theorem primitive_continuous (H : ℝ≥0 × Ω → ℝ) (omega : Ω)
    (hH : Integrable (fun s => H (s, omega)) nonnegativeLebesgueMeasure) :
    Continuous (fun t => primitive H t omega) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  have hlim : ∀ᵐ s ∂nonnegativeLebesgueMeasure,
      Tendsto (fun n => (Ioc (0 : ℝ≥0) (u n)).indicator (fun s => H (s, omega)) s)
        atTop (𝓝 ((Ioc (0 : ℝ≥0) t).indicator (fun s => H (s, omega)) s)) := by
    have hae : ∀ᵐ s ∂nonnegativeLebesgueMeasure, s ≠ t := by
      rw [ae_iff]
      simpa using FourPapersCommon.FilteredBrownian.nonnegativeLebesgueMeasure_singleton t
    filter_upwards [hae] with s hs
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hs0' : 0 < s := lt_of_le_of_ne (zero_le : 0 ≤ s) (Ne.symm hs0)
      rcases lt_or_gt_of_ne hs with hst | hts
      · apply tendsto_const_nhds.congr'
        filter_upwards [hu.eventually (eventually_gt_nhds hst)] with n hn
        simp [hs0', hst.le, hn.le]
      · apply tendsto_const_nhds.congr'
        filter_upwards [hu.eventually (eventually_lt_nhds hts)] with n hn
        simp [not_le_of_gt hts, not_le_of_gt hn]
  simpa only [primitive, Function.comp_def, integral_indicator measurableSet_Ioc] using
    tendsto_integral_of_dominated_convergence (fun s => ‖H (s, omega)‖)
      (fun n => hH.aestronglyMeasurable.indicator measurableSet_Ioc) hH.norm
      (fun n => .of_forall (fun s => norm_indicator_le_norm_self _ s)) hlim



@[expose] def cutRepresentative (U : PredictableProcessL2 F P) (T : ℝ≥0) : ℝ≥0 × Ω → ℝ :=
  (FourPapersCommon.FilteredBrownian.predictableTimeFrame T).indicator (representative U)

theorem cutRepresentative_stronglyMeasurable (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    StronglyMeasurable[F.predictable] (cutRepresentative U T) :=
  (representative_stronglyMeasurable U).indicator (FourPapersCommon.FilteredBrownian.measurableSet_predictableTimeFrame F T)

theorem cutRepresentative_memLp (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    MemLp (cutRepresentative U T) 2 (nonnegativeLebesgueMeasure.prod P) :=
  ((Lp.memLp (U : TimeProcessL2 P)).ae_eq (representative_ae U).symm).indicator
    (predictable_le_prod F _ (FourPapersCommon.FilteredBrownian.measurableSet_predictableTimeFrame F T))

theorem cutRepresentative_integrable (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    Integrable (cutRepresentative U T) (nonnegativeLebesgueMeasure.prod P) := by
  have h1 : MemLp ((FourPapersCommon.FilteredBrownian.predictableTimeFrame T).indicator (fun _ : ℝ≥0 × Ω => (1 : ℝ))) 2
      (nonnegativeLebesgueMeasure.prod P) :=
    memLp_indicator_const 2 (measurableSet_Ioc.prod MeasurableSet.univ) (1 : ℝ)
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))
  have hm : MemLp ((cutRepresentative U T) *
      (FourPapersCommon.FilteredBrownian.predictableTimeFrame T).indicator (fun _ : ℝ≥0 × Ω => (1 : ℝ))) 1
        (nonnegativeLebesgueMeasure.prod P) := (cutRepresentative_memLp U T).mul h1
  apply memLp_one_iff_integrable.mp
  convert hm using 1
  funext p
  by_cases hp : p ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame T
  · simp [cutRepresentative, hp]
  · simp [cutRepresentative, hp]

@[expose] def driftVersion (U : PredictableProcessL2 F P) (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  primitive (cutRepresentative U T)

theorem driftVersion_stronglyAdapted (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    StronglyAdapted F (driftVersion U T) :=
  primitive_stronglyAdapted _ (cutRepresentative_stronglyMeasurable U T)

theorem driftVersion_ae_continuous (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    ∀ᵐ omega ∂P, Continuous (fun t => driftVersion U T t omega) := by
  filter_upwards [(cutRepresentative_integrable U T).prod_left_ae] with omega homega
  exact primitive_continuous _ omega homega

open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)

theorem primitive_sq_le (H : ℝ≥0 × Ω → ℝ) (T t : ℝ≥0) (omega : Ω)
    (hH : MemLp (fun s => H (s, omega)) 2 nonnegativeLebesgueMeasure)
    (hsupport : ∀ s, s ∉ Ioc (0 : ℝ≥0) T → H (s, omega) = 0) :
    (primitive H t omega)^2 ≤ (T : ℝ) *
      ∫ s, H (s, omega)^2 ∂nonnegativeLebesgueMeasure := by
  let g : ℝ≥0 → ℝ := (Ioc (0 : ℝ≥0) t).indicator (fun s => H (s, omega))
  have hg : MemLp g 2 (finiteTimeMeasure T) := (hH.indicator measurableSet_Ioc).restrict _
  have hi : ∫ s, g s ∂finiteTimeMeasure T = primitive H t omega := by
    rw [finiteTimeMeasure, ← integral_indicator measurableSet_Ioc, primitive,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) T
      · simp [hs, g]
      · by_cases hst : s ∈ Ioc (0 : ℝ≥0) t <;> simp [hs, g, hst, hsupport s hs])
  have hmeasure : (finiteTimeMeasure T).real univ = T := by
    simp [finiteTimeMeasure, Measure.real_def, nonnegativeLebesgueMeasure_Ioc,
      ENNReal.toReal_ofReal T.coe_nonneg]
  have hbound : ∫ s, g s^2 ∂finiteTimeMeasure T ≤
      ∫ s, H (s, omega)^2 ∂nonnegativeLebesgueMeasure := by
    calc
      _ ≤ ∫ s, H (s, omega)^2 ∂finiteTimeMeasure T := by
        apply integral_mono_ae hg.integrable_sq (hH.restrict _).integrable_sq
        exact .of_forall (fun s => by
          by_cases hs : s ∈ Ioc (0 : ℝ≥0) t
          · simp [g, hs]
          · simp [g, hs, sq_nonneg])
      _ ≤ _ := integral_mono_measure (Measure.restrict_le_self)
        (.of_forall (fun s => sq_nonneg _)) hH.integrable_sq
  calc
    _ ≤ (finiteTimeMeasure T).real univ * ∫ s, g s^2 ∂finiteTimeMeasure T := by
      simpa only [hi] using integral_sq_le_measure_mul_integral_sq (finiteTimeMeasure T) g hg
    _ ≤ _ := by rw [hmeasure]; exact mul_le_mul_of_nonneg_left hbound T.coe_nonneg

theorem driftVersion_sq_le_ae (U : PredictableProcessL2 F P) (T t : ℝ≥0) :
    ∀ᵐ omega ∂P, (driftVersion U T t omega)^2 ≤ (T : ℝ) *
      ∫ s, (cutRepresentative U T (s, omega))^2 ∂nonnegativeLebesgueMeasure := by
  have hm := (cutRepresentative_stronglyMeasurable U T).mono (predictable_le_prod F)
  filter_upwards [(cutRepresentative_memLp U T).integrable_sq.prod_left_ae] with omega homega
  have hpath : MemLp (fun s => cutRepresentative U T (s, omega)) 2 nonnegativeLebesgueMeasure :=
    (memLp_two_iff_integrable_sq (hm.comp_measurable measurable_prodMk_right).aestronglyMeasurable).2 homega
  exact primitive_sq_le _ T t omega hpath (fun s hs => by
    simp [cutRepresentative, FourPapersCommon.FilteredBrownian.predictableTimeFrame, hs])

theorem driftVersion_memLp (U : PredictableProcessL2 F P) (T t : ℝ≥0) :
    MemLp (driftVersion U T t) 2 P := by
  have hm : AEStronglyMeasurable (driftVersion U T t) P :=
    ((driftVersion_stronglyAdapted U T t).mono (F.le t)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have he := (cutRepresentative_memLp U T).integrable_sq.integral_prod_right
  apply (he.const_mul (T : ℝ)).mono' (hm.pow 2)
  filter_upwards [driftVersion_sq_le_ae U T t] with omega homega
  simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using homega

theorem integral_sq_cutRepresentative_le (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    ∫ p, (cutRepresentative U T p)^2 ∂nonnegativeLebesgueMeasure.prod P ≤ ‖U‖^2 := by
  have hi : ∫ p, (U : TimeProcessL2 P) p ^ 2 ∂nonnegativeLebesgueMeasure.prod P = ‖U‖^2 := by
    change _ = ‖(U : TimeProcessL2 P)‖^2
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact .of_forall (fun p => by simp only [RCLike.inner_apply, conj_trivial, pow_two])
  rw [← hi]
  apply integral_mono_ae (cutRepresentative_memLp U T).integrable_sq (Lp.memLp (U : TimeProcessL2 P)).integrable_sq
  filter_upwards [representative_ae U] with p hp
  by_cases hpt : p ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame T
  · simp [cutRepresentative, hpt, hp]
  · simp [cutRepresentative, hpt, sq_nonneg]

theorem norm_driftVersion_toLp_le (U : PredictableProcessL2 F P) (T t : ℝ≥0) :
    ‖(driftVersion_memLp U T t).toLp (driftVersion U T t)‖ ≤ Real.sqrt T * ‖U‖ := by
  have hsq : ‖(driftVersion_memLp U T t).toLp (driftVersion U T t)‖^2 ≤
      (T : ℝ) * ‖U‖^2 := by
    rw [← SphericalAging.PredictableItoTime.integral_sq_toLp]
    calc
      _ ≤ ∫ omega, (T : ℝ) * ∫ s, (cutRepresentative U T (s, omega))^2
          ∂nonnegativeLebesgueMeasure ∂P :=
        integral_mono_ae (driftVersion_memLp U T t).integrable_sq
          ((cutRepresentative_memLp U T).integrable_sq.integral_prod_right.const_mul _)
          (driftVersion_sq_le_ae U T t)
      _ = (T : ℝ) * ∫ p, (cutRepresentative U T p)^2 ∂nonnegativeLebesgueMeasure.prod P := by
        rw [integral_const_mul]
        congr 1
        exact (integral_prod_symm _ (cutRepresentative_memLp U T).integrable_sq).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_sq_cutRepresentative_le U T) T.coe_nonneg
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  simpa only [mul_pow, Real.sq_sqrt T.coe_nonneg] using hsq


theorem driftVersion_timeCut_memLp (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (driftVersion U T) T) 2
      (nonnegativeLebesgueMeasure.prod P) :=
  SphericalAging.PredictableItoTime.memLp_timeCut_of_uniform_L2Bound (driftVersion U T)
    (driftVersion_stronglyAdapted U T) (driftVersion_ae_continuous U T)
    (driftVersion_memLp U T) (NNReal.sqrt T * ‖U‖₊)
    (fun t => by simpa only [NNReal.coe_mul, Real.coe_sqrt, coe_nnnorm] using
      norm_driftVersion_toLp_le U T t) T

@[expose] def driftVolterra (T : ℝ≥0) (U : PredictableProcessL2 F P) : PredictableProcessL2 F P :=
  ⟨(driftVersion_timeCut_memLp U T).toLp _,
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F (driftVersion U T)
      (driftVersion_stronglyAdapted U T) (driftVersion_ae_continuous U T) T).congr
        (driftVersion_timeCut_memLp U T).coeFn_toLp.symm⟩

theorem norm_driftVolterra_le (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖driftVolterra T U‖ ≤ (T : ℝ) * ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg T.coe_nonneg (norm_nonneg _))).1
  change ‖(driftVersion_timeCut_memLp U T).toLp _‖^2 ≤ _
  rw [← SphericalAging.PredictableItoTime.integral_sq_toLp,
    integral_prod _ (driftVersion_timeCut_memLp U T).integrable_sq]
  have hc : Integrable ((Ioc (0 : ℝ≥0) T).indicator (fun _ => (T : ℝ) * ‖U‖^2))
      nonnegativeLebesgueMeasure :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_Ioc
      ((T : ℝ) * ‖U‖^2) (Or.inr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)))
  calc
    _ ≤ ∫ t, (Ioc (0 : ℝ≥0) T).indicator (fun _ => (T : ℝ) * ‖U‖^2) t
        ∂nonnegativeLebesgueMeasure := by
      apply integral_mono_ae (driftVersion_timeCut_memLp U T).integrable_sq.integral_prod_left hc
      exact .of_forall (fun t => by
        by_cases ht : t ∈ Ioc (0 : ℝ≥0) T
        · simp only [FourPapersCommon.continuousAdaptedTimeCut, ht, if_pos, indicator_of_mem]
          rw [SphericalAging.PredictableItoTime.integral_sq_toLp]
          have h := (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
              (norm_driftVersion_toLp_le U T t)
          simpa only [mul_pow, Real.sq_sqrt T.coe_nonneg] using h
        · simp [FourPapersCommon.continuousAdaptedTimeCut, ht])
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, setIntegral_const]
      simp [Measure.real_def, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul]
      ring

theorem cutRepresentative_sub_ae (U V : PredictableProcessL2 F P) (T : ℝ≥0) :
    cutRepresentative (U - V) T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun p => cutRepresentative U T p - cutRepresentative V T p) := by
  filter_upwards [representative_ae (U - V), representative_ae U, representative_ae V,
    Lp.coeFn_sub (U : TimeProcessL2 P) (V : TimeProcessL2 P)] with p hsub hU hV hUV
  change representative (U - V) p = ((U : TimeProcessL2 P) - (V : TimeProcessL2 P)) p at hsub
  by_cases hp : p ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame T
  · simpa only [cutRepresentative, indicator_of_mem hp, hsub, hU, hV, Pi.sub_apply] using hUV
  · simp [cutRepresentative, hp]

theorem driftVersion_sub_ae (U V : PredictableProcessL2 F P) (T : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ t, driftVersion (U - V) T t omega =
      driftVersion U T t omega - driftVersion V T t omega := by
  have hswap : ∀ᵐ p ∂P.prod nonnegativeLebesgueMeasure,
      cutRepresentative (U - V) T (p.2, p.1) =
        cutRepresentative U T (p.2, p.1) - cutRepresentative V T (p.2, p.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae (cutRepresentative_sub_ae U V T)
  filter_upwards [Measure.ae_ae_of_ae_prod hswap, (cutRepresentative_integrable U T).prod_left_ae,
    (cutRepresentative_integrable V T).prod_left_ae] with omega homega hU hV
  intro t
  dsimp [driftVersion, primitive]
  rw [← integral_sub hU.integrableOn hV.integrableOn]
  exact integral_congr_ae (ae_restrict_of_ae homega)

theorem driftVolterra_sub (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    driftVolterra T (U - V) = driftVolterra T U - driftVolterra T V := by
  apply Subtype.ext
  apply Lp.ext
  have hpaths := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae (driftVersion_sub_ae U V T)
  filter_upwards [(driftVersion_timeCut_memLp (U - V) T).coeFn_toLp,
    (driftVersion_timeCut_memLp U T).coeFn_toLp, (driftVersion_timeCut_memLp V T).coeFn_toLp,
    Lp.coeFn_sub ((driftVolterra T U : PredictableProcessL2 F P) : TimeProcessL2 P)
      ((driftVolterra T V : PredictableProcessL2 F P) : TimeProcessL2 P), hpaths]
    with p hsub hU hV hdiff hp
  change ((driftVersion_timeCut_memLp (U - V) T).toLp _ : ℝ≥0 × Ω → ℝ) p =
    ((driftVolterra T U : TimeProcessL2 P) - (driftVolterra T V : TimeProcessL2 P)) p
  rw [hsub, hdiff, Pi.sub_apply]
  change FourPapersCommon.continuousAdaptedTimeCut (driftVersion (U - V) T) T p =
    ((driftVersion_timeCut_memLp U T).toLp _ : ℝ≥0 × Ω → ℝ) p -
      ((driftVersion_timeCut_memLp V T).toLp _ : ℝ≥0 × Ω → ℝ) p
  rw [hU, hV]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp [FourPapersCommon.continuousAdaptedTimeCut, ht, hp p.1]
  · simp [FourPapersCommon.continuousAdaptedTimeCut, ht]

theorem norm_driftVolterra_sub_le (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    ‖driftVolterra T U - driftVolterra T V‖ ≤ (T : ℝ) * ‖U - V‖ := by
  rw [← driftVolterra_sub]
  exact norm_driftVolterra_le T (U - V)

open SphericalAging.HardSphereDynamics SphericalAging.PredictableItoTime
variable {N : ℕ}

@[expose] def driftCoefficientMap {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    PredictableProcessL2 F P := driftVolterra T (predictableCoefficient hg U T)

theorem norm_driftCoefficientMap_sub_le {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    ‖driftCoefficientMap hg T U - driftCoefficientMap hg T V‖ ≤ (T : ℝ) * K * ‖U - V‖ := by
  calc
    _ ≤ (T : ℝ) * ‖predictableCoefficient hg U T - predictableCoefficient hg V T‖ :=
      norm_driftVolterra_sub_le T _ _
    _ ≤ (T : ℝ) * ((K : ℝ) * ‖U - V‖) :=
      mul_le_mul_of_nonneg_left (norm_predictableCoefficient_sub_le hg U V T) T.coe_nonneg
    _ = _ := by ring

@[expose] def finiteDriftPicardMap {K : ℝ≥0} {g : Fin N → State N → ℝ}
    (hg : ∀ i, LipschitzWith K (g i)) (T : ℝ≥0)
    (U : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  ∑ i : Fin N, scalarToStatePredictable i (driftCoefficientMap (hg i) T U)

theorem norm_finiteDriftPicardMap_sub_le {K : ℝ≥0} {g : Fin N → State N → ℝ}
    (hg : ∀ i, LipschitzWith K (g i)) (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    ‖finiteDriftPicardMap hg T U - finiteDriftPicardMap hg T V‖ ≤
      (N : ℝ) * T * K * ‖U - V‖ := by
  unfold finiteDriftPicardMap
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, ‖scalarToStatePredictable i (driftCoefficientMap (hg i) T U) -
        scalarToStatePredictable i (driftCoefficientMap (hg i) T V)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (T : ℝ) * K * ‖U - V‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarToStatePredictable_sub]
      exact (norm_scalarToStatePredictable_le i _).trans (norm_driftCoefficientMap_sub_le (hg i) T U V)
    _ = _ := by simp; ring

/-- The local matrix-driven SDE Picard equation is solved by the Banach
fixed point theorem in the actual closed predictable product L² space.
The coefficients are genuine functions, composed with the iterate and
integrated using the actual deterministic and stochastic operators. -/
theorem exists_unique_local_picard_fixedPoint
    (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) (A : PredictableStateL2 N F P)
    (hsmall : (N : ℝ≥0) * T * Kb + (N : ℝ≥0)^2 * NNReal.sqrt T * Ks < 1) :
    ∃! U : PredictableStateL2 N F P,
      U = A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U := by
  letI : Fact (F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω))) :=
    ⟨predictable_le_prod F⟩
  let f := fun U : PredictableStateL2 N F P =>
    A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U
  have hl : LipschitzWith ((N : ℝ≥0) * T * Kb + (N : ℝ≥0)^2 * NNReal.sqrt T * Ks) f := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simp only [f, dist_eq_norm]
    have he : A + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U -
        (A + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V) =
      (finiteDriftPicardMap hb T U - finiteDriftPicardMap hb T V) +
        (finiteNoisePicardMap D hsigma T U - finiteNoisePicardMap D hsigma T V) := by abel
    rw [he]
    calc
      _ ≤ ‖finiteDriftPicardMap hb T U - finiteDriftPicardMap hb T V‖ +
          ‖finiteNoisePicardMap D hsigma T U - finiteNoisePicardMap D hsigma T V‖ := norm_add_le _ _
      _ ≤ (N : ℝ) * T * Kb * ‖U - V‖ + (N : ℝ)^2 * Real.sqrt T * Ks * ‖U - V‖ :=
        add_le_add (norm_finiteDriftPicardMap_sub_le hb T U V)
          (norm_finiteNoisePicardMap_sub_le D hsigma T U V)
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
          NNReal.coe_natCast, Real.coe_sqrt]; ring
  have hc : ContractingWith ((N : ℝ≥0) * T * Kb + (N : ℝ≥0)^2 * NNReal.sqrt T * Ks) f :=
    ⟨hsmall, hl⟩
  refine ⟨hc.fixedPoint, hc.fixedPoint_isFixedPt.symm, ?_⟩
  intro U hU
  exact hc.fixedPoint_unique hU.symm

/-- The deterministic operator uses exactly the manuscript's real-time
Lebesgue integral after the canonical nonnegative-time identification. -/
theorem primitive_eq_real_intervalIntegral (H : ℝ≥0 × Ω → ℝ) (t : ℝ≥0) (omega : Ω) :
    primitive H t omega = ∫ s in (0 : ℝ)..(t : ℝ), H (s.toNNReal, omega) := by
  have himage : ((↑) : ℝ≥0 → ℝ) '' Ioc (0 : ℝ≥0) t = Ioc (0 : ℝ) (t : ℝ) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩
    · intro hx
      exact ⟨⟨x, hx.1.le⟩, ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩, rfl⟩
  have hmap : Measure.map ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) t)) =
        volume.restrict (Ioc (0 : ℝ) (t : ℝ)) := by
    rw [nonnegativeLebesgueMeasure,
      measurableEmbedding_nnrealCoe_iterated.restrict_comap,
      measurableEmbedding_nnrealCoe_iterated.map_comap,
      Measure.restrict_restrict measurableEmbedding_nnrealCoe_iterated.measurableSet_range,
      inter_eq_right.mpr (image_subset_range _ _), himage]
  rw [intervalIntegral.integral_of_le t.coe_nonneg, ← hmap,
    measurableEmbedding_nnrealCoe_iterated.integral_map]
  simp only [Real.toNNReal_coe, primitive]

end SphericalAging.PredictableDriftTime
