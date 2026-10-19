module

public import FourPapersCommon.FilteredItoProcess
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Sequences

public section

/-! Mean-square continuity of the actual full-filtration Ito process.
This extends the terminal isometry to a continuous `L²(P)`-valued process,
without assuming pathwise continuity or identifying the filtration with a
single Brownian coordinate's natural filtration. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace FourPapersCommon.FilteredBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem nonnegativeLebesgueMeasure_singleton (t : ℝ≥0) :
    nonnegativeLebesgueMeasure ({t} : Set ℝ≥0) = 0 := by
  rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.comap_apply]
  simp

theorem ae_time_ne (t : ℝ≥0) :
    ∀ᵐ p : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P, p.1 ≠ t := by
  rw [ae_iff]
  have hset : {p : ℝ≥0 × Ω | ¬p.1 ≠ t} = ({t} : Set ℝ≥0) ×ˢ univ := by
    ext p
    simp
  rw [hset, Measure.prod_prod, nonnegativeLebesgueMeasure_singleton, zero_mul]

@[expose] def timeCutRepresentative (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ℝ≥0 × Ω → ℝ := (predictableTimeFrame (W := Ω) t).indicator U

theorem norm_sq_predictableTimeRestrict_sub (U : PredictableProcessL2 𝓕 P)
    (s t : ℝ≥0) :
    ‖predictableTimeRestrict 𝓕 s U - predictableTimeRestrict 𝓕 t U‖ ^ 2 =
      ∫ p, (timeCutRepresentative U s p - timeCutRepresentative U t p) ^ 2
        ∂nonnegativeLebesgueMeasure.prod P := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ
    ((predictableTimeRestrict 𝓕 s U : TimeProcessL2 P) -
      (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P))
    ((predictableTimeRestrict 𝓕 s U : TimeProcessL2 P) -
      (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub
    (predictableTimeRestrict 𝓕 s U : TimeProcessL2 P)
    (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P),
    predictableTimeRestrict_coeFn 𝓕 s U,
    predictableTimeRestrict_coeFn 𝓕 t U] with p hp hs ht
  simp only [hp, Pi.sub_apply, hs, ht, timeCutRepresentative,
    RCLike.inner_apply, conj_trivial, pow_two]

theorem timeCutRepresentative_sub_sq_le (U : PredictableProcessL2 𝓕 P)
    (s t : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖(timeCutRepresentative U s p - timeCutRepresentative U t p) ^ 2‖ ≤
      ((U : ℝ≥0 × Ω → ℝ) p) ^ 2 := by
  classical
  simp only [timeCutRepresentative, predictableTimeFrame]
  by_cases hs : p ∈ Ioc 0 s ×ˢ (univ : Set Ω)
  <;> by_cases ht : p ∈ Ioc 0 t ×ˢ (univ : Set Ω)
  <;> simp [hs, ht, Real.norm_of_nonneg (sq_nonneg _), sq_nonneg]

theorem timeCutRepresentative_tendsto (U : PredictableProcessL2 𝓕 P)
    {u : ℕ → ℝ≥0} {t : ℝ≥0} (hu : Tendsto u atTop (𝓝 t))
    (p : ℝ≥0 × Ω) (hp : p.1 ≠ t) :
    Tendsto (fun n => timeCutRepresentative U (u n) p) atTop
      (𝓝 (timeCutRepresentative U t p)) := by
  classical
  by_cases hp0 : p.1 = 0
  · have hzero : ∀ s, timeCutRepresentative U s p = 0 := by
      intro s
      simp [timeCutRepresentative, predictableTimeFrame, hp0]
    simp only [hzero]
    exact tendsto_const_nhds
  · have hp0' : 0 < p.1 := lt_of_le_of_ne (zero_le : 0 ≤ p.1) (Ne.symm hp0)
    rcases lt_or_gt_of_ne hp with hpt | htp
    · have hev : ∀ᶠ n in atTop, p.1 < u n :=
        hu.eventually (eventually_gt_nhds hpt)
      have heq : ∀ᶠ n in atTop,
          timeCutRepresentative U (u n) p = timeCutRepresentative U t p := by
        filter_upwards [hev] with n hn
        simp [timeCutRepresentative, predictableTimeFrame, hp0', hpt.le, hn.le]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
    · have hev : ∀ᶠ n in atTop, u n < p.1 :=
        hu.eventually (eventually_lt_nhds htp)
      have heq : ∀ᶠ n in atTop,
          timeCutRepresentative U (u n) p = timeCutRepresentative U t p := by
        filter_upwards [hev] with n hn
        simp [timeCutRepresentative, predictableTimeFrame, not_le_of_gt htp,
          not_le_of_gt hn]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)

theorem continuous_predictableTimeRestrict (U : PredictableProcessL2 𝓕 P) :
    Continuous (fun t : ℝ≥0 => predictableTimeRestrict 𝓕 t U) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmem : MemLp (U : ℝ≥0 × Ω → ℝ) 2
      (nonnegativeLebesgueMeasure.prod P) := Lp.memLp (U : TimeProcessL2 P)
  have hcut : ∀ s, MemLp (timeCutRepresentative U s) 2
      (nonnegativeLebesgueMeasure.prod P) := fun s => hmem.indicator
        (predictable_le_prod 𝓕 _ (measurableSet_predictableTimeFrame 𝓕 s))
  have hi := tendsto_integral_of_dominated_convergence
    (μ := nonnegativeLebesgueMeasure.prod P) (f := fun _ => (0 : ℝ))
    (F := fun n p => (timeCutRepresentative U (u n) p - timeCutRepresentative U t p)^2)
    (fun p => ((U : ℝ≥0 × Ω → ℝ) p)^2)
    (fun n => ((hcut (u n)).aestronglyMeasurable.sub
      (hcut t).aestronglyMeasurable).pow 2)
    hmem.integrable_sq
    (fun n => .of_forall (timeCutRepresentative_sub_sq_le U (u n) t))
    (by
      filter_upwards [ae_time_ne (P := P) t] with p hp
      simpa using ((timeCutRepresentative_tendsto U hu p hp).sub_const
        (timeCutRepresentative U t p)).pow 2)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  simp only [integral_zero, Real.sqrt_zero] at hsqrt
  simpa only [Function.comp_def, ← norm_sq_predictableTimeRestrict_sub,
    Real.sqrt_sq (norm_nonneg _)] using hsqrt

theorem continuous_naturalItoProcess {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (U : PredictableProcessL2 𝓕 P) :
    Continuous (naturalItoProcess hB hsm hfiltered U) :=
  (naturalItoIntegral hB hsm hfiltered).continuous.comp
    (continuous_predictableTimeRestrict U)

@[expose] def finiteTimeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  nonnegativeLebesgueMeasure.restrict (Ioc 0 T)

instance finiteTimeMeasure_isFinite (T : ℝ≥0) : IsFiniteMeasure (finiteTimeMeasure T) :=
  isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)

theorem memLp_naturalItoProcess_time {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (U : PredictableProcessL2 𝓕 P)
    (T : ℝ≥0) : MemLp (naturalItoProcess hB hsm hfiltered U) 2 (finiteTimeMeasure T) :=
  MemLp.of_bound (continuous_naturalItoProcess hB hsm hfiltered U).aestronglyMeasurable
    ‖U‖ (.of_forall (norm_naturalItoProcess_le hB hsm hfiltered U))

/-- The small-time square norm estimate used by stochastic Picard iteration.
The time process on the left is the actual full-filtration Ito operator. -/
theorem integral_norm_sq_naturalItoProcess_le {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (U : PredictableProcessL2 𝓕 P)
    (T : ℝ≥0) :
    ∫ t, ‖naturalItoProcess hB hsm hfiltered U t‖ ^ 2 ∂finiteTimeMeasure T ≤
      (T : ℝ) * ‖U‖ ^ 2 := by
  have hmem := memLp_naturalItoProcess_time hB hsm hfiltered U T
  have hi := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  calc
    ∫ t, ‖naturalItoProcess hB hsm hfiltered U t‖ ^ 2 ∂finiteTimeMeasure T ≤
        ∫ _t, ‖U‖ ^ 2 ∂finiteTimeMeasure T := by
      apply integral_mono_ae hi (integrable_const _)
      exact .of_forall (fun t => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
        (norm_naturalItoProcess_le hB hsm hfiltered U t))
    _ = (T : ℝ) * ‖U‖ ^ 2 := by
      simp [finiteTimeMeasure, integral_const, Measure.real_def,
        nonnegativeLebesgueMeasure_Ioc, ENNReal.toReal_ofReal, NNReal.coe_nonneg]

@[expose] abbrev RandomTimeL2 (P : Measure Ω) (T : ℝ≥0) :=
  Lp (RandomL2 P) 2 (finiteTimeMeasure T)

@[expose] def naturalItoTimeLp {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) : RandomTimeL2 P T :=
  (memLp_naturalItoProcess_time hB hsm hfiltered U T).toLp _

theorem norm_sq_naturalItoTimeLp {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    ‖naturalItoTimeLp hB hsm hfiltered T U‖ ^ 2 =
      ∫ t, ‖naturalItoProcess hB hsm hfiltered U t‖ ^ 2 ∂finiteTimeMeasure T := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_naturalItoProcess_time hB hsm hfiltered U T).coeFn_toLp]
    with t ht
  simp only [naturalItoTimeLp, ht, real_inner_self_eq_norm_sq]

theorem norm_naturalItoTimeLp_le {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    ‖naturalItoTimeLp hB hsm hfiltered T U‖ ≤ Real.sqrt T * ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [norm_sq_naturalItoTimeLp, mul_pow, Real.sq_sqrt T.coe_nonneg]
  exact integral_norm_sq_naturalItoProcess_le hB hsm hfiltered U T

/-- The actual stochastic Volterra operator into the finite-time Bochner
`L²` space, constructed from Ito isometry and deterministic time cutting. -/
@[expose] def naturalItoTimeLinearMap {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0) :
    PredictableProcessL2 𝓕 P →ₗ[ℝ] RandomTimeL2 P T where
  toFun := naturalItoTimeLp hB hsm hfiltered T
  map_add' U V := by
    apply Lp.ext
    filter_upwards [(memLp_naturalItoProcess_time hB hsm hfiltered (U + V) T).coeFn_toLp,
      (memLp_naturalItoProcess_time hB hsm hfiltered U T).coeFn_toLp,
      (memLp_naturalItoProcess_time hB hsm hfiltered V T).coeFn_toLp,
      Lp.coeFn_add (naturalItoTimeLp hB hsm hfiltered T U)
        (naturalItoTimeLp hB hsm hfiltered T V)] with t huv hu hv hadd
    rw [hadd]
    change ((memLp_naturalItoProcess_time hB hsm hfiltered (U + V) T).toLp _ :
      ℝ≥0 → RandomL2 P) t =
      ((memLp_naturalItoProcess_time hB hsm hfiltered U T).toLp _ : ℝ≥0 → RandomL2 P) t +
      ((memLp_naturalItoProcess_time hB hsm hfiltered V T).toLp _ : ℝ≥0 → RandomL2 P) t
    rw [huv, hu, hv]
    simp only [naturalItoProcess, predictableTimeRestrict_add, map_add]
  map_smul' c U := by
    apply Lp.ext
    filter_upwards [(memLp_naturalItoProcess_time hB hsm hfiltered (c • U) T).coeFn_toLp,
      (memLp_naturalItoProcess_time hB hsm hfiltered U T).coeFn_toLp,
      Lp.coeFn_smul c (naturalItoTimeLp hB hsm hfiltered T U)] with t hcU hU hsmul
    simp only [RingHom.id_apply]
    rw [hsmul]
    change ((memLp_naturalItoProcess_time hB hsm hfiltered (c • U) T).toLp _ :
      ℝ≥0 → RandomL2 P) t =
      c • ((memLp_naturalItoProcess_time hB hsm hfiltered U T).toLp _ : ℝ≥0 → RandomL2 P) t
    rw [hcU, hU]
    simp only [naturalItoProcess, predictableTimeRestrict_smul, map_smul]

@[expose] def naturalItoTimeMap {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0) :
    PredictableProcessL2 𝓕 P →L[ℝ] RandomTimeL2 P T :=
  (naturalItoTimeLinearMap hB hsm hfiltered T).mkContinuous (Real.sqrt T)
    (norm_naturalItoTimeLp_le hB hsm hfiltered T)

theorem naturalItoTimeMap_apply {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    naturalItoTimeMap hB hsm hfiltered T U = naturalItoTimeLp hB hsm hfiltered T U := rfl

theorem norm_naturalItoTimeMap_le {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B 𝓕 P) (T : ℝ≥0) :
    ‖naturalItoTimeMap hB hsm hfiltered T‖ ≤ Real.sqrt T :=
  (naturalItoTimeLinearMap hB hsm hfiltered T).mkContinuous_norm_le
    (Real.sqrt_nonneg _) _

end FourPapersCommon.FilteredBrownian
