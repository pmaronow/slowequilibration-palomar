module

public import SphericalAging.HardSphereStochastic
public import SphericalAging.AdaptedContinuous
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Contracting

public section

/-! The genuine Ito Volterra operator on predictable product L².
Its image is obtained from an adapted continuous version and a deterministic
time cut. Product square integrability is proved by Fubini from the actual
fixed-time Ito isometry. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace SphericalAging.PredictableItoTime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem integral_sq_toLp (H : Ω → ℝ) (hH : MemLp H 2 P) :
    ∫ omega, H omega ^ 2 ∂P = ‖hH.toLp H‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hH.coeFn_toLp] with omega homega
  simp only [homega, RCLike.inner_apply, conj_trivial, pow_two]

theorem memLp_timeCut_of_uniform_L2Bound (H : ℝ≥0 → Ω → ℝ)
    (hHa : StronglyAdapted F H)
    (hHc : ∀ᵐ omega ∂P, Continuous (fun t => H t omega))
    (hHi : ∀ t, MemLp (H t) 2 P) (K : ℝ≥0)
    (hK : ∀ t, ‖(hHi t).toLp (H t)‖ ≤ K) (T : ℝ≥0) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut H T) 2
      (nonnegativeLebesgueMeasure.prod P) := by
  have hmeas := (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut
    F H hHa hHc T).mono (predictable_le_prod F)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  apply (integrable_prod_iff (hmeas.pow 2)).mpr
  constructor
  · exact .of_forall (fun t => by
      by_cases ht : t ∈ Ioc 0 T
      · simpa only [Pi.pow_apply, FourPapersCommon.continuousAdaptedTimeCut, ht, if_pos] using
          (hHi t).integrable_sq
      · simpa [Pi.pow_apply, FourPapersCommon.continuousAdaptedTimeCut, ht] using
          (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P))
  · have hb : Integrable ((Ioc (0 : ℝ≥0) T).indicator (fun _ => (K : ℝ)^2))
        nonnegativeLebesgueMeasure :=
      memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_Ioc ((K : ℝ)^2)
        (Or.inr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)))
    have hm := ((hmeas.pow 2).norm).integral_prod_right'
    apply hb.mono' hm
    exact .of_forall (fun t => by
      by_cases ht : t ∈ Ioc 0 T
      · simp only [Pi.pow_apply, FourPapersCommon.continuousAdaptedTimeCut, ht, if_pos,
          indicator_of_mem, Real.norm_of_nonneg (sq_nonneg _)]
        rw [Real.norm_of_nonneg (integral_nonneg (fun omega => sq_nonneg (H t omega))),
          integral_sq_toLp (H t) (hHi t)]
        exact (sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).2 (hK t)
      · simp [Pi.pow_apply, FourPapersCommon.continuousAdaptedTimeCut, ht])

theorem exists_adapted_itoVersion
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B F P) (U : PredictableProcessL2 F P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, StronglyAdapted F Y ∧ IsContinuousProcessModification
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm hfiltered U) Y P := by
  obtain ⟨Y, hY⟩ :=
    FourPapersCommon.FilteredBrownian.exists_continuousModification_naturalItoProcess
      hB hsm hfiltered U
  exact SphericalAging.AdaptedContinuous.exists_stronglyAdapted_continuousModification
    (FourPapersCommon.FilteredBrownian.stronglyMeasurable_naturalItoProcessRepresentative
      hB.toIsPreBrownianReal hsm hfiltered U) hY

@[expose] def itoVersion (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B F P) (U : PredictableProcessL2 F P) :
    ℝ≥0 → Ω → ℝ := (exists_adapted_itoVersion hB hsm hfiltered U).choose

theorem itoVersion_stronglyAdapted (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) : StronglyAdapted F (itoVersion hB hsm hfiltered U) :=
  (exists_adapted_itoVersion hB hsm hfiltered U).choose_spec.1

theorem itoVersion_continuousModification (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) : IsContinuousProcessModification
      (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm hfiltered U) (itoVersion hB hsm hfiltered U) P :=
  (exists_adapted_itoVersion hB hsm hfiltered U).choose_spec.2

theorem itoVersion_ae_eq (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) (t : ℝ≥0) :
    (FourPapersCommon.FilteredBrownian.naturalItoProcess hB.toIsPreBrownianReal hsm
      hfiltered U t : Ω → ℝ) =ᵐ[P] itoVersion hB hsm hfiltered U t :=
  (FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative
    hB.toIsPreBrownianReal hsm hfiltered U t).trans
      ((itoVersion_continuousModification hB hsm hfiltered U).fixedTime_ae_eq t)

theorem itoVersion_memLp (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) (t : ℝ≥0) :
    MemLp (itoVersion hB hsm hfiltered U t) 2 P :=
  (Lp.memLp (FourPapersCommon.FilteredBrownian.naturalItoProcess
    hB.toIsPreBrownianReal hsm hfiltered U t)).ae_eq (itoVersion_ae_eq hB hsm hfiltered U t)

theorem itoVersion_toLp (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) (t : ℝ≥0) :
    (itoVersion_memLp hB hsm hfiltered U t).toLp _ =
      FourPapersCommon.FilteredBrownian.naturalItoProcess hB.toIsPreBrownianReal hsm
        hfiltered U t := by
  apply Lp.ext
  exact (itoVersion_memLp hB hsm hfiltered U t).coeFn_toLp.trans
    (itoVersion_ae_eq hB hsm hfiltered U t).symm

theorem itoVersion_timeCut_memLp (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U : PredictableProcessL2 F P) (T : ℝ≥0) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (itoVersion hB hsm hfiltered U) T)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  apply memLp_timeCut_of_uniform_L2Bound _ (itoVersion_stronglyAdapted hB hsm hfiltered U)
    (itoVersion_continuousModification hB hsm hfiltered U).continuous_paths
    (itoVersion_memLp hB hsm hfiltered U) ‖U‖₊
  intro t
  rw [itoVersion_toLp]
  exact FourPapersCommon.FilteredBrownian.norm_naturalItoProcess_le
    hB.toIsPreBrownianReal hsm hfiltered U t

/-- Ito integration followed by deterministic time cutting, as an actual
element of the same predictable product L² space used for the integrand. -/
@[expose] def itoVolterra (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hfiltered : IsFilteredPreBrownian B F P) (T : ℝ≥0)
    (U : PredictableProcessL2 F P) : PredictableProcessL2 F P :=
  ⟨(itoVersion_timeCut_memLp hB hsm hfiltered U T).toLp _,
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
      (itoVersion hB hsm hfiltered U) (itoVersion_stronglyAdapted hB hsm hfiltered U)
      (itoVersion_continuousModification hB hsm hfiltered U).continuous_paths T).congr
        (itoVersion_timeCut_memLp hB hsm hfiltered U T).coeFn_toLp.symm⟩

theorem norm_sq_itoVolterra (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖itoVolterra hB hsm hfiltered T U‖ ^ 2 =
      ∫ t, ‖FourPapersCommon.FilteredBrownian.naturalItoProcess
        hB.toIsPreBrownianReal hsm hfiltered U t‖ ^ 2
        ∂FourPapersCommon.FilteredBrownian.finiteTimeMeasure T := by
  change ‖(itoVersion_timeCut_memLp hB hsm hfiltered U T).toLp _‖ ^ 2 = _
  rw [← integral_sq_toLp, integral_prod _
    (itoVersion_timeCut_memLp hB hsm hfiltered U T).integrable_sq]
  have hinner : ∀ t : ℝ≥0,
      (∫ omega, FourPapersCommon.continuousAdaptedTimeCut
        (itoVersion hB hsm hfiltered U) T (t, omega) ^ 2 ∂P) =
      (Ioc (0 : ℝ≥0) T).indicator
        (fun s => ‖FourPapersCommon.FilteredBrownian.naturalItoProcess
          hB.toIsPreBrownianReal hsm hfiltered U s‖ ^ 2) t := by
    intro t
    classical
    by_cases ht : t ∈ Ioc 0 T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut, ht, if_pos, indicator_of_mem]
      rw [integral_sq_toLp _ (itoVersion_memLp hB hsm hfiltered U t), itoVersion_toLp]
    · simp [FourPapersCommon.continuousAdaptedTimeCut, ht]
  simp_rw [hinner]
  exact integral_indicator measurableSet_Ioc

/-- The actual predictable Ito Volterra map has the `√T` small-time norm
bound required in the Banach-space Picard contraction. -/
theorem norm_itoVolterra_le (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    ‖itoVolterra hB hsm hfiltered T U‖ ≤ Real.sqrt T * ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [norm_sq_itoVolterra, mul_pow, Real.sq_sqrt T.coe_nonneg]
  exact FourPapersCommon.FilteredBrownian.integral_norm_sq_naturalItoProcess_le
    hB.toIsPreBrownianReal hsm hfiltered U T

theorem continuous_processes_ae_eq_of_fixedTime {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
    (hZ : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega))
    (hfixed : ∀ t, Y t =ᵐ[P] Z t) :
    ∀ᵐ omega ∂P, ∀ t, Y t omega = Z t omega := by
  have hgrid : ∀ᵐ omega ∂P, ∀ n k : ℕ,
      Y (SphericalAging.AdaptedContinuous.gridTime n k) omega =
        Z (SphericalAging.AdaptedContinuous.gridTime n k) omega :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun k => hfixed _))
  filter_upwards [hY, hZ, hgrid] with omega hy hz hg
  intro t
  exact (SphericalAging.AdaptedContinuous.adaptedVersion_eq_continuous
    (fun _ _ => rfl) hy t).symm.trans
      (SphericalAging.AdaptedContinuous.adaptedVersion_eq_continuous hg hz t)

theorem itoVersion_sub_ae (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (U V : PredictableProcessL2 F P) :
    ∀ᵐ omega ∂P, ∀ t, itoVersion hB hsm hfiltered (U - V) t omega =
      itoVersion hB hsm hfiltered U t omega - itoVersion hB hsm hfiltered V t omega := by
  have hsub := FourPapersCommon.FilteredBrownian.naturalItoContinuousModification_sub
    hB.toIsPreBrownianReal hsm hfiltered U V
    (itoVersion_continuousModification hB hsm hfiltered U)
    (itoVersion_continuousModification hB hsm hfiltered V)
  apply continuous_processes_ae_eq_of_fixedTime
    (itoVersion_continuousModification hB hsm hfiltered (U - V)).continuous_paths
    hsub.continuous_paths
  intro t
  exact ((itoVersion_continuousModification hB hsm hfiltered (U - V)).fixedTime_ae_eq t).symm.trans
    (hsub.fixedTime_ae_eq t)

theorem itoVolterra_sub (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    itoVolterra hB hsm hfiltered T (U - V) =
      itoVolterra hB hsm hfiltered T U - itoVolterra hB hsm hfiltered T V := by
  apply Subtype.ext
  apply Lp.ext
  have hsub := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae (itoVersion_sub_ae hB hsm hfiltered U V)
  filter_upwards [(itoVersion_timeCut_memLp hB hsm hfiltered (U - V) T).coeFn_toLp,
    (itoVersion_timeCut_memLp hB hsm hfiltered U T).coeFn_toLp,
    (itoVersion_timeCut_memLp hB hsm hfiltered V T).coeFn_toLp,
    Lp.coeFn_sub (itoVolterra hB hsm hfiltered T U : TimeProcessL2 P)
      (itoVolterra hB hsm hfiltered T V : TimeProcessL2 P), hsub]
    with p huv hu hv hs hp
  change ((itoVersion_timeCut_memLp hB hsm hfiltered (U - V) T).toLp _ : ℝ≥0 × Ω → ℝ) p =
    ((itoVolterra hB hsm hfiltered T U : TimeProcessL2 P) -
      (itoVolterra hB hsm hfiltered T V : TimeProcessL2 P)) p
  rw [huv, hs, Pi.sub_apply]
  change FourPapersCommon.continuousAdaptedTimeCut (itoVersion hB hsm hfiltered (U - V)) T p =
    ((itoVersion_timeCut_memLp hB hsm hfiltered U T).toLp _ : ℝ≥0 × Ω → ℝ) p -
      ((itoVersion_timeCut_memLp hB hsm hfiltered V T).toLp _ : ℝ≥0 × Ω → ℝ) p
  rw [hu, hv]
  simp only [FourPapersCommon.continuousAdaptedTimeCut]
  split_ifs
  · exact hp p.1
  · simp

theorem norm_itoVolterra_sub_le (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    ‖itoVolterra hB hsm hfiltered T U - itoVolterra hB hsm hfiltered T V‖ ≤
      Real.sqrt T * ‖U - V‖ := by
  rw [← itoVolterra_sub]
  exact norm_itoVolterra_le hB hsm hfiltered T (U - V)

variable {N : ℕ}

@[expose] def stochasticCoefficientMap (D : SphericalAging.HardSphereDynamics.BrownianDriver N P F)
    (j : Fin N) {K : ℝ≥0} {g : SphericalAging.HardSphereDynamics.State N → ℝ}
    (hg : LipschitzWith K g) (T : ℝ≥0)
    (U : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P) :
    PredictableProcessL2 F P :=
  itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T
    (SphericalAging.HardSphereDynamics.predictableCoefficient hg U T)

/-- Actual stochastic part of the Picard map. Both the input coefficient
and output process belong to their proved predictable closed L² spaces. -/
theorem norm_stochasticCoefficientMap_sub_le
    (D : SphericalAging.HardSphereDynamics.BrownianDriver N P F) (j : Fin N)
    {K : ℝ≥0} {g : SphericalAging.HardSphereDynamics.State N → ℝ}
    (hg : LipschitzWith K g) (T : ℝ≥0)
    (U V : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P) :
    ‖stochasticCoefficientMap D j hg T U - stochasticCoefficientMap D j hg T V‖ ≤
      Real.sqrt T * K * ‖U - V‖ := by
  unfold stochasticCoefficientMap
  calc
    _ ≤ Real.sqrt T *
        ‖SphericalAging.HardSphereDynamics.predictableCoefficient hg U T -
          SphericalAging.HardSphereDynamics.predictableCoefficient hg V T‖ :=
      norm_itoVolterra_sub_le (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) T _ _
    _ ≤ Real.sqrt T * ((K : ℝ) * ‖U - V‖) :=
      mul_le_mul_of_nonneg_left
        (SphericalAging.HardSphereDynamics.norm_predictableCoefficient_sub_le hg U V T)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

@[expose] def scalarToStatePredictable (i : Fin N) (U : PredictableProcessL2 F P) :
    SphericalAging.HardSphereDynamics.PredictableStateL2 N F P := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ (SphericalAging.HardSphereDynamics.basisVector i)
  refine ⟨L.compLp (U : TimeProcessL2 P), ?_⟩
  have hcoe : (L.compLp (U : TimeProcessL2 P) : ℝ≥0 × Ω →
      SphericalAging.HardSphereDynamics.State N) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun a => L ((U : TimeProcessL2 P) a)) := L.coeFn_compLp (U : TimeProcessL2 P)
  exact (L.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable U)).congr hcoe.symm

theorem scalarToStatePredictable_sub (i : Fin N) (U V : PredictableProcessL2 F P) :
    scalarToStatePredictable i (U - V) = scalarToStatePredictable i U - scalarToStatePredictable i V := by
  apply Subtype.ext
  exact (ContinuousLinearMap.toSpanSingleton ℝ (SphericalAging.HardSphereDynamics.basisVector i)).compLpL
    2 (nonnegativeLebesgueMeasure.prod P) |>.map_sub (U : TimeProcessL2 P) (V : TimeProcessL2 P)

theorem norm_scalarToStatePredictable_le (i : Fin N) (U : PredictableProcessL2 F P) :
    ‖scalarToStatePredictable i U‖ ≤ ‖U‖ := by
  change ‖((ContinuousLinearMap.toSpanSingleton ℝ
    (SphericalAging.HardSphereDynamics.basisVector i)).compLp (U : TimeProcessL2 P))‖ ≤ ‖(U : TimeProcessL2 P)‖
  have h := (ContinuousLinearMap.toSpanSingleton ℝ
    (SphericalAging.HardSphereDynamics.basisVector i)).norm_compLp_le (U : TimeProcessL2 P)
  simpa only [ContinuousLinearMap.norm_toSpanSingleton,
    SphericalAging.HardSphereDynamics.basisVector, EuclideanSpace.norm_single,
    norm_one, one_mul] using h

@[expose] def finiteNoisePicardMap (D : SphericalAging.HardSphereDynamics.BrownianDriver N P F)
    {K : ℝ≥0} {g : Fin N → Fin N → SphericalAging.HardSphereDynamics.State N → ℝ}
    (hg : ∀ i j, LipschitzWith K (g i j)) (T : ℝ≥0)
    (U : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P) :
    SphericalAging.HardSphereDynamics.PredictableStateL2 N F P :=
  ∑ i : Fin N, scalarToStatePredictable i
    (∑ j : Fin N, stochasticCoefficientMap D j (hg i j) T U)

/-- The complete finite-dimensional stochastic part of Picard iteration is
a proved Lipschitz self-map of the predictable state product L² space. -/
theorem norm_finiteNoisePicardMap_sub_le
    (D : SphericalAging.HardSphereDynamics.BrownianDriver N P F)
    {K : ℝ≥0} {g : Fin N → Fin N → SphericalAging.HardSphereDynamics.State N → ℝ}
    (hg : ∀ i j, LipschitzWith K (g i j)) (T : ℝ≥0)
    (U V : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P) :
    ‖finiteNoisePicardMap D hg T U - finiteNoisePicardMap D hg T V‖ ≤
      (N : ℝ)^2 * Real.sqrt T * K * ‖U - V‖ := by
  unfold finiteNoisePicardMap
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin N, ‖scalarToStatePredictable i
          (∑ j : Fin N, stochasticCoefficientMap D j (hg i j) T U) -
        scalarToStatePredictable i
          (∑ j : Fin N, stochasticCoefficientMap D j (hg i j) T V)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (N : ℝ) * (Real.sqrt T * K * ‖U - V‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarToStatePredictable_sub]
      calc
        _ ≤ ‖(∑ j : Fin N, stochasticCoefficientMap D j (hg i j) T U) -
            (∑ j : Fin N, stochasticCoefficientMap D j (hg i j) T V)‖ :=
          norm_scalarToStatePredictable_le i _
        _ ≤ ∑ j : Fin N, ‖stochasticCoefficientMap D j (hg i j) T U -
            stochasticCoefficientMap D j (hg i j) T V‖ := by
          rw [← Finset.sum_sub_distrib]
          exact norm_sum_le _ _
        _ ≤ ∑ _j : Fin N, Real.sqrt T * K * ‖U - V‖ :=
          Finset.sum_le_sum (fun j _ => norm_stochasticCoefficientMap_sub_le D j (hg i j) T U V)
        _ = _ := by simp
    _ = _ := by simp; ring

/-- Banach fixed point construction for the complete matrix-noise Picard
operator. This proves existence and uniqueness rather than assuming a
stochastic fixed point. A deterministic drift term is handled separately. -/
theorem exists_unique_stochastic_fixedPoint
    (D : SphericalAging.HardSphereDynamics.BrownianDriver N P F)
    {K : ℝ≥0} {g : Fin N → Fin N → SphericalAging.HardSphereDynamics.State N → ℝ}
    (hg : ∀ i j, LipschitzWith K (g i j)) (T : ℝ≥0)
    (A : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P)
    (hsmall : (N : ℝ≥0)^2 * NNReal.sqrt T * K < 1) :
    ∃! U : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P,
      U = A + finiteNoisePicardMap D hg T U := by
  letI : Fact (F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω))) :=
    ⟨predictable_le_prod F⟩
  let f := fun U : SphericalAging.HardSphereDynamics.PredictableStateL2 N F P =>
    A + finiteNoisePicardMap D hg T U
  have hl : LipschitzWith ((N : ℝ≥0)^2 * NNReal.sqrt T * K) f := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simpa only [f, dist_eq_norm, add_sub_add_left_eq_sub, NNReal.coe_mul,
      NNReal.coe_pow, NNReal.coe_natCast, Real.coe_sqrt] using
      norm_finiteNoisePicardMap_sub_le D hg T U V
  have hc : ContractingWith ((N : ℝ≥0)^2 * NNReal.sqrt T * K) f := ⟨hsmall, hl⟩
  refine ⟨hc.fixedPoint, hc.fixedPoint_isFixedPt.symm, ?_⟩
  intro U hU
  exact hc.fixedPoint_unique hU.symm

end SphericalAging.PredictableItoTime
