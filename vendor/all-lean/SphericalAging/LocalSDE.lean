module

public import SphericalAging.PredictableDriftTime

public section

/-! Constructive local Picard versions for the full finite-dimensional SDE.
The state space is the actual predictable product L² Banach space and every
stochastic integral uses the complete driving filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.LocalSDE
open HardSphereDynamics PredictableItoTime PredictableDriftTime
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The contraction horizon always exists for finite Lipschitz constants. -/
theorem exists_pos_contraction_horizon (N : ℕ) (Kb Ks : ℝ≥0) :
    ∃ T : ℝ≥0, 0 < T ∧ (N : ℝ≥0) * T * Kb + (N : ℝ≥0)^2 * NNReal.sqrt T * Ks < 1 := by
  let q := fun T : ℝ≥0 => (N : ℝ≥0) * T * Kb + (N : ℝ≥0)^2 * NNReal.sqrt T * Ks
  have hq : Continuous q := by fun_prop
  have hz : q 0 < 1 := by simp [q]
  have hev : ∀ᶠ T in 𝓝 (0 : ℝ≥0), q T < 1 := hq.continuousAt.eventually (eventually_lt_nhds hz)
  obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let T : ℝ≥0 := ⟨eps / 2, by positivity⟩
  have hTpos : 0 < T := by
    show (0 : ℝ) < eps / 2
    positivity
  have hcoe : (T : ℝ) = eps / 2 := rfl
  have hTdist : dist T 0 < eps := by
    rw [NNReal.dist_eq, hcoe, NNReal.coe_zero, sub_zero, abs_of_pos (by positivity : 0 < eps / 2)]
    linarith
  exact ⟨T, hTpos, hball hTdist⟩

@[expose] def initialClass (x0 : State N) (T : ℝ≥0) : PredictableStateL2 N F P :=
  ∑ i : Fin N, scalarToStatePredictable i
    (predictableCoefficient (LipschitzWith.const (x0 i)) (0 : PredictableStateL2 N F P) T)

@[expose] def coordinateVersion (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (i : Fin N) (t : ℝ≥0) (omega : Ω) : ℝ :=
  x0 i + driftVersion (predictableCoefficient (hb i) U T) T t omega +
    ∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
      (predictableCoefficient (hsigma i j) U T) t omega

@[expose] def version (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (t : ℝ≥0) (omega : Ω) : State N :=
  ∑ i : Fin N, coordinateVersion D hb hsigma x0 T U i t omega • basisVector i

theorem coordinateVersion_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (i : Fin N) :
    StronglyAdapted F (coordinateVersion D hb hsigma x0 T U i) := by
  intro t
  apply StronglyMeasurable.add
  · exact stronglyMeasurable_const.add (driftVersion_stronglyAdapted _ T t)
  · exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ =>
      itoVersion_stronglyAdapted (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t)

theorem version_stronglyAdapted (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    StronglyAdapted F (version D hb hsigma x0 T U) := by
  intro t
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (coordinateVersion_stronglyAdapted D hb hsigma x0 T U i t).smul_const (basisVector i))

theorem coordinateVersion_ae_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (i : Fin N) :
    ∀ᵐ omega ∂P, Continuous (fun t => coordinateVersion D hb hsigma x0 T U i t omega) := by
  have hall : ∀ᵐ omega ∂P, ∀ j : Fin N, Continuous (fun t =>
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (predictableCoefficient (hsigma i j) U T) t omega) :=
    ae_all_iff.mpr (fun j => (itoVersion_continuousModification (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) _).continuous_paths)
  filter_upwards [driftVersion_ae_continuous (predictableCoefficient (hb i) U T) T, hall]
    with omega hbcont hscont
  exact (continuous_const.add hbcont).add (continuous_finsetSum Finset.univ (fun j _ => hscont j))

theorem version_ae_continuous (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    ∀ᵐ omega ∂P, Continuous (fun t => version D hb hsigma x0 T U t omega) := by
  have hall := ae_all_iff.mpr (fun i => coordinateVersion_ae_continuous D hb hsigma x0 T U i)
  filter_upwards [hall] with omega homega
  exact continuous_finsetSum Finset.univ (fun i _ => (homega i).smul continuous_const)


theorem scalarToStatePredictable_coeFn (i : Fin N) (U : PredictableProcessL2 F P) :
    (scalarToStatePredictable i U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun p => (U : TimeProcessL2 P) p • basisVector i) := by
  change ((ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLp
    (U : TimeProcessL2 P) : ℝ≥0 × Ω → State N) =ᵐ[_] _
  exact (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp (U : TimeProcessL2 P)

theorem sumState_coeFn (W : Fin N → PredictableStateL2 N F P) :
    (∑ i, W i : PredictableStateL2 N F P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun p => ∑ i, (W i : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) p) := by
  simpa only [Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => (W i : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))

theorem sumScalar_coeFn (W : Fin N → PredictableProcessL2 F P) :
    (∑ i, W i : PredictableProcessL2 F P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun p => ∑ i, (W i : TimeProcessL2 P) p) := by
  simpa only [Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => (W i : TimeProcessL2 P))

theorem state_sum_basis (x : State N) : ∑ i : Fin N, x i • basisVector i = x := by
  apply PiLp.ext
  intro j
  simp [basisVector, PiLp.smul_apply, PiLp.single_apply, Pi.single_apply]

theorem initialClass_coeFn (x0 : State N) (T : ℝ≥0) :
    (initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => x0)) := by
  have hs := sumState_coeFn (fun i => scalarToStatePredictable i
    (predictableCoefficient (LipschitzWith.const (x0 i)) (0 : PredictableStateL2 N F P) T))
  have hi := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (predictableCoefficient (LipschitzWith.const (x0 i)) (0 : PredictableStateL2 N F P) T))
  have hc := ae_all_iff.mpr (fun i : Fin N => predictableCoefficient_coeFn
    (LipschitzWith.const (x0 i)) (0 : PredictableStateL2 N F P) T)
  filter_upwards [hs, hi, hc] with p hp hi hc
  unfold initialClass
  rw [hp]
  by_cases hpt : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hpt, mem_univ _⟩,
      indicator_of_mem]
    simpa only [hi, hc, hpt, if_pos] using state_sum_basis x0
  · simp [hi, hc, hpt]



theorem finiteDriftPicardMap_coeFn {Kb : ℝ≥0} {b : Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun p => if p.1 ∈ Ioc (0 : ℝ≥0) T then
        ∑ i : Fin N, driftVersion (predictableCoefficient (hb i) U T) T p.1 p.2 • basisVector i
      else 0) := by
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i (driftCoefficientMap (hb i) T U))
  have hincl := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (driftCoefficientMap (hb i) T U))
  have hcoeff : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ∀ i : Fin N,
      (driftCoefficientMap (hb i) T U : TimeProcessL2 P) p =
        FourPapersCommon.continuousAdaptedTimeCut
          (driftVersion (predictableCoefficient (hb i) U T) T) T p :=
    ae_all_iff.mpr (fun i => (driftVersion_timeCut_memLp (predictableCoefficient (hb i) U T) T).coeFn_toLp)
  filter_upwards [hsum, hincl, hcoeff] with p hp hi hc
  unfold finiteDriftPicardMap
  rw [hp]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp [hi, hc, FourPapersCommon.continuousAdaptedTimeCut, ht]
  · simp [hi, hc, FourPapersCommon.continuousAdaptedTimeCut, ht]

theorem finiteNoisePicardMap_coeFn (D : BrownianDriver N P F) {Ks : ℝ≥0}
    {sigma : Fin N → Fin N → State N → ℝ}
    (hsigma : ∀ i j, LipschitzWith Ks (sigma i j)) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun p => if p.1 ∈ Ioc (0 : ℝ≥0) T then
        ∑ i : Fin N, (∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) (predictableCoefficient (hsigma i j) U T) p.1 p.2) • basisVector i
      else 0) := by
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i
    (∑ j : Fin N, stochasticCoefficientMap D j (hsigma i j) T U))
  have hincl := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (∑ j : Fin N, stochasticCoefficientMap D j (hsigma i j) T U))
  have hinner := ae_all_iff.mpr (fun i : Fin N => sumScalar_coeFn
    (fun j => stochasticCoefficientMap D j (hsigma i j) T U))
  have hcoeff : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ∀ i j : Fin N,
      (stochasticCoefficientMap D j (hsigma i j) T U : TimeProcessL2 P) p =
        FourPapersCommon.continuousAdaptedTimeCut
          (itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
            (D.filtered j) (predictableCoefficient (hsigma i j) U T)) T p :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      (itoVersion_timeCut_memLp (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (predictableCoefficient (hsigma i j) U T) T).coeFn_toLp))
  filter_upwards [hsum, hincl, hinner, hcoeff] with p hp hi hj hc
  unfold finiteNoisePicardMap
  rw [hp]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [if_pos ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i, hj i]
    simp only [hc, FourPapersCommon.continuousAdaptedTimeCut, if_pos ht]
  · simp only [if_neg ht]
    have hz : ∀ i : Fin N, (scalarToStatePredictable i
        (∑ j : Fin N, stochasticCoefficientMap D j (hsigma i j) T U) :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) p = 0 := by
      intro i
      rw [hi i, hj i]
      simp only [hc, FourPapersCommon.continuousAdaptedTimeCut, if_neg ht,
        Finset.sum_const_zero, zero_smul]
    simp only [hz, Finset.sum_const_zero]

theorem version_timeCut_eq_fixedPoint_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (hfixed : U = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma x0 T U p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hadd := Lp.coeFn_add
    ((initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
      (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  have hadd' := Lp.coeFn_add
    (initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  filter_upwards [hadd, hadd', initialClass_coeFn (F := F) (P := P) x0 T, finiteDriftPicardMap_coeFn hb T U,
    finiteNoisePicardMap_coeFn D hsigma T U] with p hp hp' h0 hbcoe hscoe
  conv_rhs => rw [hfixed]
  change _ = (((initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) +
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) p
  rw [hp, Pi.add_apply, hp', Pi.add_apply, h0, hbcoe, hscoe]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht, mem_univ _⟩,
      indicator_of_mem, ht, if_pos]
    simp only [version, coordinateVersion, add_smul, Finset.sum_add_distrib, state_sum_basis]
  · simp [ht]

section CoefficientIdentification
variable {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} {T : ℝ≥0}
  (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
include hXeq

/-- Evaluation on the constructed process gives exactly the same predictable
coefficient class as nonlinear composition of the fixed point. -/
theorem coefficient_timeCut_ae {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (t : ℝ≥0) (ht : t ≤ T) :
    FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) t
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t
          (predictableCoefficient hg U T) : TimeProcessL2 P) := by
  filter_upwards [hXeq, FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t
    (predictableCoefficient hg U T), predictableCoefficient_coeFn hg U T] with p hp hcut hcoeff
  rw [hcut]
  by_cases hpt : p.1 ∈ Ioc (0 : ℝ≥0) t
  · have hpT : p.1 ∈ Ioc (0 : ℝ≥0) T := ⟨hpt.1, hpt.2.trans ht⟩
    have hx : X p.1 p.2 = (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) p := by
      simpa only [indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from
        ⟨hpT, mem_univ _⟩)] using hp
    simp only [FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      FourPapersCommon.continuousAdaptedTimeCut, hpt, if_pos,
      indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from ⟨hpt, mem_univ _⟩)]
    rw [hcoeff, if_pos hpT, hx]
  · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      FourPapersCommon.continuousAdaptedTimeCut, hpt]

theorem coefficient_timeCut_memLp {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) t) 2
      (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t
    (predictableCoefficient hg U T) : TimeProcessL2 P)).ae_eq
      (coefficient_timeCut_ae hXeq hg t ht).symm

@[expose] def coefficientClassAt (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) (t : ℝ≥0) (ht : t ≤ T) :
    PredictableProcessL2 F P :=
  ⟨(coefficient_timeCut_memLp hXeq hg t ht).toLp _,
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F (fun s omega => g (X s omega))
      (fun s => hg.continuous.comp_stronglyMeasurable (hXa s))
      (hXc.mono (fun omega hc => hg.continuous.comp hc)) t).congr
        (coefficient_timeCut_memLp hXeq hg t ht).coeFn_toLp.symm⟩

theorem coefficientClassAt_eq (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) (t : ℝ≥0) (ht : t ≤ T) :
    coefficientClassAt hXeq hXa hXc hg t ht =
      FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (predictableCoefficient hg U T) := by
  apply Subtype.ext
  apply Lp.ext
  exact (coefficient_timeCut_memLp hXeq hg t ht).coeFn_toLp.trans (coefficient_timeCut_ae hXeq hg t ht)


theorem cutRepresentative_coefficient_ae {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) :
    cutRepresentative (predictableCoefficient hg U T) T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) T := by
  filter_upwards [hXeq, representative_ae (predictableCoefficient hg U T),
    predictableCoefficient_coeFn hg U T] with p hp hrep hcoeff
  by_cases hpt : p.1 ∈ Ioc (0 : ℝ≥0) T
  · have hx : X p.1 p.2 = (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) p := by
      simpa only [indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from
        ⟨hpt, mem_univ _⟩)] using hp
    simp only [cutRepresentative, FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hpt, mem_univ _⟩),
      FourPapersCommon.continuousAdaptedTimeCut, if_pos hpt, hrep, hcoeff, hx]
  · simp [cutRepresentative, FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      FourPapersCommon.continuousAdaptedTimeCut, hpt]

/-- The drift of the Picard version is the actual nonlinear drift evaluated
on its state, for all times up to the construction horizon. -/
theorem driftVersion_eq_actual_drift_ae {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) :
    ∀ᵐ omega ∂P, ∀ t : ℝ≥0, t ≤ T →
      driftVersion (predictableCoefficient hg U T) T t omega =
        ∫ s in (0 : ℝ)..(t : ℝ), g (X s.toNNReal omega) := by
  have hswap : ∀ᵐ p ∂P.prod nonnegativeLebesgueMeasure,
      cutRepresentative (predictableCoefficient hg U T) T (p.2, p.1) =
        FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) T (p.2, p.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae (cutRepresentative_coefficient_ae hXeq hg)
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with omega homega
  intro t ht
  rw [← primitive_eq_real_intervalIntegral (fun p => g (X p.1 p.2)) t omega]
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae homega, ae_restrict_mem measurableSet_Ioc]
    with s hs hst
  rw [hs]
  exact if_pos (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hst.1, hst.2.trans ht⟩)

/-- The stochastic integral of coefficients evaluated on the actual version
agrees with its constructed continuous Itô representative. -/
theorem actual_integral_ae_eq_itoVersion (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    (D : BrownianDriver N P F) (j : Fin N) {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (t : ℝ≥0) (ht : t ≤ T) :
    (FourPapersCommon.FilteredBrownian.naturalItoIntegral
      (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j)
        (coefficientClassAt hXeq hXa hXc hg t ht) : Ω → ℝ)
      =ᵐ[P] itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (predictableCoefficient hg U T) t := by
  rw [coefficientClassAt_eq]
  exact itoVersion_ae_eq (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t

end CoefficientIdentification

/-- Existence of the actual adapted continuous Picard version, including
its proved coefficient-class interpretation. -/
theorem exists_local_continuous_picard_version (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j)) (x0 : State N) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ U : PredictableStateL2 N F P,
      U = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U ∧
      StronglyAdapted F (version D hb hsigma x0 T U) ∧
      (∀ᵐ omega ∂P, Continuous (fun t => version D hb hsigma x0 T U t omega)) ∧
      (((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma x0 T U p.1 p.2))
        =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) := by
  obtain ⟨T, hTpos, hsmall⟩ := exists_pos_contraction_horizon N Kb Ks
  obtain ⟨U, hU, _huniq⟩ := exists_unique_local_picard_fixedPoint D hb hsigma T
    (initialClass (F := F) (P := P) x0 T) hsmall
  exact ⟨T, hTpos, U, hU, version_stronglyAdapted D hb hsigma x0 T U,
    version_ae_continuous D hb hsigma x0 T U, version_timeCut_eq_fixedPoint_ae D hb hsigma x0 T U hU⟩


@[expose] def coefficientPredictableActual {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    {g : State N → ℝ} (hg : Continuous g) (t : ℝ≥0)
    (hmem : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) t)
      2 (nonnegativeLebesgueMeasure.prod P)) : PredictableProcessL2 F P :=
  ⟨hmem.toLp _, (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
      (fun s omega => g (X s omega)) (fun s => hg.comp_stronglyMeasurable (hXa s))
      (hXc.mono (fun omega hc => hg.comp hc)) t).congr hmem.coeFn_toLp.symm⟩

theorem coefficientClassAt_eq_actual {X : ℝ≥0 → Ω → State N}
    {U : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) (t : ℝ≥0) (ht : t ≤ T) :
    coefficientClassAt hXeq hXa hXc hg t ht =
      coefficientPredictableActual hXa hXc hg.continuous t (coefficient_timeCut_memLp hXeq hg t ht) := rfl

theorem actual_driverIto_ae_eq {X : ℝ≥0 → Ω → State N}
    {U : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    (D : BrownianDriver N P F) {Ks : ℝ≥0} {sigma : Fin N → State N → ℝ}
    (hsigma : ∀ j, LipschitzWith Ks (sigma j)) (t : ℝ≥0) (ht : t ≤ T) :
    (driverItoMap D (fun j => coefficientPredictableActual hXa hXc (hsigma j).continuous t
        (coefficient_timeCut_memLp hXeq (hsigma j) t ht)) : Ω → ℝ)
      =ᵐ[P] (fun omega => ∑ j : Fin N, itoVersion (D.brownian j)
        (D.coordinateStronglyMeasurable j) (D.filtered j) (predictableCoefficient (hsigma j) U T) t omega) := by
  have hi := ae_all_iff.mpr (fun j : Fin N => actual_integral_ae_eq_itoVersion hXeq hXa hXc D j
    (hsigma j) t ht)
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin N =>
    FourPapersCommon.FilteredBrownian.naturalItoIntegral (D.brownian j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) (coefficientClassAt hXeq hXa hXc (hsigma j) t ht))
  filter_upwards [hi, hsum] with omega hi hs
  rw [driverItoMap_apply]
  change ((∑ j : Fin N, FourPapersCommon.FilteredBrownian.naturalItoIntegral
    (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j)
      (coefficientClassAt hXeq hXa hXc (hsigma j) t ht) : RandomL2 P) : Ω → ℝ) omega = _
  rw [hs]
  simp only [hi]

/-- Faithful local strong-solution semantics with the actual full-filtration
matrix Itô integral. Existence, adaptation and continuity are not assumed
by the theorem constructing a value of this predicate. -/
@[expose] def IsLocalStrongSolutionOn (b : Fin N → State N → ℝ) (sigma : Fin N → Fin N → State N → ℝ)
    (hsigma : ∀ i j, Continuous (sigma i j)) (D : BrownianDriver N P F) (x0 : State N)
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  ∃ (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    (_hbmem : ∀ i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s omega => b i (X s omega)) T) 2 (nonnegativeLebesgueMeasure.prod P))
    (hsigmamem : ∀ i j (t : ℝ≥0), t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => sigma i j (X s omega)) t)
      2 (nonnegativeLebesgueMeasure.prod P)),
    ∀ t : ℝ≥0, ∀ ht : t ≤ T, ∀ i : Fin N, ∀ᵐ omega ∂P,
      (X t omega) i = x0 i + (∫ s in (0 : ℝ)..(t : ℝ), b i (X s.toNNReal omega)) +
        (driverItoMap D (fun j => coefficientPredictableActual hXa hXc (hsigma i j) t
          (hsigmamem i j t ht)) : Ω → ℝ) omega

theorem version_apply (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) (t : ℝ≥0) (omega : Ω) (i : Fin N) :
    (version D hb hsigma x0 T U t omega) i = coordinateVersion D hb hsigma x0 T U i t omega := by
  simp [version, basisVector, Pi.single_apply]

/-- Actual local strong-solution existence for a finite matrix-driven SDE
with globally Lipschitz coefficients and a deterministic initial state. -/
theorem exists_local_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j)) (x0 : State N) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ X : ℝ≥0 → Ω → State N,
      IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T := by
  obtain ⟨T, hT, U, hU, hXa, hXc, hXeq⟩ := exists_local_continuous_picard_version D hb hsigma x0
  refine ⟨T, hT, version D hb hsigma x0 T U, hXa, hXc,
    (fun i => coefficient_timeCut_memLp hXeq (hb i) T le_rfl),
    (fun i j t ht => coefficient_timeCut_memLp hXeq (hsigma i j) t ht), ?_⟩
  intro t ht i
  filter_upwards [driftVersion_eq_actual_drift_ae hXeq (hb i),
    actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega hbactual hsactual
  rw [version_apply, hsactual]
  simp only [coordinateVersion, hbactual t ht]



theorem coefficientPredictableActual_zero {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    {g : State N → ℝ} (hg : Continuous g)
    (hmem : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s omega => g (X s omega)) 0)
      2 (nonnegativeLebesgueMeasure.prod P)) :
    coefficientPredictableActual hXa hXc hg 0 hmem = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hmem.coeFn_toLp,
    Lp.coeFn_zero ℝ 2 (nonnegativeLebesgueMeasure.prod P)] with p hp hz
  change (hmem.toLp _ : ℝ≥0 × Ω → ℝ) p = (0 : TimeProcessL2 P) p
  rw [hp, hz]
  simp [FourPapersCommon.continuousAdaptedTimeCut]

/-- The constructed strong solution starts from the specified state. -/
theorem IsLocalStrongSolutionOn.initial {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ} {hsigma : ∀ i j, Continuous (sigma i j)}
    {D : BrownianDriver N P F} {x0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsLocalStrongSolutionOn b sigma hsigma D x0 X T) :
    ∀ᵐ omega ∂P, X 0 omega = x0 := by
  rcases h with ⟨hXa, hXc, hbmem, hsigmamem, heq⟩
  have hi : ∀ i : Fin N, ∀ᵐ omega ∂P, (X 0 omega) i = x0 i := by
    intro i
    have hzero : (fun j => coefficientPredictableActual hXa hXc (hsigma i j) 0
        (hsigmamem i j 0 (zero_le : 0 ≤ T))) = (0 : Fin N → PredictableProcessL2 F P) := by
      funext j
      exact coefficientPredictableActual_zero hXa hXc (hsigma i j) _
    have h0 := heq 0 (zero_le : 0 ≤ T) i
    rw [hzero, map_zero] at h0
    filter_upwards [h0, Lp.coeFn_zero ℝ 2 P] with omega homega hz
    simpa only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero, hz, Pi.zero_apply] using homega
  filter_upwards [ae_all_iff.mpr hi] with omega homega
  exact PiLp.ext homega

end SphericalAging.LocalSDE
