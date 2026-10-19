module

public import SphericalAging.HardSphereDynamics
public import FourPapersCommon.FilteredItoL2Continuity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import FourPapersCommon.ContinuousAEAdaptedPredictable

public section

/-!
# Finite-driver stochastic integration for the sphere SDE

The driving filtration includes all coordinates. The stochastic operators
below are finite sums of the actual isometrically constructed integrals.
Their continuous versions are proved by the elementary predictable density
and Doob estimates in `FourPapersCommon.FilteredItoContinuous`.
-/

noncomputable section

namespace SphericalAging.HardSphereDynamics

open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal BigOperators ContDiff InnerProductSpace RealInnerProductSpace

theorem hamiltonianGradient_contDiff {N p : ℕ} (J : FiniteModel.Disorder N p) :
    ContDiff ℝ ⊤ (hamiltonianGradient J) := by
  unfold hamiltonianGradient gradient
  exact ((InnerProductSpace.toDual ℝ (State N)).symm.contDiff).comp
    ((FiniteModel.Hamiltonian_contDiff J).fderiv_right (by simp))

theorem contDiff_projection_pair {N : ℕ} :
    ContDiff ℝ ⊤ (fun z : State N × State N => projection z.1 z.2) := by
  simp only [projection, div_eq_mul_inv]
  exact contDiff_snd.sub
    (((contDiff_fst.inner ℝ contDiff_snd).mul contDiff_const).smul contDiff_fst)

theorem contDiff_drift {N : ℕ} (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ ⊤ g) : ContDiff ℝ ⊤ (drift β g) := by
  have hp : ContDiff ℝ ⊤ (fun x : State N => projection x (g x)) := by
    simp only [projection, div_eq_mul_inv]
    exact hg.sub (((contDiff_id.inner ℝ hg).mul contDiff_const).smul contDiff_id)
  exact hp.const_smul β |>.sub (contDiff_id.const_smul (kappa N))

theorem contDiff_hamiltonianDrift {N p : ℕ} (β : ℝ) (J : FiniteModel.Disorder N p) :
    ContDiff ℝ ⊤ (hamiltonianDrift β J) :=
  contDiff_drift β (hamiltonianGradient J) (hamiltonianGradient_contDiff J)

theorem contDiff_noiseColumn {N : ℕ} (j : Fin N) :
    ContDiff ℝ ⊤ (fun x : State N => noiseColumn x j) :=
  (contDiff_projection_pair.comp (contDiff_id.prodMk contDiff_const)).const_smul _

theorem hamiltonianDrift_locallyLipschitz {N p : ℕ} (β : ℝ)
    (J : FiniteModel.Disorder N p) : LocallyLipschitz (hamiltonianDrift β J) :=
  ((contDiff_hamiltonianDrift β J).of_le (by simp)).locallyLipschitz

@[expose] def coefficientBump {N : ℕ} (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : State N) :=
  ⟨R, 2 * R, hR, by linarith⟩

/-- Actual smooth truncation used in the local SDE construction. -/
@[expose] def cutoffCoefficient {N : ℕ} (R : ℝ) (hR : 0 < R) (g : State N → State N) :
    State N → State N := fun x => coefficientBump (N := N) R hR x • g x

theorem cutoffCoefficient_eq {N : ℕ} (R : ℝ) (hR : 0 < R)
    (g : State N → State N) (x : State N) (hx : ‖x‖ ≤ R) :
    cutoffCoefficient R hR g x = g x := by
  have hmem : x ∈ Metric.closedBall (0 : State N) (coefficientBump (N := N) R hR).rIn := by
    simpa [coefficientBump, dist_zero_right] using hx
  simp only [cutoffCoefficient, (coefficientBump (N := N) R hR).one_of_mem_closedBall hmem, one_smul]

theorem cutoffCoefficient_contDiff {N : ℕ} (R : ℝ) (hR : 0 < R)
    (g : State N → State N) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (cutoffCoefficient R hR g) :=
  (coefficientBump (N := N) R hR).contDiff.smul hg

theorem cutoffCoefficient_hasCompactSupport {N : ℕ} (R : ℝ) (hR : 0 < R)
    (g : State N → State N) : HasCompactSupport (cutoffCoefficient R hR g) :=
  (coefficientBump (N := N) R hR).hasCompactSupport.smul_right

theorem cutoffCoefficient_lipschitz {N : ℕ} (R : ℝ) (hR : 0 < R)
    (g : State N → State N) (hg : ContDiff ℝ ∞ g) :
    ∃ K, LipschitzWith K (cutoffCoefficient R hR g) :=
  ContDiff.lipschitzWith_of_hasCompactSupport
    (cutoffCoefficient_hasCompactSupport R hR g) (cutoffCoefficient_contDiff R hR g hg)
    (by simp)

theorem cutoffCoefficient_bounded {N : ℕ} (R : ℝ) (hR : 0 < R)
    (g : State N → State N) (hg : Continuous g) :
    ∃ K : ℝ, ∀ x, ‖cutoffCoefficient R hR g x‖ ≤ K :=
  (cutoffCoefficient_hasCompactSupport R hR g).exists_bound_of_continuous
    ((coefficientBump (N := N) R hR).continuous.smul hg)

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] abbrev PredictableStateL2 (N : ℕ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) :=
  lpMeas (State N) ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P)

theorem lipschitzWith_centered {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) : LipschitzWith K (fun x => g x - g 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hg.dist_le_mul x y

/-- Genuine nonlinear composition on the predictable closed L² space. -/
@[expose] def centeredPredictableCoefficient {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U : PredictableStateL2 N 𝓕 P) : PredictableProcessL2 𝓕 P :=
  ⟨(lipschitzWith_centered hg).compLp (by simp) (U : Lp (State N) 2
    (nonnegativeLebesgueMeasure.prod P)),
    ((lipschitzWith_centered hg).continuous.comp_aestronglyMeasurable
      (lpMeas.aestronglyMeasurable U)).congr
        ((lipschitzWith_centered hg).coeFn_compLp (by simp)
          (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).symm⟩

theorem norm_centeredPredictableCoefficient_sub_le {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U V : PredictableStateL2 N 𝓕 P) :
    ‖centeredPredictableCoefficient hg U - centeredPredictableCoefficient hg V‖ ≤
      K * ‖U - V‖ :=
  (lipschitzWith_centered hg).norm_compLp_sub_le (by simp)
    (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))

/-- Finite-time nonlinear coefficient, including its actual nonzero value
at the zero state. The deterministic term is the elementary predictable
constant on `(0,T]`. -/
@[expose] def predictableCoefficient {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U : PredictableStateL2 N 𝓕 P) (T : ℝ≥0) :
    PredictableProcessL2 𝓕 P :=
  FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 T
    (centeredPredictableCoefficient hg U) +
    g 0 • elementaryPredictable 𝓕 0 T (adaptedOne (P := P) 𝓕 0)

theorem norm_predictableCoefficient_sub_le {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U V : PredictableStateL2 N 𝓕 P) (T : ℝ≥0) :
    ‖predictableCoefficient hg U T - predictableCoefficient hg V T‖ ≤ K * ‖U - V‖ := by
  simp only [predictableCoefficient, add_sub_add_right_eq_sub,
    ← FourPapersCommon.FilteredBrownian.predictableTimeRestrict_sub]
  exact (FourPapersCommon.FilteredBrownian.norm_predictableTimeRestrict_le 𝓕 T _).trans
    (norm_centeredPredictableCoefficient_sub_le hg U V)

theorem predictableCoefficient_coeFn {K : ℝ≥0} {g : State N → ℝ}
    (hg : LipschitzWith K g) (U : PredictableStateL2 N 𝓕 P) (T : ℝ≥0) :
    (predictableCoefficient hg U T : ℝ≥0 × Ω → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      fun p => if p.1 ∈ Ioc 0 T then g ((U : ℝ≥0 × Ω → State N) p) else 0 := by
  have hcenter : (centeredPredictableCoefficient hg U : ℝ≥0 × Ω → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      fun p => g ((U : ℝ≥0 × Ω → State N) p) - g 0 :=
    (lipschitzWith_centered hg).coeFn_compLp (by simp)
      (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  have hone : (adaptedOne (P := P) 𝓕 0 : Ω → ℝ) =ᵐ[P] (fun _ => 1) :=
    Lp.coeFn_const 2 P (1 : ℝ)
  have honep := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae_eq_comp hone
  filter_upwards [Lp.coeFn_add
      (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 T
        (centeredPredictableCoefficient hg U) : TimeProcessL2 P)
      (g 0 • elementaryPredictable 𝓕 0 T (adaptedOne (P := P) 𝓕 0) : TimeProcessL2 P),
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn 𝓕 T
      (centeredPredictableCoefficient hg U), hcenter,
    Lp.coeFn_smul (g 0) (elementaryPredictable 𝓕 0 T (adaptedOne (P := P) 𝓕 0) : TimeProcessL2 P),
    elementaryPredictable_coeFn 𝓕 0 T (adaptedOne (P := P) 𝓕 0), honep]
      with p hadd hcut hcent hsmul hel hone
  change ((FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 T
    (centeredPredictableCoefficient hg U) : TimeProcessL2 P) +
      g 0 • (elementaryPredictable 𝓕 0 T (adaptedOne (P := P) 𝓕 0) : TimeProcessL2 P)) p = _
  rw [hadd, Pi.add_apply, hcut, hsmul, Pi.smul_apply, hel]
  dsimp only [Function.comp_def] at hone
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · simp only [FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      mem_prod, mem_univ, and_true, hp, indicator_of_mem, if_pos, hone,
      smul_eq_mul, mul_one, hcent]
    ring
  · simp [FourPapersCommon.FilteredBrownian.predictableTimeFrame, hp]

/-- The actual finite-driver terminal integration operator. -/
@[expose] def driverItoMap (D : BrownianDriver N P 𝓕) :
    (Fin N → PredictableProcessL2 𝓕 P) →L[ℝ] RandomL2 P :=
  ∑ j : Fin N,
    (FourPapersCommon.FilteredBrownian.naturalItoIntegral
      (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
      (D.filtered j)).comp (ContinuousLinearMap.proj j)

theorem driverItoMap_apply (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) :
    driverItoMap D U = ∑ j : Fin N,
      FourPapersCommon.FilteredBrownian.naturalItoIntegral
        (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
        (D.filtered j) (U j) := by
  simp [driverItoMap]

theorem norm_driverItoMap_le (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) :
    ‖driverItoMap D U‖ ≤ ∑ j : Fin N, ‖U j‖ := by
  rw [driverItoMap_apply]
  exact (norm_sum_le _ _).trans_eq (by
    congr 1
    funext j
    exact FourPapersCommon.FilteredBrownian.norm_naturalItoIntegral
      (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
      (D.filtered j) (U j))

theorem norm_driverItoMap_sub_le (D : BrownianDriver N P 𝓕)
    (U V : Fin N → PredictableProcessL2 𝓕 P) :
    ‖driverItoMap D U - driverItoMap D V‖ ≤ ∑ j : Fin N, ‖U j - V j‖ := by
  rw [← map_sub]
  exact norm_driverItoMap_le D (U - V)

/-- Finite-driver contraction estimate, applicable to matrix coefficients
without reducing adaptedness to individual Brownian filtrations. -/
theorem norm_driverItoMap_sub_le_of_uniform_bound (D : BrownianDriver N P 𝓕)
    (U V : Fin N → PredictableProcessL2 𝓕 P) {K : ℝ}
    (hK : ∀ j, ‖U j - V j‖ ≤ K) :
    ‖driverItoMap D U - driverItoMap D V‖ ≤ N * K := by
  calc
    ‖driverItoMap D U - driverItoMap D V‖ ≤ ∑ j : Fin N, ‖U j - V j‖ :=
      norm_driverItoMap_sub_le D U V
    _ ≤ ∑ _j : Fin N, K := Finset.sum_le_sum (fun j _ => hK j)
    _ = N * K := by simp

@[expose] def driverItoProcess (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) : ℝ≥0 → Ω → ℝ :=
  fun t omega => ∑ j : Fin N,
    FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative
      (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
      (D.filtered j) (U j) t omega

/-- A continuous modification exists for the finite-driver integral itself;
this conclusion is proved from the genuine scalar Ito construction. -/
theorem exists_continuousModification_driverItoProcess
    (D : BrownianDriver N P 𝓕) (U : Fin N → PredictableProcessL2 𝓕 P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsContinuousProcessModification (driverItoProcess D U) Y P := by
  classical
  choose Y hY using fun j : Fin N =>
    FourPapersCommon.FilteredBrownian.exists_continuousModification_naturalItoProcess
      (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (U j)
  refine ⟨fun t omega => ∑ j : Fin N, Y j t omega, ?_⟩
  constructor
  · intro t
    have h : ∀ j : Fin N, ∀ᵐ omega ∂P,
        FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative
          (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
          (D.filtered j) (U j) t omega = Y j t omega := fun j => (hY j).fixedTime_ae_eq t
    filter_upwards [ae_all_iff.2 h] with omega homega
    exact Finset.sum_congr rfl (fun j _ => homega j)
  · have h : ∀ j : Fin N, ∀ᵐ omega ∂P, Continuous (fun t => Y j t omega) :=
      fun j => (hY j).continuous_paths
    filter_upwards [ae_all_iff.2 h] with omega homega
    exact continuous_finset_sum _ (fun j _ => homega j)

theorem locallySquareIntegrableNoise_of_sphere (hN : N ≠ 0)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted 𝓕 X)
    (hXc : ∀ omega, Continuous (fun t => X t omega))
    (hXs : ∀ t omega, OnSphere (X t omega)) :
    LocallySquareIntegrableNoise (P := P) X := by
  intro i j T
  exact FourPapersCommon.memLp_continuousAdaptedTimeCut 𝓕
    (noiseCoefficient X i j) (stronglyAdapted_noiseCoefficient X hXa i j)
    (continuous_noiseCoefficient X hXc i j) ⟨Real.sqrt 2, Real.sqrt_nonneg _⟩
    (fun t omega => noiseCoordinate_norm_le_onSphere hN (X t omega) (hXs t omega) i j) T

theorem noisePredictable_zero (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ omega, Continuous (fun t => X t omega))
    (hXi : LocallySquareIntegrableNoise (P := P) X) (i j : Fin N) :
    noisePredictable X hXa hXc hXi i j 0 = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(hXi i j 0).coeFn_toLp, Lp.coeFn_zero ℝ 2
    (nonnegativeLebesgueMeasure.prod P)] with p hp hz
  change ((hXi i j 0).toLp _ : ℝ≥0 × Ω → ℝ) p = (0 : TimeProcessL2 P) p
  rw [hp, hz]
  simp [FourPapersCommon.continuousAdaptedTimeCut]

theorem coordinateNoiseIntegral_zero (D : BrownianDriver N P 𝓕)
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ omega, Continuous (fun t => X t omega))
    (hXi : LocallySquareIntegrableNoise (P := P) X) (i : Fin N) :
    coordinateNoiseIntegral D X hXa hXc hXi i 0 = 0 := by
  simp [coordinateNoiseIntegral, noisePredictable_zero]

theorem IsStrongSolutionOn_initial {β : ℝ} {g : State N → State N}
    {D : BrownianDriver N P 𝓕} {initial : Ω → State N}
    {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn β g D initial X T) : X 0 =ᵐ[P] initial := by
  rcases h with ⟨hXa, hXc, hXi, h⟩
  have hi : ∀ i : Fin N, ∀ᵐ omega ∂P, (X 0 omega) i = (initial omega) i := by
    intro i
    have he := h 0 (zero_le : 0 ≤ T) i
    rw [coordinateNoiseIntegral_zero] at he
    filter_upwards [he, Lp.coeFn_zero ℝ 2 P] with omega homega hzero
    simpa only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero,
      hzero, Pi.zero_apply] using homega
  filter_upwards [ae_all_iff.2 hi] with omega homega
  exact PiLp.ext homega

@[expose] def noisePredictableAE (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted 𝓕 X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXi : LocallySquareIntegrableNoise (P := P) X)
    (i j : Fin N) (T : ℝ≥0) : PredictableProcessL2 𝓕 P :=
  ⟨(hXi i j T).toLp _,
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut 𝓕
      (noiseCoefficient X i j) (stronglyAdapted_noiseCoefficient X hXa i j)
      (hXc.mono (fun omega hc => (continuous_noiseCoordinate i j).comp hc)) T).congr
        (hXi i j T).coeFn_toLp.symm⟩

@[expose] def coordinateNoiseIntegralAE (D : BrownianDriver N P 𝓕)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted 𝓕 X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXi : LocallySquareIntegrableNoise (P := P) X)
    (i : Fin N) (T : ℝ≥0) : RandomL2 P :=
  driverItoMap D (fun j => noisePredictableAE X hXa hXc hXi i j T)

/-- Standard strong-solution semantics with almost-sure continuous paths.
The matrix coefficients are integrated against the complete driving
filtration using the actual predictable Ito operator. This definition
includes neither existence nor invariance as an assumed assertion. -/
@[expose] def IsAEStrongSolutionOn (β : ℝ) (g : State N → State N)
    (D : BrownianDriver N P 𝓕) (initial : Ω → State N)
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  ∃ (hXa : StronglyAdapted 𝓕 X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXi : LocallySquareIntegrableNoise (P := P) X),
    ∀ t : ℝ≥0, t ≤ T → ∀ i : Fin N, ∀ᵐ omega ∂P,
      (X t omega) i = (initial omega) i +
        (∫ s in (0 : ℝ)..(t : ℝ), (drift β g (X s.toNNReal omega)) i) +
        (coordinateNoiseIntegralAE D X hXa hXc hXi i t : Ω → ℝ) omega

theorem IsStrongSolutionOn.ae {β : ℝ} {g : State N → State N}
    {D : BrownianDriver N P 𝓕} {initial : Ω → State N}
    {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn β g D initial X T) :
    IsAEStrongSolutionOn β g D initial X T := by
  rcases h with ⟨hXa, hXc, hXi, heq⟩
  refine ⟨hXa, .of_forall hXc, hXi, ?_⟩
  intro t ht i
  convert heq t ht i using 1
  simp only [coordinateNoiseIntegralAE, driverItoMap_apply]
  rfl

@[expose] def IsHamiltonianStrongSolutionOn {p : ℕ} (β : ℝ) (J : FiniteModel.Disorder N p)
    (D : BrownianDriver N P 𝓕) (initial : Ω → State N)
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  IsAEStrongSolutionOn β (hamiltonianGradient J) D initial X T

end SphericalAging.HardSphereDynamics
