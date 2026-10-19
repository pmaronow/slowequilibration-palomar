module

public import SphericalAging.LinearSDELocalization

public section

/-! Faithful bounded predictable affine matrix SDE semantics.  Drift
forcing is actual predictable data, rather than a supplied moment bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.InhomogeneousLinearSDE
open HardSphereDynamics PredictableDriftTime PredictableLinearCoefficient VectorIto
set_option maxHeartbeats 1200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

structure Forcing (B : ℝ≥0) where
  value : ℝ≥0 × Ω → ℝ
  predictable : AEStronglyMeasurable[F.predictable] value (nonnegativeLebesgueMeasure.prod P)
  bound : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, ‖value q‖ ≤ B

/-- The actual drift contains the given bounded forcing, and every noise
class is the given matrix coefficient evaluated at the state. -/
@[expose] def IsStrongSolutionOn {Kb Ks B : ℝ≥0}
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → Forcing (F := F) (P := P) B)
    (D : BrownianDriver N P F) (v0 : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyAdapted F X ∧ (∀ᵐ omega ∂P, Continuous (fun t => X t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
    (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega =>
        (a i).value (s,omega) (X s omega) + (forcing i).value (s,omega)) T) ∧
    (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma i j).value (s,omega) (X s omega)) T) ∧
    ∀ t, t ≤ T → ∀ i, ∀ᵐ omega ∂P, X t omega i = v0 i +
      (∫ s in (0 : ℝ)..(t : ℝ), (a i).value (s.toNNReal,omega) (X s.toNNReal omega) +
        (forcing i).value (s.toNNReal,omega)) +
      (HardSphereDynamics.driverItoMap D
        (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) : Ω → ℝ) omega

theorem driftVersion_eq_actual_of_coe (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (A : PredictableProcessL2 F P)
    (hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut f T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → driftVersion A T t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), f s.toNNReal ω := by
  have hc : cutRepresentative A T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut f T := by
    filter_upwards [representative_ae A,hA] with q hr ha
    unfold cutRepresentative FourPapersCommon.FilteredBrownian.predictableTimeFrame
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),hr,ha]
    · simp [ht,FourPapersCommon.continuousAdaptedTimeCut]
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  intro t ht
  change driftVersion A T t ω = ∫ s in (0 : ℝ)..(t : ℝ), (Function.uncurry f) (s.toNNReal,ω)
  rw [← primitive_eq_real_intervalIntegral (Function.uncurry f) t ω]
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ioc] with r hr hrt
  change cutRepresentative A T (r,ω) =
    FourPapersCommon.continuousAdaptedTimeCut f T (r,ω) at hr
  rw [hr]
  exact ite_eq_left ⟨hrt.1,hrt.2.trans ht⟩

theorem strongSolution_class_equation {Kb Ks B : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T) :
    ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => (a i).value (s,ω) (X s ω) + (forcing i).value (s,ω)) T) ∧
      (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => (sigma i j).value (s,ω) (X s ω)) T) ∧
      (∀ t, t ≤ T → ∀ i, ∀ᵐ ω ∂P, X t ω i = v0 i + driftVersion (A i) T t ω + vectorProcess D (U i) t ω) := by
  rcases h with ⟨_,_,A,U,hA,hU,heq⟩
  refine ⟨A,U,hA,hU,?_⟩
  intro t ht i
  have hdrift := driftVersion_eq_actual_of_coe (fun s ω => (a i).value (s,ω) (X s ω) + (forcing i).value (s,ω)) T (A i) (hA i)
  have hnoise : HardSphereDynamics.driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) =
      vectorProcessLp D (U i) t := CutoffSphere.driverItoMap_eq_vectorIto D _
  have hh := heq t ht i
  rw [hnoise] at hh
  filter_upwards [hh,hdrift,vectorProcessLp_ae_eq D (U i) t] with ω hω hd hn
  rw [← hd t ht,hn] at hω
  exact hω

theorem IsStrongSolutionOn.initial {Kb Ks B : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T) : ∀ᵐ ω ∂P, X 0 ω = v0 := by
  obtain ⟨A,U,_,_,heq⟩ := strongSolution_class_equation h
  have hnoise (i : Fin N) : vectorProcess D (U i) 0 =ᵐ[P] fun _ => (0 : ℝ) := by
    have he := vectorProcessLp_ae_eq D (U i) 0
    rw [LinearSDELocalization.vectorProcessLp_zero_time] at he
    exact he.symm.trans (Lp.coeFn_zero ℝ 2 P)
  filter_upwards [ae_all_iff.mpr (fun i => heq 0 bot_le i),ae_all_iff.mpr hnoise] with ω hω hn
  apply PiLp.ext
  intro i
  have hh := hω i
  simp only [driftVersion,primitive,Ioc_self,Measure.restrict_empty,integral_zero_measure,hn i,add_zero] at hh
  exact hh


end SphericalAging.InhomogeneousLinearSDE
