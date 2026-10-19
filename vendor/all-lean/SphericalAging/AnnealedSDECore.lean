module

public import SphericalAging.ParameterizedDriftLift

public section

/-! Faithful strong-solution semantics for genuine random coefficients,
using actual full-filtration predictable L² classes, real drift integrals,
and the actual finite-vector Itô operator. These semantics permit the
independent Gaussian disorder to be known at time zero.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedSDECore
open HardSphereDynamics PredictableDriftTime PredictableItoTime
set_option maxHeartbeats 1000000
variable {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}

/-- True scalar drift-class identification implies the actual real-time
drift integral equation simultaneously at every time in its horizon. -/
theorem driftVersion_eq_actual (U : PredictableProcessL2 F P) (H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (hU : (U : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut H T) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → driftVersion U T t ω = ∫ s in (0 : ℝ)..(t : ℝ), H s.toNNReal ω := by
  have he : cutRepresentative U T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut H T := by
    filter_upwards [representative_ae U,hU] with z hrep hU
    simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator,Set.mem_prod,Set.mem_univ,and_true,FourPapersCommon.continuousAdaptedTimeCut,hrep,hU]
    split <;> rfl
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  intro t ht
  calc
    driftVersion U T t ω = primitive (fun z : ℝ≥0 × Ω => H z.1 z.2) t ω := by
      unfold driftVersion primitive
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ioc] with s hs hst
      dsimp only [Function.comp_def,Prod.swap] at hs
      exact hs.trans (by simp only [FourPapersCommon.continuousAdaptedTimeCut,
        ite_eq_left (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hst.1,hst.2.trans ht⟩)])
    _ = _ := primitive_eq_real_intervalIntegral _ t ω

/-- Genuine vector Itô terminal classes equal the sum of the genuine
coordinate continuous Itô versions almost everywhere. -/
theorem vectorProcessLp_ae_itoVersions (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) (t : ℝ≥0) :
    (VectorIto.vectorProcessLp D U t : Ω → ℝ) =ᵐ[P] (fun ω => ∑ j : Fin N,
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (U j) t ω) := by
  have hi := ae_all_iff.mpr (fun j : Fin N => itoVersion_ae_eq
    (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (U j) t)
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin N =>
    FourPapersCommon.FilteredBrownian.naturalItoProcess (D.filtered j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) (U j) t)
  filter_upwards [hi,hs] with ω hi hs
  exact hs.trans (Finset.sum_congr rfl (fun j _ => hi j))

/-- Exact random-coefficient strong SDE semantics. The coefficient
classes are existentially actual predictable L² classes and are identified
with the specified coefficient evaluations on the solution. -/
@[expose] def IsRandomStrongSolutionOn (D : BrownianDriver N P F)
    (b : Ω → Fin N → State N → ℝ) (sigma : Ω → Fin N → Fin N → State N → ℝ)
    (Z₀ : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyMeasurable[F 0] Z₀ ∧ StronglyAdapted F X ∧
    (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
    ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => b ω i (X s ω)) T) ∧
      (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => sigma ω i j (X s ω)) T) ∧
      ∀ t, t ≤ T → ∀ i, ∀ᵐ ω ∂P, (X t ω) i = (Z₀ ω) i +
        (∫ s in (0 : ℝ)..(t : ℝ), b ω i (X s.toNNReal ω)) +
          (VectorIto.vectorProcessLp D (U i) t : Ω → ℝ) ω

end SphericalAging.AnnealedSDECore
