module

public import SphericalAging.InhomogeneousLinearSDE
public import SphericalAging.HamiltonianParameter
public import SphericalAging.SecantPredictable

public section

/-! The actual predictable bounded tensor-disorder forcing in the cutoff
Hamiltonian SDE, including its faithful coefficient-class interpretation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianPredictableForcing
open HardSphereDynamics LocalSDE HamiltonianParameter InhomogeneousLinearSDE
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def disorderConstant (β : ℝ) (R : ℝ) (hR : 0 < R) : ℝ≥0 :=
  (cutoffDrift_disorder_lipschitz (N := N) (p := p) β R hR).choose

 theorem scalar_disorder_bound (β : ℝ) (J K : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (i : Fin N) (x : State N) :
    ‖CutoffSDE.cutoffDrift β K R hR i x-CutoffSDE.cutoffDrift β J R hR i x‖ ≤
      (disorderConstant (N := N) (p := p) β R hR : ℝ)*‖K-J‖ := by
  apply (show ‖CutoffSDE.cutoffDrift β K R hR i x-CutoffSDE.cutoffDrift β J R hR i x‖ ≤
      ‖cutoffCoefficient R hR (hamiltonianDrift β K) x-cutoffCoefficient R hR (hamiltonianDrift β J) x‖ from by
    simpa only [CutoffSDE.cutoffDrift,NNReal.coe_one,one_mul] using
      (CutoffSDE.coordinate_lipschitz i).norm_sub_le
        (cutoffCoefficient R hR (hamiltonianDrift β K) x) (cutoffCoefficient R hR (hamiltonianDrift β J) x)).trans
  exact (cutoffDrift_disorder_lipschitz β R hR).choose_spec K J x

@[expose]  def disorderForcing (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J K : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (T : ℝ≥0) (i : Fin N) :
    Forcing (F := F) (P := P) (disorderConstant (N := N) (p := p) β R hR*‖K-J‖₊) where
  value := FourPapersCommon.continuousAdaptedTimeCut
    (fun t omega => CutoffSDE.cutoffDrift β K R hR i (X t omega)-CutoffSDE.cutoffDrift β J R hR i (X t omega)) T
  predictable := FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _
    (fun t => (((VariationalCoefficients.cutoffDrift_contDiff β K R hR i).continuous.comp_stronglyMeasurable (hXa t)).sub
      ((VariationalCoefficients.cutoffDrift_contDiff β J R hR i).continuous.comp_stronglyMeasurable (hXa t))))
    (by
      filter_upwards [hXc] with omega hc
      exact ((VariationalCoefficients.cutoffDrift_contDiff β K R hR i).continuous.comp hc).sub
        ((VariationalCoefficients.cutoffDrift_contDiff β J R hR i).continuous.comp hc)) T
  bound := .of_forall (fun q => by
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,NNReal.coe_mul,coe_nnnorm]
      exact scalar_disorder_bound β J K R hR i (X q.1 q.2)
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,norm_zero]
      exact (disorderConstant (N := N) (p := p) β R hR*‖K-J‖₊).coe_nonneg)

 theorem disorderForcing_affine (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J K : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (i : Fin N) (q : ℝ≥0 × Ω) :
    (disorderForcing X hXa hXc β J K R hR T i).value q =
      if q.1 ∈ Ioc 0 T then ∑ I,(K I-J I)*(couplingDrift β R hR I (X q.1 q.2)) i else 0 := by
  change (if q.1 ∈ Ioc 0 T then CutoffSDE.cutoffDrift β K R hR i (X q.1 q.2)-
    CutoffSDE.cutoffDrift β J R hR i (X q.1 q.2) else 0) = _
  congr 1
  have h := congrArg (VariationalCoefficients.coordinate i)
    (cutoffDrift_vector_sub β K J R hR (X q.1 q.2))
  simpa only [CutoffSDE.cutoffDrift,map_sub,map_sum,map_smul,
    VariationalCoefficients.coordinate_apply,smul_eq_mul] using h
end SphericalAging.HamiltonianPredictableForcing
