module

public import SphericalAging.InhomogeneousLinearSDE
public import SphericalAging.StaticSDEOperators
public import SphericalAging.LinearSDELocalization

public section

/-! Pathwise uniqueness for actual bounded predictable affine matrix
SDEs. The real difference equation is derived, then genuine localized
fourth moments with zero initial state force the difference to vanish.
No predictable state class or moment is a uniqueness premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.LinearStrongUniqueness
open HardSphereDynamics LocalSDE PredictableLinearCoefficient PredictableDriftTime VectorIto StaticSDEOperators
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks B : ℝ≥0}

 theorem affine_difference_strongSolution
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D v0 X T)
    (hY : InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D v0 Y T) :
    LinearVariationalSDE.IsStrongSolutionOn a sigma D 0 (fun t omega => X t omega-Y t omega) T := by
  obtain ⟨AX,UX,hAX,hUX,hXe⟩ := InhomogeneousLinearSDE.strongSolution_class_equation hX
  obtain ⟨AY,UY,hAY,hUY,hYe⟩ := InhomogeneousLinearSDE.strongSolution_class_equation hY
  let A := fun i => AX i-AY i
  let U := fun i j => UX i j-UY i j
  have hA : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (a i).value (s,omega) (X s omega-Y s omega)) T := by
    intro i
    filter_upwards [hAX i,hAY i,Lp.coeFn_sub (AX i : TimeProcessL2 P) (AY i)] with q hX hY hsub
    simp only [A,Submodule.coe_sub]
    rw [hsub,Pi.sub_apply,hX,hY]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,map_sub]
      ring
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_self]
  have hU : ∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma i j).value (s,omega) (X s omega-Y s omega)) T := by
    intro i j
    filter_upwards [hUX i j,hUY i j,Lp.coeFn_sub (UX i j : TimeProcessL2 P) (UY i j)] with q hX hY hsub
    simp only [U,Submodule.coe_sub]
    rw [hsub,Pi.sub_apply,hX,hY]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T <;>
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,map_sub,sub_self]
  refine ⟨(fun t => (hX.1 t).sub (hY.1 t)),?_,A,U,hA,hU,?_⟩
  · filter_upwards [hX.2.1,hY.2.1] with omega hX hY
    exact hX.sub hY
  · intro t ht i
    have hn : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) =
        vectorProcessLp D (UX i) t-vectorProcessLp D (UY i) t := by
      rw [CutoffSphere.driverItoMap_eq_vectorIto]
      exact vectorProcessLp_sub D _ _ t
    have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
      (fun s omega => (a i).value (s,omega) (X s omega-Y s omega)) T (A i) (hA i)
    filter_upwards [hXe t ht i,hYe t ht i,driftVersion_sub_ae (AX i) (AY i) T,hd,
      vectorProcessLp_ae_eq D (UX i) t,vectorProcessLp_ae_eq D (UY i) t,
      Lp.coeFn_sub (vectorProcessLp D (UX i) t) (vectorProcessLp D (UY i) t)]
      with omega hX hY hsub hd hnX hnY hnsub
    change (X t omega-Y t omega) i = _
    simp only [PiLp.sub_apply,PiLp.zero_apply,zero_add]
    rw [← hd t ht,hsub t,hn,hnsub,Pi.sub_apply,hnX,hnY,hX,hY]
    ring

/-- A genuine zero-initial bounded predictable linear SDE is zero,
without assuming any moment or predictable state-class property. -/
 theorem linear_zero_of_strongSolution
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : LinearVariationalSDE.IsStrongSolutionOn a sigma D 0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → X t omega=0 := by
  have hpoint (t : ℝ≥0) (ht : t ≤ T) : X t =ᵐ[P] (fun _ => (0 : State N)) := by
    have h4 := LinearSDELocalization.linear_solution_fourthMoment hX hnull t ht
    have hi : Integrable (fun omega => ‖X t omega‖^4) P := h4.1.integrable_norm_pow (by norm_num)
    have hint : (∫ omega,‖X t omega‖^4 ∂P)=0 := by
      apply le_antisymm
      · simpa only [norm_zero,zero_pow (by norm_num : 4 ≠ 0),mul_zero,zero_mul] using h4.2
      · exact integral_nonneg (fun _ => by positivity)
    have hz := (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hi).mp hint
    filter_upwards [hz] with omega hzero
    change ‖X t omega‖ ^ 4 = 0 at hzero
    have hn : ‖X t omega‖ = 0 := eq_zero_of_pow_eq_zero hzero
    exact norm_eq_zero.mp hn
  exact StrongUniqueness.continuous_state_processes_ae_eq_of_fixedTime_on hX.2.1
    (.of_forall (fun _ => continuous_const)) hpoint

/-- Actual affine strong pathwise uniqueness on any finite horizon,
proved from the true difference SDE and its localized zero moment. -/
 theorem affine_pathwise_uniqueness
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D v0 X T)
    (hY : InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D v0 Y T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → X t omega=Y t omega := by
  exact (linear_zero_of_strongSolution (affine_difference_strongSolution hX hY) hnull).mono
    (fun omega h t ht => sub_eq_zero.mp (h t ht))
end SphericalAging.LinearStrongUniqueness
