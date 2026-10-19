module

public import SphericalAging.StochasticFlowDerivative

public section

/-! Genuine predictable quadratic Hessian sources along actual adapted
continuous paths. Their L² existence follows from actual L⁴ variations. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.HessianQuadraticSource
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open LinearSDETimeFourthMoment StochasticTaylorRemainder
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def hessianField (g : State N → ℝ) (X Y Z : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (omega : Ω) : ℝ := fderiv ℝ (fderiv ℝ g) (X t omega) (Y t omega) (Z t omega)

lemma hessianField_adapted (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (X Y Z : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y) (hZa : StronglyAdapted F Z) :
    StronglyAdapted F (hessianField g X Y Z) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  intro t
  exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    ((isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((hc.comp_stronglyMeasurable (hXa t)).prodMk (hYa t))).prodMk (hZa t))

lemma hessianField_continuous (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (X Y Z : ℝ≥0 → Ω → State N)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂P,Continuous (fun t => Y t omega))
    (hZc : ∀ᵐ omega ∂P,Continuous (fun t => Z t omega)) :
    ∀ᵐ omega ∂P,Continuous (fun t => hessianField g X Y Z t omega) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  filter_upwards [hXc,hYc,hZc] with omega hx hy hz
  exact ((hc.comp hx).clm_apply hy).clm_apply hz

lemma hessianField_bound {g : State N → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ g)) (X Y Z : ℝ≥0 → Ω → State N) (t : ℝ≥0) (omega : Ω) :
    ‖hessianField g X Y Z t omega‖≤(L : ℝ)*‖Y t omega‖*‖Z t omega‖ := by
  exact ((fderiv ℝ (fderiv ℝ g) (X t omega) (Y t omega)).le_opNorm (Z t omega)).trans
    (mul_le_mul_of_nonneg_right
      ((fderiv ℝ (fderiv ℝ g) (X t omega)).le_of_opNorm_le
        (norm_fderiv_le_of_lipschitz ℝ hL) (Y t omega)) (norm_nonneg _))

section Source
variable (g : State N → ℝ) (hg : ContDiff ℝ ∞ g) {L : ℝ≥0}
  (hL : LipschitzWith L (fderiv ℝ g)) (X Y Z : ℝ≥0 → Ω → State N)
  (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y) (hZa : StronglyAdapted F Z)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (hYc : ∀ᵐ omega ∂P,Continuous (fun t => Y t omega))
  (hZc : ∀ᵐ omega ∂P,Continuous (fun t => Z t omega)) (T : ℝ≥0)
  (hY4 : MemLp (stateTimeCut Y T) 4 (nonnegativeLebesgueMeasure.prod P))
  (hZ4 : MemLp (stateTimeCut Z T) 4 (nonnegativeLebesgueMeasure.prod P))

include hg hXa hYa hZa hXc hYc hZc in
lemma hessianCut_predictable :
    AEStronglyMeasurable[F.predictable]
      (FourPapersCommon.continuousAdaptedTimeCut (hessianField g X Y Z) T)
      (nonnegativeLebesgueMeasure.prod P) :=
  FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _
    (hessianField_adapted g hg X Y Z hXa hYa hZa)
    (hessianField_continuous g hg X Y Z hXc hYc hZc) T

include hg hL hXa hYa hZa hXc hYc hZc hY4 hZ4 in
lemma hessianCut_memLp :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (hessianField g X Y Z) T)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
    change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹+((4 : ℝ≥0) : ℝ≥0∞)⁻¹=((2 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0)≠0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0)≠0),← ENNReal.coe_add]
    exact_mod_cast (by norm_num : (4 : ℝ≥0)⁻¹+(4 : ℝ≥0)⁻¹=(2 : ℝ≥0)⁻¹)⟩
  have hp : MemLp (fun q => ‖stateTimeCut Y T q‖*‖stateTimeCut Z T q‖) 2
      (nonnegativeLebesgueMeasure.prod P) := hY4.norm.fun_mul hZ4.norm
  apply hp.of_le_mul (c := (L : ℝ))
    ((hessianCut_predictable g hg X Y Z hXa hYa hZa hXc hYc hZc T).mono (predictable_le_prod F))
  filter_upwards [] with q
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_true,
      Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg _)]
    simpa only [mul_assoc,Real.norm_eq_abs] using hessianField_bound hL X Y Z q.1 q.2
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_false,
      norm_zero,mul_zero,zero_mul,le_refl]

/-- Actual predictable Hessian source class for the second variational SDE. -/
@[expose] def source : PredictableProcessL2 F P :=
  ⟨(hessianCut_memLp g hg hL X Y Z hXa hYa hZa hXc hYc hZc T hY4 hZ4).toLp _,
    (hessianCut_predictable g hg X Y Z hXa hYa hZa hXc hYc hZc T).congr
      (hessianCut_memLp g hg hL X Y Z hXa hYa hZa hXc hYc hZc T hY4 hZ4).coeFn_toLp.symm⟩

lemma source_coe : (source g hg hL X Y Z hXa hYa hZa hXc hYc hZc T hY4 hZ4 : TimeProcessL2 P)
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (hessianField g X Y Z) T :=
  (hessianCut_memLp g hg hL X Y Z hXa hYa hZa hXc hYc hZc T hY4 hZ4).coeFn_toLp

end Source
end SphericalAging.HessianQuadraticSource
