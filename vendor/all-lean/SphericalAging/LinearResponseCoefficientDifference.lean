module

public import SphericalAging.PredictableProductNorm
public import SphericalAging.ConstructedFirstVariation

public section

/-! Exact same-source linear response differences and genuine Hessian
Lipschitz bounds along constructed nonlinear flow paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.LinearResponseCoefficientDifference
open HardSphereDynamics LocalSDE PredictableLinearCoefficient LinearResolvent
open StochasticLinearizationError
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem same_source_difference {Kb Ks : ℝ≥0} (D : BrownianDriver N P F)
    (ax ay : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sx sy : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A : PredictableStateL2 N F P) :
    LinearVariationalSDE.sourceClass D ay sy T A-LinearVariationalSDE.sourceClass D ax sx T A=
      sourceLinearMap D ax sx T
        (driftSource T (fun i => apply (ay i) (LinearVariationalSDE.sourceClass D ay sy T A)-
          apply (ax i) (LinearVariationalSDE.sourceClass D ay sy T A))+
        noiseSource D T (fun i j => apply (sy i j) (LinearVariationalSDE.sourceClass D ay sy T A)-
          apply (sx i j) (LinearVariationalSDE.sourceClass D ay sy T A))) := by
  let U := LinearVariationalSDE.sourceClass D ax sx T A
  let V := LinearVariationalSDE.sourceClass D ay sy T A
  apply (LinearVariationalSDE.exists_unique_picard_fixedPoint D ax sx T _).choose_spec.2
  have hu := LinearVariationalSDE.sourceClass_fixedPoint D ax sx T A
  have hv := LinearVariationalSDE.sourceClass_fixedPoint D ay sy T A
  change U=A+_+_ at hu
  change V=A+_+_ at hv
  have hd : LinearVariationalSDE.finiteDriftPicardMap ay T V-
      LinearVariationalSDE.finiteDriftPicardMap ax T V=
      driftSource T (fun i => apply (ay i) V-apply (ax i) V) := by
    simp only [LinearVariationalSDE.finiteDriftPicardMap,LinearVariationalSDE.driftCoefficientMap,
      driftSource,VolterraLinearity.driftOperator_apply,VolterraLinearity.stateInclusion_apply,
      map_sub,Finset.sum_sub_distrib]
  have hs : LinearVariationalSDE.finiteNoisePicardMap D sy T V-
      LinearVariationalSDE.finiteNoisePicardMap D sx T V=
      noiseSource D T (fun i j => apply (sy i j) V-apply (sx i j) V) := by
    simp only [LinearVariationalSDE.finiteNoisePicardMap,LinearVariationalSDE.stochasticCoefficientMap,
      noiseSource,VolterraLinearity.itoOperator_apply,VolterraLinearity.stateInclusion_apply,
      map_sub,Finset.sum_sub_distrib]
  rw [← hd,← hs,finiteDrift_sub,finiteNoise_sub]
  have he := congrArg₂ (fun v u : PredictableStateL2 N F P => v-u) hv hu
  exact he.trans (by abel)

theorem derivative_apply_difference_bound {K L : ℝ≥0} {g : State N → ℝ}
    (hg : ContDiff ℝ ∞ g) (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (X Z Y : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (hZa : StronglyAdapted F Z) (hZc : ∀ᵐ omega ∂P,Continuous (fun t => Z t omega))
    (T : ℝ≥0) (V : PredictableStateL2 N F P)
    (hY : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖((apply (VariationalCoefficients.derivativeRow Z hZa hZc hg hK T) V-
        apply (VariationalCoefficients.derivativeRow X hXa hXc hg hK T) V : PredictableProcessL2 F P) : TimeProcessL2 P) q‖≤
        (L : ℝ)*‖LinearSDETimeFourthMoment.stateTimeCut (fun t omega => Z t omega-X t omega) T q‖*
          ‖LinearSDETimeFourthMoment.stateTimeCut Y T q‖ := by
  filter_upwards [Lp.coeFn_sub (apply (VariationalCoefficients.derivativeRow Z hZa hZc hg hK T) V : TimeProcessL2 P)
    (apply (VariationalCoefficients.derivativeRow X hXa hXc hg hK T) V),
    LinearVariationalSDE.apply_eq_actual hY (VariationalCoefficients.derivativeRow Z hZa hZc hg hK T),
    LinearVariationalSDE.apply_eq_actual hY (VariationalCoefficients.derivativeRow X hXa hXc hg hK T)]
    with q hsub hz hx
  change ‖((apply (VariationalCoefficients.derivativeRow Z hZa hZc hg hK T) V : TimeProcessL2 P)-
    (apply (VariationalCoefficients.derivativeRow X hXa hXc hg hK T) V : TimeProcessL2 P)) q‖≤_
  rw [hsub,Pi.sub_apply,hz,hx]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,VariationalCoefficients.derivativeRow,
      LinearSDETimeFourthMoment.stateTimeCut,ht,ite_true]
    rw [← ContinuousLinearMap.sub_apply]
    have hd : ‖fderiv ℝ g (Z q.1 q.2)-fderiv ℝ g (X q.1 q.2)‖≤(L : ℝ)*‖Z q.1 q.2-X q.1 q.2‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul (Z q.1 q.2) (X q.1 q.2)
    exact ((fderiv ℝ g (Z q.1 q.2)-fderiv ℝ g (X q.1 q.2)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,LinearSDETimeFourthMoment.stateTimeCut,
      ht,ite_false,sub_self,norm_zero,mul_zero,le_refl]

end SphericalAging.LinearResponseCoefficientDifference
