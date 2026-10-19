module

public import SphericalAging.LinearResolventUniformBound
public import SphericalAging.LinearResponseCoefficientDifference

public section
/-! Actual bounded linear-SDE source responses vary continuously when their
literal coefficient applications and source data vary continuously. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.LinearResponseSpatialContinuity
open HardSphereDynamics LocalSDE PredictableLinearCoefficient LinearResolvent
open StochasticLinearizationError VolterraLinearity PredictableDriftTime PredictableItoTime
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

theorem varying_source_difference (D : BrownianDriver N P F)
    (ax ay : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sx sy : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A B : PredictableStateL2 N F P) :
    LinearVariationalSDE.sourceClass D ay sy T B-LinearVariationalSDE.sourceClass D ax sx T A=
      sourceLinearMap D ay sy T (B-A+
        driftSource T (fun i => apply (ay i) (LinearVariationalSDE.sourceClass D ax sx T A)-
          apply (ax i) (LinearVariationalSDE.sourceClass D ax sx T A))+
        noiseSource D T (fun i j => apply (sy i j) (LinearVariationalSDE.sourceClass D ax sx T A)-
          apply (sx i j) (LinearVariationalSDE.sourceClass D ax sx T A))) := by
  let U := LinearVariationalSDE.sourceClass D ax sx T A
  let V := LinearVariationalSDE.sourceClass D ay sy T B
  apply (LinearVariationalSDE.exists_unique_picard_fixedPoint D ay sy T _).choose_spec.2
  have hu := LinearVariationalSDE.sourceClass_fixedPoint D ax sx T A
  have hv := LinearVariationalSDE.sourceClass_fixedPoint D ay sy T B
  change U=A+_+_ at hu
  change V=B+_+_ at hv
  have hd : driftSource T (fun i => apply (ay i) U-apply (ax i) U)=
      LinearVariationalSDE.finiteDriftPicardMap ay T U-LinearVariationalSDE.finiteDriftPicardMap ax T U := by
    simp only [driftSource,LinearVariationalSDE.finiteDriftPicardMap,LinearVariationalSDE.driftCoefficientMap,
      map_sub,Finset.sum_sub_distrib,driftOperator_apply,stateInclusion_apply]
  have hn : noiseSource D T (fun i j => apply (sy i j) U-apply (sx i j) U)=
      LinearVariationalSDE.finiteNoisePicardMap D sy T U-LinearVariationalSDE.finiteNoisePicardMap D sx T U := by
    simp only [noiseSource,LinearVariationalSDE.finiteNoisePicardMap,LinearVariationalSDE.stochasticCoefficientMap,
      map_sub,Finset.sum_sub_distrib,itoOperator_apply,stateInclusion_apply]
  rw [hd,hn,finiteDrift_sub,finiteNoise_sub]
  exact (congrArg₂ (fun v u : PredictableStateL2 N F P => v-u) hv hu).trans (by abel)

theorem sourceClass_continuous (D : BrownianDriver N P F) (T : ℝ≥0)
    (a : State N → Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (s : State N → Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (A : State N → PredictableStateL2 N F P)
    (ha : ∀ i Q,Continuous (fun x => apply (a x i) Q))
    (hs : ∀ i j Q,Continuous (fun x => apply (s x i j) Q)) (hA : Continuous A) :
    Continuous (fun x => LinearVariationalSDE.sourceClass D (a x) (s x) T (A x)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := LinearResolventUniformBound.sourceLinearMap_uniform_norm D Kb Ks T
  rw [continuous_iff_continuousAt]
  intro x
  let Q := LinearVariationalSDE.sourceClass D (a x) (s x) T (A x)
  let E := fun y => A y-A x+driftSource T (fun i => apply (a y i) Q-apply (a x i) Q)+
    noiseSource D T (fun i j => apply (s y i j) Q-apply (s x i j) Q)
  have hd : Continuous (fun y => driftSource T (fun i => apply (a y i) Q-apply (a x i) Q)) := by
    apply continuous_finset_sum
    intro i _
    exact (stateInclusion i).continuous.comp ((driftOperator T).continuous.comp ((ha i Q).sub continuous_const))
  have hn : Continuous (fun y => noiseSource D T (fun i j => apply (s y i j) Q-apply (s x i j) Q)) := by
    apply continuous_finset_sum
    intro i _
    apply (stateInclusion i).continuous.comp
    apply continuous_finset_sum
    intro j _
    exact (itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T).continuous.comp
      ((hs i j Q).sub continuous_const)
  have he : Continuous E := ((hA.sub continuous_const).add hd).add hn
  have hex : E x=0 := by simp only [E,sub_self,driftSource,noiseSource,map_zero,Finset.sum_const_zero,zero_add]
  have hnorm (y : State N) : ‖LinearVariationalSDE.sourceClass D (a y) (s y) T (A y)-Q‖≤C*‖E y‖ := by
    rw [varying_source_difference]
    exact ((sourceLinearMap D (a y) (s y) T).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound (a y) (s y)) (norm_nonneg _))
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have ht := (he.norm.tendsto x).const_mul C
  rw [hex,norm_zero,mul_zero] at ht
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm ht
end SphericalAging.LinearResponseSpatialContinuity
