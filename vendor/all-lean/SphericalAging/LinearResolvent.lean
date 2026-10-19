module

public import SphericalAging.VolterraLinearity

public section

/-! The constructed bounded predictable linear-SDE solution map is an
actual continuous linear resolvent on its predictable source space. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.LinearResolvent
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open PredictableLinearCoefficient VolterraLinearity LinearVariationalSDE
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

 theorem finiteDrift_sub (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    LinearVariationalSDE.finiteDriftPicardMap a T (U-V) =
      LinearVariationalSDE.finiteDriftPicardMap a T U-LinearVariationalSDE.finiteDriftPicardMap a T V := by
  classical
  unfold LinearVariationalSDE.finiteDriftPicardMap LinearVariationalSDE.driftCoefficientMap
  simp only [apply_sub,driftVolterra_sub,scalarToStatePredictable_sub,Finset.sum_sub_distrib]

 theorem finiteNoise_sub (D : BrownianDriver N P F)
    (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (U V : PredictableStateL2 N F P) :
    LinearVariationalSDE.finiteNoisePicardMap D s T (U-V) =
      LinearVariationalSDE.finiteNoisePicardMap D s T U-LinearVariationalSDE.finiteNoisePicardMap D s T V := by
  classical
  unfold LinearVariationalSDE.finiteNoisePicardMap LinearVariationalSDE.stochasticCoefficientMap
  simp only [apply_sub,itoVolterra_sub,Finset.sum_sub_distrib,scalarToStatePredictable_sub]

 theorem sourceClass_sub (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A B : PredictableStateL2 N F P) :
    sourceClass D a s T (A-B) = sourceClass D a s T A-sourceClass D a s T B := by
  have hA := sourceClass_fixedPoint D a s T A
  have hB := sourceClass_fixedPoint D a s T B
  apply Eq.symm
  apply (exists_unique_picard_fixedPoint D a s T (A-B)).choose_spec.2
  rw [finiteDrift_sub,finiteNoise_sub]
  have h := congrArg₂ (fun u v : PredictableStateL2 N F P => u-v) hA hB
  exact h.trans (by abel)

@[expose]  def sourceLinearMap (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) : PredictableStateL2 N F P →L[ℝ] PredictableStateL2 N F P :=
  ({toFun := sourceClass D a s T
    map_zero' := sourceClass_zero D a s T
    map_add' := fun A B => by
      have h := sourceClass_sub D a s T (A+B) B
      rw [add_sub_cancel_right] at h
      exact (eq_sub_iff_add_eq.mp h).symm} : PredictableStateL2 N F P →+ PredictableStateL2 N F P).toRealLinearMap
    (by
      change Continuous (sourceClass D a s T)
      obtain ⟨K,hK⟩ := sourceClass_lipschitz D a s T
      exact hK.continuous)

 @[simp] theorem sourceLinearMap_apply (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (A : PredictableStateL2 N F P) : sourceLinearMap D a s T A = sourceClass D a s T A := rfl

/-- The actual bounded-predictable linear variational solution class as a
continuous linear function of its initial perturbation. -/
@[expose]  def initialResponse (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) : State N →L[ℝ] PredictableStateL2 N F P :=
  (sourceLinearMap D a s T).comp (initialOperator T)

 @[simp] theorem initialResponse_apply (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) (v : State N) : initialResponse D a s T v = sourceClass D a s T (initialClass v T) := rfl
end SphericalAging.LinearResolvent
