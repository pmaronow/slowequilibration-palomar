module

public import SphericalAging.LinearVariationalSDE
public import Mathlib.Topology.Instances.RealVectorSpace

public section

set_option backward.privateInPublic true

/-! The actual full-filtration time-dependent drift and Itô operators are
continuous real linear maps, proved from their genuine additive identities
and norm estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.VolterraLinearity
open HardSphereDynamics PredictableItoTime PredictableDriftTime LocalSDE
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

private def additiveOfSub {E G : Type*} [AddCommGroup E] [AddCommGroup G]
    (f : E → G) (hf : ∀ x y, f (x-y) = f x-f y) : E →+ G where
  toFun := f
  map_zero' := by simpa only [sub_self] using hf 0 0
  map_add' x y := by
    have h := hf (x+y) y
    rw [add_sub_cancel_right] at h
    exact (eq_sub_iff_add_eq.mp h).symm

@[simp] private theorem additiveOfSub_apply {E G : Type*} [AddCommGroup E] [AddCommGroup G]
    (f : E → G) (hf : ∀ x y, f (x-y) = f x-f y) (x : E) :
    additiveOfSub f hf x = f x := rfl

@[expose] def driftOperator (T : ℝ≥0) : PredictableProcessL2 F P →L[ℝ] PredictableProcessL2 F P :=
  (additiveOfSub (driftVolterra T) (driftVolterra_sub T)).toRealLinearMap
    (LipschitzWith.of_dist_le_mul (K := T) (fun U V => by
      simpa only [dist_eq_norm,additiveOfSub_apply] using norm_driftVolterra_sub_le T U V)).continuous

@[simp] theorem driftOperator_apply (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    driftOperator T U = driftVolterra T U := rfl

@[expose] def itoOperator {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P) (T : ℝ≥0) :
    PredictableProcessL2 F P →L[ℝ] PredictableProcessL2 F P :=
  (additiveOfSub (itoVolterra hB hsm hfiltered T) (itoVolterra_sub hB hsm hfiltered T)).toRealLinearMap
    (LipschitzWith.of_dist_le_mul (K := NNReal.sqrt T) (fun U V => by
      simpa only [dist_eq_norm,additiveOfSub_apply,Real.coe_sqrt] using norm_itoVolterra_sub_le hB hsm hfiltered T U V)).continuous

@[simp] theorem itoOperator_apply {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P) (T : ℝ≥0)
    (U : PredictableProcessL2 F P) : itoOperator hB hsm hfiltered T U = itoVolterra hB hsm hfiltered T U := rfl

theorem driftVolterra_smul (T : ℝ≥0) (c : ℝ) (U : PredictableProcessL2 F P) :
    driftVolterra T (c • U) = c • driftVolterra T U := (driftOperator T).map_smul c U

theorem driftVolterra_add (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    driftVolterra T (U+V) = driftVolterra T U+driftVolterra T V := (driftOperator T).map_add U V

theorem itoVolterra_smul {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (T : ℝ≥0) (c : ℝ) (U : PredictableProcessL2 F P) :
    itoVolterra hB hsm hfiltered T (c • U) = c • itoVolterra hB hsm hfiltered T U :=
  (itoOperator hB hsm hfiltered T).map_smul c U

theorem itoVolterra_add {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hfiltered : IsFilteredPreBrownian B F P)
    (T : ℝ≥0) (U V : PredictableProcessL2 F P) :
    itoVolterra hB hsm hfiltered T (U+V) = itoVolterra hB hsm hfiltered T U+itoVolterra hB hsm hfiltered T V :=
  (itoOperator hB hsm hfiltered T).map_add U V

@[expose] def stateInclusion (i : Fin N) : PredictableProcessL2 F P →L[ℝ] PredictableStateL2 N F P :=
  (additiveOfSub (scalarToStatePredictable i) (scalarToStatePredictable_sub i)).toRealLinearMap
    (LipschitzWith.of_dist_le_mul (K := 1) (fun U V => by
      simpa only [dist_eq_norm,additiveOfSub_apply,NNReal.coe_one,one_mul,
        ← scalarToStatePredictable_sub] using norm_scalarToStatePredictable_le i (U-V))).continuous

@[simp] theorem stateInclusion_apply (i : Fin N) (U : PredictableProcessL2 F P) :
    stateInclusion i U = scalarToStatePredictable i U := rfl

theorem scalarToStatePredictable_smul (i : Fin N) (c : ℝ) (U : PredictableProcessL2 F P) :
    scalarToStatePredictable i (c • U) = c • scalarToStatePredictable i U :=
  (stateInclusion i).map_smul c U

@[expose] def initialOperator (T : ℝ≥0) : State N →L[ℝ] PredictableStateL2 N F P :=
  (additiveOfSub (fun x : State N => initialClass (F := F) (P := P) x T)
    (PicardDependence.initialClass_sub T)).toRealLinearMap (by
      change Continuous (fun x : State N => initialClass (F := F) (P := P) x T)
      exact (PicardDependence.initialClass_lipschitz (N := N) (F := F) (P := P) T).continuous)

@[simp] theorem initialOperator_apply (T : ℝ≥0) (x : State N) :
    initialOperator (F := F) (P := P) T x = initialClass (F := F) (P := P) x T := rfl

theorem initialClass_smul (T : ℝ≥0) (c : ℝ) (x : State N) :
    initialClass (F := F) (P := P) (c • x) T = c • initialClass x T :=
  (initialOperator T).map_smul c x

end SphericalAging.VolterraLinearity
