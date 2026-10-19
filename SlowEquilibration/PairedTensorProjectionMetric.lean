-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairedTensorBlockFeatures
public import SlowEquilibration.GaussianSharpAbsoluteMaximum

/-! Actual all-order paired projection features on the unit sphere, and
their genuine square-root coefficient increment metric. -/

@[expose] public section
namespace SlowEquilibration.PairedTensorProjectionFeatures
noncomputable section
open MeasureTheory SphericalAging.FiniteModel SphericalProjectionMatrixFeature
open PureTensorJetBounds
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def physicalAxis {N : ℕ} (u : UnitSphere N) : Vector N := Real.sqrt N • (u : Vector N)

theorem physicalAxis_norm_sq {N : ℕ} (u : UnitSphere N) :
    ‖physicalAxis u‖^2=(N : ℝ) := by
  simp only [physicalAxis,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    unit_norm,mul_one,Real.sq_sqrt (Nat.cast_nonneg N)]

def unitProjectionFeature {N : ℕ} (u : UnitSphere N) : EuclideanSpace ℝ (Fin N × Fin N) :=
  (Real.sqrt ((N : ℝ)-1))⁻¹ • projectionMatrixFeature (physicalAxis u)

theorem unitProjectionFeature_norm {N : ℕ} (hN : 2≤N) (u : UnitSphere N) :
    ‖unitProjectionFeature u‖=1 := by
  have hNr : (0 : ℝ)<(N : ℝ)-1 := by
    have h : (2 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hs : 0<Real.sqrt ((N : ℝ)-1) := Real.sqrt_pos.mpr hNr
  have hn : ‖projectionMatrixFeature (physicalAxis u)‖=Real.sqrt ((N : ℝ)-1) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [projectionMatrixFeature_norm_sq (by omega) _ (physicalAxis_norm_sq u),Real.sq_sqrt hNr.le]
  simp only [unitProjectionFeature,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,hn]
  exact inv_mul_cancel₀ hs.ne'

/-- Matrix normalization retains a dimension-independent actual chord cost. -/
theorem unitProjectionFeature_increment_le {N : ℕ} (hN : 2≤N) (u v : UnitSphere N) :
    ‖unitProjectionFeature u-unitProjectionFeature v‖ ≤ 2*‖(u : Vector N)-(v : Vector N)‖ := by
  have hNr : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hsN : Real.sqrt (N : ℝ)≠0 := (Real.sqrt_pos.mpr hNr).ne'
  have hs : 1≤Real.sqrt ((N : ℝ)-1) := by
    have h : (2 : ℝ)≤N := by exact_mod_cast hN
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    norm_num
    linarith
  have hinv : (Real.sqrt ((N : ℝ)-1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have hi := projectionMatrixFeature_increment_le (by omega) (physicalAxis u) (physicalAxis v)
    (physicalAxis_norm_sq u) (physicalAxis_norm_sq v)
  have hd : ‖physicalAxis u-physicalAxis v‖=Real.sqrt N*‖(u : Vector N)-(v : Vector N)‖ := by
    simp only [physicalAxis,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hd] at hi
  have hi' : ‖projectionMatrixFeature (physicalAxis u)-projectionMatrixFeature (physicalAxis v)‖≤
      2*‖(u : Vector N)-(v : Vector N)‖ := by
    simpa only [←mul_assoc,div_mul_cancel₀ _ hsN] using hi
  simp only [unitProjectionFeature,←smul_sub,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _≤1*‖projectionMatrixFeature (physicalAxis u)-projectionMatrixFeature (physicalAxis v)‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _≤_ := by simpa only [one_mul] using hi'

def unitPairedFeature (N q j : ℕ) (u : UnitSphere N) :
    EuclideanSpace ℝ (TensorIndex N (q+j+j)) :=
  pairedBlockFeature (fun _ : Fin q => (u : Vector N))
    (fun _ : Fin j => unitProjectionFeature u)

theorem unitPairedFeature_norm {N : ℕ} (hN : 2≤N) (q j : ℕ) (u : UnitSphere N) :
    ‖unitPairedFeature N q j u‖=1 := by
  have h := pairedBlockFeature_norm_sq_of_unit (fun _ : Fin q => (u : Vector N))
    (fun _ : Fin j => unitProjectionFeature u) (fun _ => unit_norm u)
    (fun _ => unitProjectionFeature_norm hN u)
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp (by simpa only [unitPairedFeature,one_pow] using h)

theorem unitPairedFeature_increment_le {N : ℕ} (hN : 2≤N) (q j : ℕ) (u v : UnitSphere N) :
    ‖unitPairedFeature N q j u-unitPairedFeature N q j v‖ ≤
      Real.sqrt ((q : ℝ)+4*j)*‖(u : Vector N)-(v : Vector N)‖ := by
  have hi := pairedBlockFeature_increment_sq_le (fun _ : Fin q => (u : Vector N))
    (fun _ : Fin q => (v : Vector N)) (fun _ : Fin j => unitProjectionFeature u)
    (fun _ : Fin j => unitProjectionFeature v) (fun _ => unit_norm u) (fun _ => unit_norm v)
    (fun _ => unitProjectionFeature_norm hN u) (fun _ => unitProjectionFeature_norm hN v)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  have hb : ‖unitProjectionFeature u-unitProjectionFeature v‖^2 ≤
      4*‖(u : Vector N)-(v : Vector N)‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (unitProjectionFeature_increment_le hN u v) 2
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hjb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg j)
  change ‖unitPairedFeature N q j u-unitPairedFeature N q j v‖^2≤_ at hi
  nlinarith

theorem unitPairedFeature_continuous (N q j : ℕ) : Continuous (unitPairedFeature N q j) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro I
  dsimp only [unitPairedFeature,pairedBlockFeature,unitProjectionFeature,
    projectionMatrixFeature,identityFeature,outerFeature,physicalAxis]
  fun_prop

/-- This feature is the literal original projected tensor, at physical radius. -/
theorem pairedTensorFeature_physicalAxis_eq {N q j : ℕ} (hN : 2≤N) (u : UnitSphere N) :
    pairedTensorFeature N q j (physicalAxis u)=
      ((Real.sqrt N)^q*(Real.sqrt ((N : ℝ)-1))^j) • unitPairedFeature N q j u := by
  have hNr : (0 : ℝ)<(N : ℝ)-1 := by
    have h : (2 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hs : Real.sqrt ((N : ℝ)-1)≠0 := (Real.sqrt_pos.mpr hNr).ne'
  ext I
  simp only [pairedTensorFeature,physicalAxis,PiLp.smul_apply,smul_eq_mul,
    unitPairedFeature,pairedBlockFeature,unitProjectionFeature,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hc : (Real.sqrt ((N : ℝ)-1))^j*((Real.sqrt ((N : ℝ)-1))⁻¹)^j=1 := by
    rw [←mul_pow,mul_inv_cancel₀ hs,one_pow]
  calc
    _=((Real.sqrt N)^q*(∏ k : Fin q,(u : Vector N) (I (freeSlot q j k)))*
        (∏ k : Fin j,projectionMatrixFeature (physicalAxis u)
          (I (leftPairSlot q j k),I (rightPairSlot q j k))))*1 := by simp only [physicalAxis,mul_one]
    _=_ := by
      conv_lhs => arg 2; rw [←hc]
      dsimp only [physicalAxis]
      ring

end
end SlowEquilibration.PairedTensorProjectionFeatures
