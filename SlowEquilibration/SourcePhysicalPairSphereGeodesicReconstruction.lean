-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereGeodesic
public import SlowEquilibration.SourcePhysicalPairLatitudeReconstruction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Every distinct near-overlap sphere point lies at a positive short
angle on a genuine great circle from the center. The angle cutoff is
chosen from the actual Hessian margin and covariant regularity constant. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set SphericalModel SphericalGaussianJet SphericalForm SphericalCriticalLatitude
open PureTensorJetBounds
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma source_sphere_eq_of_overlap_one {N:ℕ} (hN:0<N) (u w:Vector N)
    (hu:‖u‖^2=(N:ℝ)) (hw:‖w‖^2=(N:ℝ)) (hr:overlap u w=1) :u=w:=by
  have hN':(0:ℝ)<N:=Nat.cast_pos.mpr hN
  have hi:inner ℝ u w=(N:ℝ):=by
    have H:=(div_eq_iff hN'.ne').mp hr
    simpa only [overlap,one_mul] using H
  have hsq:‖u-w‖^2=0:=by rw [norm_sub_sq_real,hu,hw,hi];ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

theorem sourceSphereGeodesic_reconstruction {n:ℕ} (u w:Vector (n+1))
    (hu:‖u‖^2=(n+1:ℕ)) (hw:‖w‖^2=(n+1:ℕ)) (hr:overlap u w ∈ Ioo (0:ℝ) 1) :
    ∃ v:Vector (n+1),‖v‖^2=(n+1:ℕ) ∧ inner ℝ u v=0 ∧
      sourceSphereGeodesic u v (Real.arccos (overlap u w))=w:=by
  obtain ⟨x,hx⟩:=sourceLatitudeUnit_reconstruction u hu w hw hr
  let r:=overlap u w
  let e:=sourceLatitudeIsometry u hu
  let v:=Real.sqrt (n+1:ℕ) • e x
  have hv:‖v‖^2=(n+1:ℕ):=by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),e.norm_map,unit_norm,mul_one,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have huv:inner ℝ u v=0:=by
    dsimp [v,e]
    rw [real_inner_smul_right,real_inner_comm,sourceLatitudeIsometry_orthogonal,mul_zero]
  refine ⟨v,hv,huv,?_⟩
  change Real.cos (Real.arccos r) • u+Real.sin (Real.arccos r) • (Real.sqrt (n+1:ℕ) • e x)=w
  rw [Real.cos_arccos (by have hr0:0<r:=hr.1;linarith) hr.2.le,Real.sin_arccos,smul_smul,
    mul_comm (Real.sqrt (1-r^2)) (Real.sqrt (n+1:ℕ)),←Real.sqrt_mul (Nat.cast_nonneg (n+1))]
  exact hx

def sourceCriticalCollarAngle (κ C:ℝ):ℝ:=min (κ/(2*C)) (Real.pi/4)
def sourceCriticalCollarOverlapLoss (κ C:ℝ):ℝ:=(1-Real.cos (sourceCriticalCollarAngle κ C))/2

theorem sourceCriticalCollar_parameters {κ C:ℝ} (hκ:0<κ) (hC:0<C) :
    0<sourceCriticalCollarOverlapLoss κ C ∧ sourceCriticalCollarOverlapLoss κ C<1 ∧
      ∀ r:ℝ,1-sourceCriticalCollarOverlapLoss κ C ≤ r → r<1 →
        0<Real.arccos r ∧ Real.arccos r<κ/(2*C):=by
  let θ:=sourceCriticalCollarAngle κ C
  have hθ:0<θ:=lt_min (div_pos hκ (by positivity)) (div_pos Real.pi_pos (by norm_num))
  have hθκ:θ ≤ κ/(2*C):=min_le_left _ _
  have hθπ4:θ ≤ Real.pi/4:=min_le_right _ _
  have hθπ:θ ≤ Real.pi:=by linarith [Real.pi_pos]
  have hc:Real.cos θ<1:=by
    have H:=Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=θ) (by norm_num) hθπ hθ
    simpa only [Real.cos_zero] using H
  have hcp:0<Real.cos θ:=Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  refine ⟨by unfold sourceCriticalCollarOverlapLoss;change 0<(1-Real.cos θ)/2;linarith,
    by unfold sourceCriticalCollarOverlapLoss;change (1-Real.cos θ)/2<1;linarith,?_⟩
  intro r hr hr1
  have hcr:Real.cos θ<r:=by
    change 1-(1-Real.cos θ)/2 ≤ r at hr
    linarith
  have H:=Real.arccos_lt_arccos (Real.neg_one_le_cos θ) hcr hr1.le
  rw [Real.arccos_cos hθ.le hθπ] at H
  exact ⟨Real.arccos_pos.mpr hr1,H.trans_le hθκ⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
