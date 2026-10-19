-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereGeodesicJets
public import SlowEquilibration.SourcePhysicalPairSphereGeodesicReconstruction
public import SlowEquilibration.SourcePairScalarCriticalCollar

/-! Actual high-overlap critical-point exclusion. The literal intrinsic
Hessian margin and covariant D_N bound imply a short great-circle collar
without another critical point. Combining this with the all-w band
height excludes all other high critical points at positive overlap. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Set SphericalModel SphericalGaussianJet SphericalForm
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_actual_sphere_critical_collar_exclusion {n P:ℕ} (c:Degree P→ℝ) (J:Disorder (n+1) P)
    {κ C:ℝ} (hκ:0<κ) (hC:0<C) (u w:Vector (n+1))
    (hu:‖u‖^2=(n+1:ℕ)) (hw:‖w‖^2=(n+1:ℕ)) (huw:u≠w)
    (huc:surfaceGradient (field c J) u=0) (hwc:surfaceGradient (field c J) w=0)
    (hMargin:sourceHessianMargin c κ J u) (hReg:sourceSphereRegularity c J ≤ C) :
    overlap u w<1-sourceCriticalCollarOverlapLoss κ C:=by
  by_contra hbad
  have hrLower:1-sourceCriticalCollarOverlapLoss κ C ≤ overlap u w:=le_of_not_gt hbad
  obtain ⟨hη,hηOne,hAngle⟩:=sourceCriticalCollar_parameters hκ hC
  have hrPos:0<overlap u w:=by linarith
  have hrLe:overlap u w ≤ 1:=(overlap_mem_Icc_of_norm_sq (by omega) u w hu hw).2
  have hrNe:overlap u w≠1:=fun he=>huw (source_sphere_eq_of_overlap_one (by omega) u w hu hw he)
  have hrLt:overlap u w<1:=lt_of_le_of_ne hrLe hrNe
  obtain ⟨v,hv,huv,hEnd⟩:=sourceSphereGeodesic_reconstruction u w hu hw ⟨hrPos,hrLt⟩
  obtain ⟨hθ,hθsmall⟩:=hAngle _ hrLower hrLt
  have hs0:sourceSphereGeodesicSlope c J u v 0=0:=by
    unfold sourceSphereGeodesicSlope
    rw [sourceSphereGeodesicVelocity_zero,sourceSphereGeodesic_zero,huc,inner_zero_right]
  have hh0:sourceSphereGeodesicCurvature c J u v 0 ≤ -κ*(n+1:ℕ):=by
    unfold sourceSphereGeodesicCurvature
    rw [sourceSphereGeodesicVelocity_zero,sourceSphereGeodesic_zero]
    have H:=hMargin v
    rwa [source_tangentProjection_fixed u v huv,hv] at H
  have H:=source_pair_scalar_critical_collar ((n+1:ℕ):ℝ) C κ (Real.arccos (overlap u w))
    (by positivity) hC hκ hθ hθsmall
    (sourceSphereGeodesicSlope c J u v) (sourceSphereGeodesicCurvature c J u v) (sourceSphereGeodesicCubic c J u v)
    hs0 hh0
    (fun t _=>sourceSphereGeodesicSlope_hasDerivAt (by omega) c J u v hu hv huv t)
    (fun t _=>sourceSphereGeodesicCurvature_hasDerivAt (by omega) c J u v hu hv huv t)
    (fun t _=>sourceSphereGeodesicCubic_abs_le (by omega) c J u v hu hv huv hReg t)
  have hsEnd:sourceSphereGeodesicSlope c J u v (Real.arccos (overlap u w))=0:=by
    unfold sourceSphereGeodesicSlope
    rw [hEnd,hwc,inner_zero_right]
  rw [hsEnd] at H
  exact (lt_irrefl (0:ℝ)) H

theorem sourceSelectionEvent_excludes_high_critical_points {n P:ℕ} (c:Degree P→ℝ) (J:Disorder (n+1) P)
    {κ C ε η E G δ:ℝ} (hκ:0<κ) (hC:0<C) (hη:η ≤ sourceCriticalCollarOverlapLoss κ C)
    (hδ:δ<G/2) (u w:Vector (n+1))
    (hu:‖u‖^2=(n+1:ℕ)) (hw:‖w‖^2=(n+1:ℕ)) (huw:u≠w)
    (huc:surfaceGradient (field c J) u=0) (hwc:surfaceGradient (field c J) w=0)
    (hSel:sourceSelectionEvent c κ C ε η E G J u)
    (hHigh:(n+1:ℕ)*(E-δ) ≤ field c J w) :overlap u w<ε:=by
  have hcollar:=source_actual_sphere_critical_collar_exclusion c J hκ hC u w hu hw huw huc hwc hSel.1 hSel.2.1
  have hr:overlap u w ≤ 1-η:=hcollar.le.trans (by linarith)
  by_contra hbad
  have hBand:=hSel.2.2 w hw (le_of_not_gt hbad) hr
  have hN:(0:ℝ)<(n+1:ℕ):=by positivity
  have hgap:=mul_pos hN (sub_pos.mpr hδ)
  nlinarith

end
end SlowEquilibration.PairConditionalDeterminantMoments
