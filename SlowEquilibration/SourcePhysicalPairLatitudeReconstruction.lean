-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairLatitudeGeometry
public import SlowEquilibration.SourcePhysicalPairSelectionEvent
public import SlowEquilibration.SphericalCriticalLatitudeAuxiliaryLaw
public import SlowEquilibration.PureTensorJetBounds

/-! Every original sphere point in a strict positive overlap band has an
actual unit transverse parameter in the complete canonical tangent frame.
The literal all-points band event is therefore exactly the unit-parameter
family used by the actual posterior process maximum law. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm IntrinsicHessianLaw
open SphericalCriticalLatitude PureTensorJetBounds
open Set Metric
open scoped RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem sourceLatitudeUnit_reconstruction {n:ℕ} (u:Vector (n+1))
    (hu:‖u‖^2=(n+1:ℕ)) (w:Vector (n+1)) (hw:‖w‖^2=(n+1:ℕ))
    (hr:overlap u w∈Ioo (0:ℝ) 1) :
    ∃ x:UnitSphere n,sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) (overlap u w) x=w:=by
  let r:=overlap u w
  have hN:(0:ℝ)<((n+1:ℕ):ℝ):=by positivity
  have huw:inner ℝ u w=r*(n+1:ℕ):=by
    unfold r overlap
    exact (div_mul_cancel₀ _ hN.ne').symm
  have hwu:inner ℝ w u=r*(n+1:ℕ):=by rw [real_inner_comm];exact huw
  have hv:inner ℝ (w-r • u) u=0:=by
    rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hu,hwu]
    ring
  let v:tangentPlane u:=⟨w-r • u,Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hv⟩
  have hvnorm:‖(v:Vector (n+1))‖^2=(n+1:ℕ)*(1-r^2):=by
    change ‖w-r • u‖^2=_
    rw [norm_sub_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,hu,hw,
      inner_smul_right,hwu]
    ring
  let a:=Real.sqrt ((n+1:ℕ)*(1-r^2))
  have ha:0<a:=Real.sqrt_pos.mpr (mul_pos hN (by have hrr:(0:ℝ)<r ∧ r<1:=hr;nlinarith))
  have hz:‖(tangentBasis u hu).repr v‖=a:=by
    rw [LinearIsometryEquiv.norm_map]
    change ‖(v:Vector (n+1))‖=a
    unfold a
    rw [←hvnorm,Real.sqrt_sq (norm_nonneg _)]
  let x:UnitSphere n:=⟨a⁻¹ • (tangentBasis u hu).repr v,by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ha,hz]
    exact inv_mul_cancel₀ ha.ne'⟩
  refine ⟨x,?_⟩
  change r • u+a • sourceLatitudeIsometry u hu (a⁻¹ • (tangentBasis u hu).repr v)=w
  rw [map_smul,sourceLatitudeIsometry_reconstruct,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  change r • u+(w-r • u)=w
  module

theorem sourceOverlapBandHeight_unit_iff {n P:ℕ} (c:Degree P→ℝ)
    {ε η:ℝ} (hε:0<ε) (hη:0<η) (H:ℝ) (J:Disorder (n+1) P)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)) :
    sourceOverlapBandHeight c ε η H J u ↔
      ∀ r∈Icc ε (1-η),∀ x:UnitSphere n,
        field c J (sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) r x) ≤ H:=by
  constructor
  · intro hBand r hr x
    have hr':r∈Ioo (0:ℝ) 1:=⟨hε.trans_le hr.1,by linarith [hr.2]⟩
    have hshape:=sourceUnitLatitudeMap_norm_sq (by omega) u hu _ (sourceLatitudeIsometry_orthogonal u hu)
      hr' (x:Vector n) (by rw [unit_norm x];norm_num)
    have ho:=sourceUnitLatitudeMap_overlap (by omega) u hu _ (sourceLatitudeIsometry_orthogonal u hu) r (x:Vector n)
    exact hBand _ hshape (by rw [ho];exact hr.1) (by rw [ho];exact hr.2)
  · intro hAll w hw hlo hhi
    have hr:overlap u w∈Ioo (0:ℝ) 1:=⟨hε.trans_le hlo,by linarith⟩
    obtain ⟨x,hx⟩:=sourceLatitudeUnit_reconstruction u hu w hw hr
    rw [←hx]
    exact hAll (overlap u w) ⟨hlo,hhi⟩ x

end
end SlowEquilibration.PairConditionalDeterminantMoments
