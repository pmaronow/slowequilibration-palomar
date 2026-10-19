-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeometricIntrinsicBorder

/-! The canonical common-complement frame is unchanged by swapping the
sphere points. Both physical intrinsic Hessians therefore use one literal
common bulk frame in the source pair determinant comparison. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open SphericalModel SphericalGaussianJet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma commonPlane_comm {N:ℕ} (x y:Vector N) : commonPlane x y=commonPlane y x:=by
  simp only [commonPlane,Matrix.range_cons_cons_empty,Set.pair_comm]

private lemma canonical_frame_eq {N m:ℕ} (S T:Submodule ℝ (Vector N))
    (hS:Module.finrank ℝ S=m) (hT:Module.finrank ℝ T=m) (hST:S=T) :
    (fun i:Fin m=>(((stdOrthonormalBasis ℝ S).reindex (finCongr hS)) i:Vector N))=
      (fun i:Fin m=>(((stdOrthonormalBasis ℝ T).reindex (finCongr hT)) i:Vector N)):=by
  subst T
  rfl

lemma commonFrame_comm {N:ℕ} (hN:0<N) (x y:Vector N)
    (hx:‖x‖^2=(N:ℝ)) (hy:‖y‖^2=(N:ℝ)) (hxy:|overlap x y|<1) (hyx:|overlap y x|<1) :
    commonFrame hN x y hx hy hxy=commonFrame hN y x hy hx hyx:=by
  exact canonical_frame_eq _ _ _ _ (commonPlane_comm x y)

end
end SlowEquilibration.SphericalPairCommonFrame
