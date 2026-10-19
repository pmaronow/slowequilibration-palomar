-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointHamiltonianContDiff

/-! Joint C1 regularity of the actual spatial Riesz and spherical
gradients of a joint C2 Hamiltonian. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel PairConditionalDeterminantMoments
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

def jointSpatialGradient (H : Θ×Vector N→ℝ) (z : Θ×Vector N) : Vector N :=
  gradient (fun x => H (z.1,x)) z.2

theorem jointSpatialGradient_contDiff (H : Θ×Vector N→ℝ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (jointSpatialGradient H) := by
  have hh : ContDiff ℝ 2 (fun z : (Θ×Vector N)×Vector N => H (z.1.1,z.2)) :=
    hH.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ 1 (fun z : Θ×Vector N => fderiv ℝ (fun x => H (z.1,x)) z.2) :=
    hh.fderiv (f:=fun z : Θ×Vector N => fun x => H (z.1,x)) contDiff_snd (by norm_num)
  exact (InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff.comp hd

theorem jointSurfaceGradient_contDiff (H : Θ×Vector N→ℝ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun z : Θ×Vector N => surfaceGradient (fun x => H (z.1,x)) z.2) :=
  (((source_tangentProjection_contDiff N).of_le (by simp)).comp contDiff_snd).clm_apply
    (jointSpatialGradient_contDiff H hH)

end SlowEquilibration.SphericalForm

namespace SlowEquilibration.ConditionedEntrance
open SphericalForm
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem sourceJointSpatialGradient_contDiff {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 1 (jointSpatialGradient (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ)) :=
  jointSpatialGradient_contDiff _ (sourceJointHamiltonian_contDiff μ Q hQ hnp α χ hχ)

end SlowEquilibration.ConditionedEntrance
