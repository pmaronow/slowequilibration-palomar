-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedObservationBlocks
public import SlowEquilibration.PairGradientNondegeneracy
public import SlowEquilibration.ObservationTargetEquiv
public import SlowEquilibration.GaussianResidualCoercivity

/-! Exact isometric regrouping of the actual mixed pair into its score and
gradient blocks. This preserves the canonical whole-field posterior at every
target and transfers the actual uniform observation coercivity. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity ObservationTargetEquiv
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

abbrev ScorePairSpace := WithLp 2 (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))
abbrev GradientPairSpace (m : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin m)×EuclideanSpace ℝ (Fin m))
abbrev MixedPairSpace (m : ℕ) := WithLp 2 (MixedObservationSpace m×MixedObservationSpace m)
abbrev GroupedMixedPairSpace (m : ℕ) := WithLp 2 (ScorePairSpace×GradientPairSpace m)

def pairScoreProjection (m : ℕ) : MixedPairSpace m →L[ℝ] ScorePairSpace :=
  pairHilbert
    ((WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin m))).comp
      (WithLp.fstL 2 ℝ (MixedObservationSpace m) (MixedObservationSpace m)))
    ((WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin m))).comp
      (WithLp.sndL 2 ℝ (MixedObservationSpace m) (MixedObservationSpace m)))

def pairGradientProjection (m : ℕ) : MixedPairSpace m →L[ℝ] GradientPairSpace m :=
  pairHilbert
    ((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin m))).comp
      (WithLp.fstL 2 ℝ (MixedObservationSpace m) (MixedObservationSpace m)))
    ((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin m))).comp
      (WithLp.sndL 2 ℝ (MixedObservationSpace m) (MixedObservationSpace m)))

def mixedGrouping (m : ℕ) : MixedPairSpace m →L[ℝ] GroupedMixedPairSpace m :=
  pairHilbert (pairScoreProjection m) (pairGradientProjection m)

def mixedUngrouping (m : ℕ) : GroupedMixedPairSpace m →L[ℝ] MixedPairSpace m :=
  pairHilbert
    (pairHilbert
      ((WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))).comp
        (WithLp.fstL 2 ℝ ScorePairSpace (GradientPairSpace m)))
      ((WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))).comp
        (WithLp.sndL 2 ℝ ScorePairSpace (GradientPairSpace m))))
    (pairHilbert
      ((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))).comp
        (WithLp.fstL 2 ℝ ScorePairSpace (GradientPairSpace m)))
      ((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))).comp
        (WithLp.sndL 2 ℝ ScorePairSpace (GradientPairSpace m))))

lemma mixedGrouping_norm (m : ℕ) (w : MixedPairSpace m) : ‖mixedGrouping m w‖=‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [WithLp.prod_norm_sq_eq_of_L2]
  change (‖w.fst.fst‖^2+‖w.snd.fst‖^2)+(‖w.fst.snd‖^2+‖w.snd.snd‖^2)=
    (‖w.fst.fst‖^2+‖w.fst.snd‖^2)+(‖w.snd.fst‖^2+‖w.snd.snd‖^2)
  ring

/-- Genuine Hilbert isometry, merely permuting the four observation blocks. -/
def mixedGroupingEquiv (m : ℕ) : MixedPairSpace m ≃ₗᵢ[ℝ] GroupedMixedPairSpace m where
  toLinearEquiv :=
    { toLinearMap := (mixedGrouping m).toLinearMap
      invFun := mixedUngrouping m
      left_inv := by intro w;rfl
      right_inv := by intro w;rfl }
  norm_map' := mixedGrouping_norm m

def scorePair {N P : ℕ} (c : Degree P → ℝ) (x y : Vector N) :
    EuclideanDisorder N P →L[ℝ] ScorePairSpace :=
  pairHilbert (normalizedScore c x) (normalizedScore c y)

def groupedMixedPair {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] GroupedMixedPairSpace m :=
  pairHilbert (scorePair c x y) (pairGradient c x y e f)

lemma groupedMixedPair_eq {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) :
    groupedMixedPair c x y e f=(mixedGroupingEquiv m : MixedPairSpace m →L[ℝ] GroupedMixedPairSpace m).comp
      (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)) := by
  ext z
  rfl

lemma groupedMixedPair_coercive {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) {α : ℝ}
    (hA : CoerciveObservation (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)) α) :
    CoerciveObservation (groupedMixedPair c x y e f) α := by
  intro w
  rw [groupedMixedPair_eq,ContinuousLinearMap.adjoint_comp,(mixedGroupingEquiv m).adjoint_eq_symm]
  simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',LinearIsometryEquiv.norm_map] using hA ((mixedGroupingEquiv m).symm w)

end
end SlowEquilibration.NormalizedPairObservations
