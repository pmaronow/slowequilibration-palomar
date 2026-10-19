-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationGrouping
public import SlowEquilibration.PairScoreDisintegration

/-! Proper pure/value pair observations, without redundant radial scores. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- Genuine Hilbert rearrangement of the four blocks. -/
def hilbertRegroup {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] :
    WithLp 2 (WithLp 2 (F×G)×WithLp 2 (F×G)) ≃ₗᵢ[ℝ]
      WithLp 2 (WithLp 2 (F×F)×WithLp 2 (G×G)) where
  toLinearEquiv :=
    ((WithLp.linearEquiv 2 ℝ _).trans
      ((LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (F×G)) (WithLp.linearEquiv 2 ℝ (F×G))).trans
        ((LinearEquiv.prodProdProdComm ℝ F G F G).trans
          ((LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (F×F)).symm (WithLp.linearEquiv 2 ℝ (G×G)).symm).trans
            (WithLp.linearEquiv 2 ℝ _).symm))))
  norm_map' := by
    intro w
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [WithLp.prod_norm_sq_eq_of_L2]
    change (‖w.fst.fst‖^2+‖w.snd.fst‖^2)+(‖w.fst.snd‖^2+‖w.snd.snd‖^2)=
      (‖w.fst.fst‖^2+‖w.fst.snd‖^2)+(‖w.snd.fst‖^2+‖w.snd.snd‖^2)
    ring

abbrev ValuePairSpace := WithLp 2 (ℝ×ℝ)
abbrev GroupedValuePairSpace (m : ℕ) := WithLp 2 (ValuePairSpace×GradientPairSpace m)

def normalizedValue {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    EuclideanDisorder N P →L[ℝ] ℝ := (Real.sqrt (N:ℝ))⁻¹ • valueCLM c x

def valuePair {N P : ℕ} (c : Degree P → ℝ) (x y : Vector N) :
    EuclideanDisorder N P →L[ℝ] ValuePairSpace := pairHilbert (normalizedValue c x) (normalizedValue c y)

def groupedValuePair {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] GroupedValuePairSpace m :=
  pairHilbert (valuePair c x y) (pairGradient c x y e f)

def residualPairValue {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] ValuePairSpace :=
  (valuePair c x y).comp (GaussianRegression.residual (pairGradient c x y e f))

lemma groupedValuePair_eq {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) :
    groupedValuePair c x y e f=(hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m)) : _ →L[ℝ] _).comp
      (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)) := by
  ext z
  rfl

lemma groupedValuePair_coercive {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) {α : ℝ}
    (hA : CoerciveObservation (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)) α) :
    CoerciveObservation (groupedValuePair c x y e f) α := by
  intro w
  rw [groupedValuePair_eq,ContinuousLinearMap.adjoint_comp,(hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m))).adjoint_eq_symm]
  simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',LinearIsometryEquiv.norm_map] using hA ((hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m))).symm w)

end
end SlowEquilibration.NormalizedPairObservations
