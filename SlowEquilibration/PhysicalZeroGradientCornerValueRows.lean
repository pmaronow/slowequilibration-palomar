-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalZeroGradientCornerPairRows
public import SlowEquilibration.PairResidualValueCoercivity

/-! Proper value-only Hessian rows, retaining the sharp active-degree rate.
No inverse of a redundant pure-model radial observation is introduced. -/
@[expose] public section
namespace SlowEquilibration.PhysicalZeroGradientCorner
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open PairObservationNormBounds HessianObservationCovariance
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 700000

lemma score_adjoint_scalar_value {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) (w : ℝ) :
    (normalizedScore c x).adjoint (WithLp.toLp 2 ![w,0]) =
      (normalizedValue c x).adjoint w := by
  have hd : (innerSL ℝ (WithLp.toLp 2 ![w,0] : EuclideanSpace ℝ (Fin 2))).comp
      (normalizedScore c x)=(innerSL ℝ w).comp (normalizedValue c x) := by
    rw [normalizedScore_dual,normalizedValue_dual]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,zero_div,zero_smul,add_zero]
    rfl
  have hh := congrArg (fun L : EuclideanDisorder N P →L[ℝ] ℝ => L.adjoint (1:ℝ)) hd
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_innerSL_apply, ContinuousLinearMap.toSpanSingleton_apply_one] using hh

lemma scalar_score_norm (w : ℝ) :
    ‖(WithLp.toLp 2 ![w,0] : EuclideanSpace ℝ (Fin 2))‖=‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,norm_zero,zero_pow,
    ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,add_zero]

theorem hessian_pair_value_degree_order {N P : ℕ} (hN : 0<N) (c : Degree P → ℝ)
    (hc : ∀ p,0≤c p) {d : ℕ} (hd : 3≤d) (hdeg : ∀ p,c p≠0 → d≤p.val.val)
    (x y u v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (htanu : inner ℝ u x=0) (htanv : inner ℝ v x=0) (hr : |overlap x y|≤1) :
    ‖(flatJetCLM c 2 x ![u,v]).comp (valuePair c x y).adjoint‖≤
      4*profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by
  let H:=flatJetCLM c 2 x ![u,v]
  have hrow := hessian_score_degree_order hN c hc hd hdeg x y u v hy hu hv hr
  apply norm_pair_hessian_row H (normalizedValue c x) (normalizedValue c y)
    (by positivity [profileBound_pos c])
  · intro w
    rw [← score_adjoint_scalar_value]
    exact own_score_hessian_zero hN c hc (fun p hp => by have hh:=hdeg p hp;omega)
      x u v htanu htanv _
  · intro w
    have hb := ((H.comp (normalizedScore c y).adjoint).le_opNorm
      (WithLp.toLp 2 ![w,0])).trans (mul_le_mul_of_nonneg_right hrow (norm_nonneg _))
    rwa [ContinuousLinearMap.comp_apply,score_adjoint_scalar_value,scalar_score_norm] at hb

end
end SlowEquilibration.PhysicalZeroGradientCorner
