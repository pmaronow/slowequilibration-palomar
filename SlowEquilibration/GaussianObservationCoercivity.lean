-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegression
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

/-! # Dimension-independent coercivity of true observation Gram operators -/
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Literal uniform lower bound on the true adjoint observation. -/
def CoerciveObservation (A : E →L[ℝ] F) (α : ℝ) : Prop :=
  ∀ u : F, α*‖u‖^2 ≤ ‖A.adjoint u‖^2

theorem gram_inner (A : E →L[ℝ] F) (u : F) :
    inner ℝ u (GaussianRegression.gram A u)=‖A.adjoint u‖^2 := by
  rw [GaussianRegression.gram,ContinuousLinearMap.comp_apply,
    ← A.adjoint_inner_left,real_inner_self_eq_norm_sq]

theorem observation_surjective (A : E →L[ℝ] F) {α : ℝ}
    (hα : 0 < α) (hA : CoerciveObservation A α) : Surjective A := by
  have hadj : Injective A.adjoint := by
    intro u v huv
    have hh := hA (u-v)
    rw [map_sub,huv,sub_self,norm_zero] at hh
    have hn : ‖u-v‖=0 := by
      by_contra hn
      have hp : 0 < ‖u-v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      have hprod := mul_pos hα (sq_pos_of_pos hp)
      norm_num at hh
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hgram : Injective (GaussianRegression.gram A) :=
    A.self_comp_adjoint_injective_iff.mpr hadj
  have hsurj : Surjective (GaussianRegression.gram A) :=
    LinearMap.injective_iff_surjective.mp hgram
  intro y
  obtain ⟨x,hx⟩ := hsurj y
  exact ⟨A.adjoint x,hx⟩

theorem gram_norm_lower (A : E →L[ℝ] F) {α : ℝ}
    (_hα : 0 < α) (hA : CoerciveObservation A α) (u : F) :
    α*‖u‖ ≤ ‖GaussianRegression.gram A u‖ := by
  have hh := (hA u).trans_eq (gram_inner A u).symm
  have hc := real_inner_le_norm u (GaussianRegression.gram A u)
  rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
  · rw [← hzero,mul_zero];exact norm_nonneg _
  · nlinarith

theorem gram_inverse_norm_le (A : E →L[ℝ] F) {α : ℝ}
    (hα : 0 < α) (hA : CoerciveObservation A α) :
    ‖(GaussianRegression.gram A).inverse‖ ≤ 1/α := by
  have hinv := GaussianRegression.gram_isInvertible A (observation_surjective A hα hA)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hg : GaussianRegression.gram A ((GaussianRegression.gram A).inverse y)=y := by
    have hh := congrArg (fun T : F →L[ℝ] F => T y) hinv.self_comp_inverse
    exact hh
  have hh := gram_norm_lower A hα hA ((GaussianRegression.gram A).inverse y)
  rw [hg] at hh
  calc
    _ ≤ ‖y‖/α := (le_div_iff₀ hα).mpr (by nlinarith)
    _ = (1/α)*‖y‖ := by ring

/-- The pair takes values in the actual Hilbert L2 product. -/
def pairHilbert (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    E →L[ℝ] WithLp 2 (F×G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F G).symm.toContinuousLinearMap.comp (A.prod B)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
lemma pairHilbert_apply (A : E →L[ℝ] F) (B : E →L[ℝ] G) (x : E) :
    pairHilbert A B x=WithLp.toLp 2 (A x,B x) := rfl

lemma pairHilbert_adjoint (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (w : WithLp 2 (F×G)) :
    (pairHilbert A B).adjoint w=A.adjoint w.fst+B.adjoint w.snd := by
  apply ext_inner_right ℝ
  intro x
  rw [(pairHilbert A B).adjoint_inner_left,inner_add_left,
    A.adjoint_inner_left,B.adjoint_inner_left,pairHilbert_apply,WithLp.prod_inner_apply]
  rfl

theorem pair_coercive (A : E →L[ℝ] F) (B : E →L[ℝ] G) {α : ℝ}
    (hα : 0 < α) (hA : CoerciveObservation A α) (hB : CoerciveObservation B α)
    (hcross : ‖A.comp B.adjoint‖ ≤ α/2) : CoerciveObservation (pairHilbert A B) (α/2) := by
  intro w
  rw [pairHilbert_adjoint,norm_add_sq_real,WithLp.prod_norm_sq_eq_of_L2]
  have hfst := hA w.fst
  have hsnd := hB w.snd
  have hinner : |inner ℝ (A.adjoint w.fst) (B.adjoint w.snd)| ≤
      (α/2)*‖w.fst‖*‖w.snd‖ := by
    rw [A.adjoint_inner_left]
    have hn := (A.comp B.adjoint).le_opNorm w.snd
    calc
      _ ≤ ‖w.fst‖*‖A (B.adjoint w.snd)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖w.fst‖*((α/2)*‖w.snd‖) :=
        mul_le_mul_of_nonneg_left (hn.trans (mul_le_mul_of_nonneg_right hcross (norm_nonneg _)))
          (norm_nonneg _)
      _ = _ := by ring
  have hlow := neg_abs_le (inner ℝ (A.adjoint w.fst) (B.adjoint w.snd))
  nlinarith [sq_nonneg (‖w.fst‖-‖w.snd‖)]

theorem pair_surjective (A : E →L[ℝ] F) (B : E →L[ℝ] G) {α : ℝ}
    (hα : 0 < α) (hA : CoerciveObservation A α) (hB : CoerciveObservation B α)
    (hcross : ‖A.comp B.adjoint‖ ≤ α/2) : Surjective (pairHilbert A B) :=
  observation_surjective _ (half_pos hα) (pair_coercive A B hα hA hB hcross)

theorem pair_gram_inverse_norm_le (A : E →L[ℝ] F) (B : E →L[ℝ] G) {α : ℝ}
    (hα : 0 < α) (hA : CoerciveObservation A α) (hB : CoerciveObservation B α)
    (hcross : ‖A.comp B.adjoint‖ ≤ α/2) :
    ‖(GaussianRegression.gram (pairHilbert A B)).inverse‖ ≤ 2/α := by
  have hh := gram_inverse_norm_le _ (half_pos hα) (pair_coercive A B hα hA hB hcross)
  convert hh using 1
  field_simp

end
end SlowEquilibration.GaussianObservationCoercivity
