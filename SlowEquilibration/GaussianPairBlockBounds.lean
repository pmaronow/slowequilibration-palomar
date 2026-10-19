-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairGramSchurDeterminant

/-! Dimension-free operator bounds on genuine Hilbert-product covariance
blocks, and an actual independent product observation for comparison. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {E F G H I E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup I] [InnerProductSpace ℝ I] [FiniteDimensional ℝ I]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

lemma inner_cross_bound (A : E →L[ℝ] F) (B : E →L[ℝ] G) (u : F) (v : G)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |inner ℝ (A.adjoint u) (B.adjoint v)| ≤ ‖A.comp B.adjoint‖ := by
  rw [A.adjoint_inner_left]
  calc
    _ ≤ ‖u‖*‖A (B.adjoint v)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖*(‖A.comp B.adjoint‖*‖v‖) := by
      gcongr
      exact (A.comp B.adjoint).le_opNorm v
    _ ≤ 1*(‖A.comp B.adjoint‖*1) := by gcongr
    _ = _ := by ring

/-- The bound uses the four actual covariance blocks without a dimension
factor. Diagonal zero blocks disappear exactly upon specialization. -/
theorem pair_cross_block_bound (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (C : E →L[ℝ] H) (D : E →L[ℝ] I) :
    ‖(pairHilbert A B).comp (pairHilbert C D).adjoint‖ ≤
      ‖A.comp C.adjoint‖+‖A.comp D.adjoint‖+‖B.comp C.adjoint‖+‖B.comp D.adjoint‖ := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro v u hv hu
  change inner ℝ (pairHilbert A B ((pairHilbert C D).adjoint v)) u ≤ _
  rw [real_inner_comm,← (pairHilbert A B).adjoint_inner_left,
    pairHilbert_adjoint,pairHilbert_adjoint,inner_add_left,inner_add_right,inner_add_right]
  have huf : ‖u.fst‖ ≤ 1 := (WithLp.norm_fst_le _ u).trans_eq hu
  have hus : ‖u.snd‖ ≤ 1 := (WithLp.norm_snd_le _ u).trans_eq hu
  have hvf : ‖v.fst‖ ≤ 1 := (WithLp.norm_fst_le _ v).trans_eq hv
  have hvs : ‖v.snd‖ ≤ 1 := (WithLp.norm_snd_le _ v).trans_eq hv
  have h1:=inner_cross_bound A C u.fst v.fst huf hvf
  have h2:=inner_cross_bound A D u.fst v.snd huf hvs
  have h3:=inner_cross_bound B C u.snd v.fst hus hvf
  have h4:=inner_cross_bound B D u.snd v.snd hus hvs
  linarith [le_abs_self (inner ℝ (A.adjoint u.fst) (C.adjoint v.fst)),
    le_abs_self (inner ℝ (A.adjoint u.fst) (D.adjoint v.snd)),
    le_abs_self (inner ℝ (B.adjoint u.snd) (C.adjoint v.fst)),
    le_abs_self (inner ℝ (B.adjoint u.snd) (D.adjoint v.snd))]

/-- Ordinary independent product of two actual linear Gaussian observations. -/
def independentPair (A : E →L[ℝ] F) (B : E' →L[ℝ] G) :
    WithLp 2 (E×E') →L[ℝ] WithLp 2 (F×G) :=
  pairHilbert (A.comp (WithLp.fstL 2 ℝ E E')) (B.comp (WithLp.sndL 2 ℝ E E'))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] [FiniteDimensional ℝ E'] in
lemma independentPair_apply (A : E →L[ℝ] F) (B : E' →L[ℝ] G) (w : WithLp 2 (E×E')) :
    independentPair A B w=WithLp.toLp 2 (A w.fst,B w.snd) := rfl

lemma independentPair_adjoint (A : E →L[ℝ] F) (B : E' →L[ℝ] G) (w : WithLp 2 (F×G)) :
    (independentPair A B).adjoint w=WithLp.toLp 2 (A.adjoint w.fst,B.adjoint w.snd) := by
  apply ext_inner_right ℝ
  intro z
  rw [(independentPair A B).adjoint_inner_left,independentPair_apply,WithLp.prod_inner_apply,
    WithLp.prod_inner_apply,A.adjoint_inner_left,B.adjoint_inner_left]
  rfl

lemma independentPair_gram_apply (A : E →L[ℝ] F) (B : E' →L[ℝ] G) (w : WithLp 2 (F×G)) :
    gram (independentPair A B) w=WithLp.toLp 2 (gram A w.fst,gram B w.snd) := by
  rw [gram,ContinuousLinearMap.comp_apply,independentPair_adjoint,independentPair_apply]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] [FiniteDimensional ℝ E'] in
lemma independentPair_surjective (A : E →L[ℝ] F) (B : E' →L[ℝ] G)
    (hA : Surjective A) (hB : Surjective B) : Surjective (independentPair A B) := by
  intro w
  obtain ⟨x,hx⟩:=hA w.fst
  obtain ⟨y,hy⟩:=hB w.snd
  exact ⟨WithLp.toLp 2 (x,y),by rw [independentPair_apply];simp only [WithLp.toLp_fst,WithLp.toLp_snd,hx,hy];rfl⟩

/-- Equal actual marginal covariances leave precisely the two cross blocks. -/
theorem pair_gram_difference_independent (A B : E →L[ℝ] F)
    (A₀ B₀ : E' →L[ℝ] F) (hA : gram A=gram A₀) (hB : gram B=gram B₀) :
    ‖gram (pairHilbert A B)-gram (independentPair A₀ B₀)‖ ≤ 2*‖A.comp B.adjoint‖ := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro v u hv hu
  change inner ℝ ((gram (pairHilbert A B)-gram (independentPair A₀ B₀)) v) u ≤ _
  rw [real_inner_comm,sub_apply,inner_sub_right]
  rw [WithLp.prod_inner_apply,WithLp.prod_inner_apply]
  change (inner ℝ u.fst (gram (pairHilbert A B) v).fst+inner ℝ u.snd (gram (pairHilbert A B) v).snd)-
    (inner ℝ u.fst (gram (independentPair A₀ B₀) v).fst+inner ℝ u.snd (gram (independentPair A₀ B₀) v).snd) ≤ _
  rw [pair_gram_left,pair_gram_right,independentPair_gram_apply]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,inner_add_right,hA,hB]
  have h1:=inner_cross_bound A B u.fst v.snd
    ((WithLp.norm_fst_le _ u).trans_eq hu) ((WithLp.norm_snd_le _ v).trans_eq hv)
  have h2:=inner_cross_bound B A u.snd v.fst
    ((WithLp.norm_snd_le _ u).trans_eq hu) ((WithLp.norm_fst_le _ v).trans_eq hv)
  rw [A.adjoint_inner_left] at h1
  rw [B.adjoint_inner_left] at h2
  have hadj : B.comp A.adjoint=(A.comp B.adjoint).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  rw [hadj,LinearIsometryEquiv.norm_map] at h2
  simp only [ContinuousLinearMap.comp_apply]
  linarith [le_abs_self (inner ℝ u.fst (A (B.adjoint v.snd))),
    le_abs_self (inner ℝ u.snd (B (A.adjoint v.fst)))]

end
end SlowEquilibration.GaussianObservationCoercivity
