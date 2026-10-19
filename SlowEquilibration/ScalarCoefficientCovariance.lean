-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.IntrinsicHessianLaw

/-! Covariance algebra for literal scalar maps on the actual disorder space. -/
@[expose] public section
namespace SlowEquilibration.ScalarCoefficientCovariance
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scalarCross (f g : E →L[ℝ] ℝ) : ℝ := f (g.adjoint 1)

lemma scalarCross_add_left (f g h : E →L[ℝ] ℝ) :
    scalarCross (f+g) h=scalarCross f h+scalarCross g h := rfl
lemma scalarCross_add_right (f g h : E →L[ℝ] ℝ) :
    scalarCross f (g+h)=scalarCross f g+scalarCross f h := by
  simp only [scalarCross,map_add,add_apply]
lemma scalarCross_smul_left (r : ℝ) (f g : E →L[ℝ] ℝ) :
    scalarCross (r • f) g=r*scalarCross f g := rfl
lemma scalarCross_smul_right (r : ℝ) (f g : E →L[ℝ] ℝ) :
    scalarCross f (r • g)=r*scalarCross f g := by
  simp only [scalarCross,map_smul,smul_apply,smul_eq_mul]

lemma scalarCross_dual {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : E →L[ℝ] F) (B : E →L[ℝ] G) (u : F) (v : G) :
    scalarCross ((innerSL ℝ u).comp A) ((innerSL ℝ v).comp B)=
      inner ℝ u (A (B.adjoint v)) := by
  simp only [scalarCross,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one,innerSL_apply_apply]

lemma scalarCross_flatJet {N P : ℕ} (c : Degree P → ℝ) (a b : ℕ)
    (x y : Vector N) (u : Fin a → Vector N) (v : Fin b → Vector N) :
    scalarCross (flatJetCLM c a x u) (flatJetCLM c b y v)=
      cov[jet c a x u,jet c b y v;disorderLaw N P] := by
  have h:=actual_scalar_cross_covariance (flatJetCLM c a x u) (flatJetCLM c b y v) (1:ℝ)
  simpa only [flatJetCLM_apply,unpack_euclideanDisorder,real_inner_comm,
    RCLike.inner_apply,conj_trivial,mul_one,scalarCross] using h.symm

end
end SlowEquilibration.ScalarCoefficientCovariance
