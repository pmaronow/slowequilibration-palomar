-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPairBlockBounds
public import SlowEquilibration.GaussianRegressionCovariance

/-! Actual correlated-pair Gaussian law from genuine marginal and cross
Gram operators. Singular target laws and correlations ±1 are permitted. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {E E' F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Equality of actual Gram operators gives equality of full Gaussian laws,
including covariance-singular observations. -/
theorem gaussian_map_eq_of_gram (A : E →L[ℝ] F) (B : E' →L[ℝ] F) (hGram : gram A=gram B) :
    (stdGaussian E).map A=(stdGaussian E').map B := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian,integral_id_stdGaussian,map_zero,map_zero]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,covarianceBilin_stdGaussian,innerSL_apply_apply,innerSL_apply_apply,
      A.adjoint_inner_left,B.adjoint_inner_left]
    change inner ℝ u (gram A v)=inner ℝ u (gram B v)
    rw [hGram]

def firstCopy (R : E' →L[ℝ] F) : WithLp 2 (E'×E') →L[ℝ] F := R.comp (WithLp.fstL 2 ℝ E' E')
def secondCopy (R : E' →L[ℝ] F) : WithLp 2 (E'×E') →L[ℝ] F := R.comp (WithLp.sndL 2 ℝ E' E')

def correlatedSecond (R : E' →L[ℝ] F) (ρ s : ℝ) : WithLp 2 (E'×E') →L[ℝ] F :=
  ρ • firstCopy R+s • secondCopy R

def correlatedPair (R : E' →L[ℝ] F) (ρ s : ℝ) : WithLp 2 (E'×E') →L[ℝ] WithLp 2 (F×F) :=
  pairHilbert (firstCopy R) (correlatedSecond R ρ s)

omit [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace F] [BorelSpace F] in
lemma firstCopy_adjoint (R : E' →L[ℝ] F) (u : F) :
    (firstCopy R).adjoint u=WithLp.toLp 2 (R.adjoint u,0) := by
  apply ext_inner_right ℝ
  intro z
  rw [(firstCopy R).adjoint_inner_left,WithLp.prod_inner_apply,R.adjoint_inner_left]
  simp only [inner_zero_left,add_zero]
  rfl

omit [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace F] [BorelSpace F] in
lemma secondCopy_adjoint (R : E' →L[ℝ] F) (u : F) :
    (secondCopy R).adjoint u=WithLp.toLp 2 (0,R.adjoint u) := by
  apply ext_inner_right ℝ
  intro z
  rw [(secondCopy R).adjoint_inner_left,WithLp.prod_inner_apply,R.adjoint_inner_left]
  simp only [inner_zero_left,zero_add]
  rfl

omit [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace F] [BorelSpace F] in
lemma firstCopy_gram (R : E' →L[ℝ] F) : gram (firstCopy R)=gram R := by
  ext u
  rw [gram,ContinuousLinearMap.comp_apply,firstCopy_adjoint]
  rfl

omit [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace F] [BorelSpace F] in
lemma correlatedSecond_adjoint (R : E' →L[ℝ] F) (ρ s : ℝ) (u : F) :
    (correlatedSecond R ρ s).adjoint u=WithLp.toLp 2 (ρ • R.adjoint u,s • R.adjoint u) := by
  simp only [correlatedSecond,map_add,map_smul,add_apply,smul_apply,firstCopy_adjoint,secondCopy_adjoint]
  rw [← WithLp.toLp_smul,← WithLp.toLp_smul,← WithLp.toLp_add]
  simp

omit [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace F] [BorelSpace F] in
lemma correlatedSecond_gram (R : E' →L[ℝ] F) (ρ s : ℝ) (h : ρ^2+s^2=1) :
    gram (correlatedSecond R ρ s)=gram R := by
  ext u
  rw [gram,ContinuousLinearMap.comp_apply,correlatedSecond_adjoint]
  change ρ • R (ρ • R.adjoint u)+s • R (s • R.adjoint u)=R (R.adjoint u)
  rw [map_smul,map_smul,smul_smul,smul_smul,← add_smul,← pow_two,← pow_two,h,one_smul]

omit [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace F] [BorelSpace F] in
lemma correlatedPair_cross (R : E' →L[ℝ] F) (ρ s : ℝ) :
    (firstCopy R).comp (correlatedSecond R ρ s).adjoint=ρ • gram R := by
  ext u
  rw [ContinuousLinearMap.comp_apply,correlatedSecond_adjoint]
  change R (ρ • R.adjoint u)=ρ • R (R.adjoint u)
  rw [map_smul]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  [MeasurableSpace F] [BorelSpace F] in
lemma pair_gram_eq_of_blocks (A1 A2 : E →L[ℝ] F) (B1 B2 : E' →L[ℝ] F)
    (h1 : gram A1=gram B1) (h2 : gram A2=gram B2)
    (hcross : A1.comp A2.adjoint=B1.comp B2.adjoint) :
    gram (pairHilbert A1 A2)=gram (pairHilbert B1 B2) := by
  have hrev : A2.comp A1.adjoint=B2.comp B1.adjoint := by
    have h:=congrArg ContinuousLinearMap.adjoint hcross
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint] using h
  apply ContinuousLinearMap.ext
  intro w
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (gram (pairHilbert A1 A2) w).fst=(gram (pairHilbert B1 B2) w).fst
    rw [pair_gram_left,pair_gram_left,h1,hcross]
  · change (gram (pairHilbert A1 A2) w).snd=(gram (pairHilbert B1 B2) w).snd
    rw [pair_gram_right,pair_gram_right,h2,hrev]

/-- The full joint law is derived from the actual Gram and cross operators,
not supplied as a correlated-GOE assumption. -/
theorem gaussian_pair_law_eq_correlated (A1 A2 : E →L[ℝ] F) (R : E' →L[ℝ] F)
    (ρ s : ℝ) (h : ρ^2+s^2=1) (h1 : gram A1=gram R) (h2 : gram A2=gram R)
    (hcross : A1.comp A2.adjoint=ρ • gram R) :
    (stdGaussian E).map (pairHilbert A1 A2)=
      (stdGaussian (WithLp 2 (E'×E'))).map (correlatedPair R ρ s) := by
  apply gaussian_map_eq_of_gram
  apply pair_gram_eq_of_blocks
  · rw [firstCopy_gram,h1]
  · rw [correlatedSecond_gram R ρ s h,h2]
  · rw [correlatedPair_cross,hcross]

end
end SlowEquilibration.GaussianObservationCoercivity
