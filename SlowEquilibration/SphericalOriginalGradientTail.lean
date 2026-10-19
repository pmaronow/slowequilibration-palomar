-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientIndependence
public import SlowEquilibration.SphericalGaussianAxis
public import Mathlib.Probability.Moments.SubGaussian

/-! Exact original center tangent-gradient Gaussian MGF and fixed-state
tail with the manuscript variance a_Q=Q xi'(Q). -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open GaussianRegression IntrinsicGradientRegression SphericalPosteriorMaps
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem gaussian_inner_subGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (v : E) :
    HasSubgaussianMGF (fun g : E=>inner ℝ v g) (‖v‖^2).toNNReal (stdGaussian E) := by
  let L := innerSL ℝ v
  have hG : HasGaussianLaw (fun g : E=>inner ℝ v g) (stdGaussian E) := by
    simpa only [L,id_eq,innerSL_apply_apply] using (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun L
  have hLaw : (stdGaussian E).map (fun g : E=>inner ℝ v g)=gaussianReal 0 (‖v‖^2).toNNReal := by
    rw [hG.map_eq_gaussianReal]
    rw [show (∫ g : E,inner ℝ v g ∂stdGaussian E)=0 from integral_strongDual_stdGaussian L]
    rw [show Var[fun g : E=>inner ℝ v g;stdGaussian E]=‖v‖^2 by
      change Var[L;stdGaussian E]=_
      rw [variance_dual_stdGaussian,innerSL_apply_norm]]
  have hId : HasSubgaussianMGF id (‖v‖^2).toNNReal (gaussianReal 0 (‖v‖^2).toNNReal) := by
    refine { integrable_exp_mul := fun t=>integrable_exp_mul_gaussianReal t, mgf_le := ?_ }
    intro t
    rw [mgf_gaussianReal (μ:=0) (v:=(‖v‖^2).toNNReal) (by simp)]
    simp
  have hh := HasSubgaussianMGF.of_map L.measurable.aemeasurable (hLaw.symm ▸ hId)
  have he : (L : E→ℝ)=(fun g : E=>inner ℝ v g) := by funext g; rfl
  simpa only [id_comp,he] using hh

theorem subGaussian_mono_parameter {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω→ℝ} {a b : ℝ≥0} (hX : HasSubgaussianMGF X a μ) (hab : a ≤ b) :
    HasSubgaussianMGF X b μ := by
  refine ⟨hX.integrable_exp_mul,fun t=>(hX.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show (a:ℝ) ≤ (b:ℝ) from hab) (sq_nonneg t)) (by norm_num)

theorem original_tangent_projection_subGaussian (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (y : Vector (n+1)) (hy : ‖y‖^2=(n+1:ℕ)) :
    HasSubgaussianMGF (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) y/(n+1:ℕ))
      (Q*μ.xi1 Q/(n+1:ℕ)).toNNReal (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A := intrinsicGamma c u
  let w := (tangentPlane u).orthogonalProjectionOnto y
  let v := (1/(n+1:ℕ):ℝ) • A.adjoint w
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have ha : 0 < Q*μ.xi1 Q := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hGram := center_intrinsicGamma_gram (by omega : 0 < n+1) μ hQ.le u hu
  have hnorm : ‖A.adjoint w‖^2=(Q*μ.xi1 Q)*‖w‖^2 := by
    rw [← real_inner_self_eq_norm_sq,A.adjoint_inner_left]
    change inner ℝ w (gram A w)=_
    rw [hGram]
    simp only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hw : ‖w‖^2 ≤ ((n+1:ℕ):ℝ) := by
    have hh := (sq_le_sq₀ (norm_nonneg w) (norm_nonneg y)).mpr
      ((tangentPlane u).norm_orthogonalProjectionOnto_apply_le y)
    exact hh.trans_eq hy
  have hv : ‖v‖^2 ≤ Q*μ.xi1 Q/(n+1:ℕ) := by
    dsimp only [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (1/(n+1:ℕ):ℝ)),mul_pow,hnorm]
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ (1/(n+1:ℕ):ℝ)^2*(Q*μ.xi1 Q) by positivity)
    calc
      _ = (1/(n+1:ℕ):ℝ)^2*(Q*μ.xi1 Q)*‖w‖^2 := by ring
      _ ≤ _ := hh
      _ = _ := by field_simp
  have hEval (g) : inner ℝ v g =
      inner ℝ (surfaceGradient (field c (unpackDisorder g)) u) y/(n+1:ℕ) := by
    rw [show surfaceGradient (field c (unpackDisorder g)) u=(A g:Vector (n+1)) from
      (intrinsicGamma_coe (by omega : n+1≠0) c u hu g).symm]
    dsimp only [v,w]
    rw [real_inner_smul_left,A.adjoint_inner_left,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,real_inner_comm]
    ring
  have hh := subGaussian_mono_parameter (gaussian_inner_subGaussian v) (Real.toNNReal_le_toNNReal hv)
  simpa only [hEval] using hh

/-- Exact fixed-state original-gradient tail with the printed source
normalization; the budget is derived from the actual center covariance. -/
theorem original_tangent_projection_tail (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (y : Vector (n+1)) (hy : ‖y‖^2=(n+1:ℕ)) {α : ℝ} (hα : 0 ≤ α) :
    (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).real
      {g | α/2 ≤ |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) y/(n+1:ℕ)|} ≤
      2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) := by
  let X := fun g : EuclideanDisorder (n+1) μ.maxDegree=>
    inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) y/(n+1:ℕ)
  have hX := original_tangent_projection_subGaussian n μ hQ u hu y hy
  have hsub : {g | α/2 ≤ |X g|} ⊆ {g | α/2 ≤ X g} ∪ {g | α/2 ≤ -X g} := by
    intro g hg
    change α/2 ≤ |X g| at hg
    exact le_abs.mp hg
  have hRight := hX.measure_ge_le (show 0 ≤ α/2 by positivity)
  have hLeft := hX.neg.measure_ge_le (show 0 ≤ α/2 by positivity)
  have hp := (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hRight hLeft))
  have ha : 0 < Q*μ.xi1 Q := mul_pos hQ (mixture_xi1_pos μ hQ)
  rw [Real.coe_toNNReal _ (by positivity)] at hp
  have he : -(α/2)^2/(2*(Q*μ.xi1 Q/(n+1:ℕ))) = -((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q)) := by
    field_simp
    ring
  rw [he] at hp
  simpa only [X,two_mul] using hp

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
