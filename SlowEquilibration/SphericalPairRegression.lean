-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairOrthogonalJetCovariances
public import SlowEquilibration.SphericalHessianTraceCovariance
public import SlowEquilibration.ValueTangentConditioning
public import SlowEquilibration.GaussianOrthogonalRegression

/-! Actual two-point whole-disorder Gaussian observations, with separate
nonpure value/radial observations and proper value-only pure observations.
Zero-overlap nonsingularity is derived from the original tensor covariances. -/

@[expose] public section
namespace SlowEquilibration.SphericalPairRegression

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open IntrinsicGradientRegression ValueTangentConditioning GaussianRegression
open PairOrthogonalJetCovariances
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- The actual joint observation of two complete mixed critical-point jets. -/
def pairJointCLM {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ]
      (EuclideanSpace ℝ (Sum (Fin 2) (Fin m)) × EuclideanSpace ℝ (Sum (Fin 2) (Fin m))) :=
  (jointCLM c x e).prod (jointCLM c y f)

/-- The actual proper two-point value/tangent observation, omitting redundant
radial coordinates in the pure case. -/
def pairValueCLM {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ]
      (EuclideanSpace ℝ (Sum (Fin 1) (Fin m)) × EuclideanSpace ℝ (Sum (Fin 1) (Fin m))) :=
  (valueTangentCLM c x e).prod (valueTangentCLM c y f)

/-- Mixed coordinate observations are true first-order field jets. -/
lemma joint_coordinate_low_order {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (i : Sum (Fin 2) (Fin m)) :
    ∃ k : ℕ,k ≤ 1 ∧ ∃ a : Fin k → Vector N,
      ∀ J : Disorder N P,actualObservation (jointCLM c x e) J i=jet c k x a J := by
  cases i with
  | inl i =>
    fin_cases i
    · refine ⟨0,by omega,(fun i => Fin.elim0 i),?_⟩
      intro J
      change scoreCLM c x (euclideanDisorder J) 0=jet c 0 x (fun i => Fin.elim0 i) J
      rw [scoreCLM_apply_zero,unpack_euclideanDisorder]
    · refine ⟨1,by omega,(fun _ => x),?_⟩
      intro J
      change scoreCLM c x (euclideanDisorder J) 1=jet c 1 x (fun _ => x) J
      rw [scoreCLM_apply_one,unpack_euclideanDisorder]
  | inr i =>
    refine ⟨1,by omega,(fun _ => e i),?_⟩
    intro J
    simp only [actualObservation,jointCLM_apply_inr,gradientCLM_apply,unpack_euclideanDisorder]

lemma value_coordinate_low_order {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (i : Sum (Fin 1) (Fin m)) :
    ∃ k : ℕ,k ≤ 1 ∧ ∃ a : Fin k → Vector N,
      ∀ J : Disorder N P,actualObservation (valueTangentCLM c x e) J i=jet c k x a J := by
  cases i with
  | inl i =>
    refine ⟨0,by omega,(fun i => Fin.elim0 i),?_⟩
    intro J
    simp only [actualObservation,valueTangentCLM_apply_value,unpack_euclideanDisorder]
  | inr i =>
    refine ⟨1,by omega,(fun _ => e i),?_⟩
    intro J
    simp only [actualObservation,valueTangentCLM_apply_gradient,unpack_euclideanDisorder]

lemma cross_covariance_entry {N P : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι)
    (B : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ κ) (i : ι) (j : κ) :
    cov[fun J : Disorder N P => actualObservation A J i,
      fun J : Disorder N P => actualObservation B J j;disorderLaw N P]=
      A (B.adjoint (EuclideanSpace.basisFun κ ℝ j)) i := by
  have h := actual_scalar_cross_covariance ((EuclideanSpace.proj i).comp A) B
    (EuclideanSpace.basisFun κ ℝ j)
  simpa only [actualObservation,EuclideanSpace.basisFun_inner,ContinuousLinearMap.comp_apply,
    EuclideanSpace.proj,PiLp.proj_apply] using h

lemma cross_zero_of_coordinate_covariances {N P : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι)
    (B : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ κ)
    (hcov : ∀ i j,cov[fun J : Disorder N P => actualObservation A J i,
      fun J : Disorder N P => actualObservation B J j;disorderLaw N P]=0) :
    A.comp B.adjoint=0 := by
  have hlin : (A.comp B.adjoint).toLinearMap=0 := by
    apply (EuclideanSpace.basisFun κ ℝ).toBasis.ext
    intro j
    apply PiLp.ext
    intro i
    change A (B.adjoint (EuclideanSpace.basisFun κ ℝ j)) i=0
    rw [← cross_covariance_entry A B i j,hcov]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ ι => L v) hlin

/-- The two genuine mixed observations are orthogonal coefficient subspaces
at zero overlap, proved from actual field jet covariance. -/
lemma orthogonal_jointCLM_cross_zero {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p ≠ 0 → 3 ≤ p.val.val)
    (x y : Vector N) (hxy : inner ℝ x y=0) (e f : Fin m → Vector N) :
    (jointCLM c x e).comp (jointCLM c y f).adjoint=0 := by
  apply cross_zero_of_coordinate_covariances
  intro i j
  obtain ⟨k,hk,a,ha⟩ := joint_coordinate_low_order c x e i
  obtain ⟨l,hl,b,hb⟩ := joint_coordinate_low_order c y f j
  simp_rw [ha,hb]
  exact low_order_jet_covariance_zero hN c hc hdeg x y hxy hk hl a b

lemma orthogonal_valueCLM_cross_zero {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p ≠ 0 → 3 ≤ p.val.val)
    (x y : Vector N) (hxy : inner ℝ x y=0) (e f : Fin m → Vector N) :
    (valueTangentCLM c x e).comp (valueTangentCLM c y f).adjoint=0 := by
  apply cross_zero_of_coordinate_covariances
  intro i j
  obtain ⟨k,hk,a,ha⟩ := value_coordinate_low_order c x e i
  obtain ⟨l,hl,b,hb⟩ := value_coordinate_low_order c y f j
  simp_rw [ha,hb]
  exact low_order_jet_covariance_zero hN c hc hdeg x y hxy hk hl a b

/-- Two actual surjective orthogonal coefficient observations have a genuine
surjective joint observation, by their canonical lifts. -/
lemma orthogonal_prod_surjective {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →L[ℝ] F) (B : E →L[ℝ] G) (hA : Surjective A) (hB : Surjective B)
    (hAB : A.comp B.adjoint=0) : Surjective (A.prod B) := by
  have hBA := orthogonal_observation_symm A B hAB
  intro w
  refine ⟨lift A w.1+lift B w.2,?_⟩
  apply Prod.ext
  · change A (lift A w.1+lift B w.2)=w.1
    rw [map_add,observation_lift_apply A hA,orthogonal_observation_lift_zero A B hAB,add_zero]
  · change B (lift A w.1+lift B w.2)=w.2
    rw [map_add,orthogonal_observation_lift_zero B A hBA,observation_lift_apply B hB,zero_add]

/-- Actual nonpure two-point observation covariance is nonsingular at zero
overlap; this is a proved field property, not a regression input. -/
theorem orthogonal_mixed_pair_surjective {n : ℕ} (μ : FiniteMixture)
    (hdeg : 3 ≤ μ.minDegree) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x y : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (hy : ‖y‖^2=(n+1 : ℕ))
    (hxy : inner ℝ x y=0) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Surjective (pairJointCLM c x y (tangentFrame x hx) (tangentFrame y hy)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  apply orthogonal_prod_surjective
  · exact center_joint_surjective (by omega) μ hQ hnp x hx _ (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)
  · exact center_joint_surjective (by omega) μ hQ hnp y hy _ (tangentFrame_orthonormal y hy) (tangentFrame_tangent y hy)
  · exact orthogonal_jointCLM_cross_zero (by omega) c
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le)
      (center_degree_support hdeg Q) x y hxy _ _

/-- Proper value/tangent observations remain nonsingular for a pure mixture;
no redundant radial coordinate is included. -/
theorem orthogonal_value_pair_surjective {n : ℕ} (μ : FiniteMixture)
    (hdeg : 3 ≤ μ.minDegree) {Q : ℝ} (hQ : 0 < Q)
    (x y : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (hy : ‖y‖^2=(n+1 : ℕ))
    (hxy : inner ℝ x y=0) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Surjective (pairValueCLM c x y (tangentFrame x hx) (tangentFrame y hy)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  apply orthogonal_prod_surjective
  · exact center_valueTangent_surjective (by omega) μ hQ x hx _ (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)
  · exact center_valueTangent_surjective (by omega) μ hQ y hy _ (tangentFrame_orthonormal y hy) (tangentFrame_tangent y hy)
  · exact orthogonal_valueCLM_cross_zero (by omega) c
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le)
      (center_degree_support hdeg Q) x y hxy _ _

end
end SlowEquilibration.SphericalPairRegression
