-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureConditionedHessian
public import SlowEquilibration.SphericalTAPCertificate
public import SlowEquilibration.SphericalBorderedIntrinsicHessian

/-! # Source Lemma 5.14 in an arbitrary complete tangent orthonormal basis

The coordinate frame is a parameter, as in the manuscript.  Every random
matrix and every conditioning kernel below is built from the same original
finite-mixture tensor disorder.  `goeLaw n (n+1) b` has independent upper
entries with variances `b/(n+1)` off the diagonal and `2*b/(n+1)` on it:
this is the manuscript's `sqrt(n*b/(n+1)) * G_n` convention.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTAPPhysicalHessianSource
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open IntrinsicHessianLaw ConditionedIntrinsicHessian PureConditionedHessian
open IntrinsicGradientRegression
open SphericalPairCommonFrame SphericalSequentialRegression SphericalTAPCertificate
open WholeFieldRegression ValueTangentConditioning TwoAtomStationarity
open scoped RealInnerProductSpace ENNReal
set_option maxHeartbeats 500000

/-- The ambient coordinate family underlying any complete tangent basis. -/
def basisFrame {n : ℕ} {x : Vector (n+1)}
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x)) :
    Fin n → Vector (n+1) := fun i => B i

theorem basisFrame_orthonormal {n : ℕ} {x : Vector (n+1)}
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x)) :
    Orthonormal ℝ (basisFrame B) := by
  simpa only [basisFrame, orthonormal_iff_ite, Submodule.coe_inner] using B.orthonormal

theorem basisFrame_tangent {n : ℕ} {x : Vector (n+1)}
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x)) (i : Fin n) :
    inner ℝ (basisFrame B i) x = 0 := by
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (B i).2

/-- The actual intrinsic Hessian matrix in an arbitrary complete tangent basis. -/
def basisIntrinsicMatrix {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (_hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x))
    (J : Disorder (n+1) P) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix B.toBasis B.toBasis (intrinsicHessian (field c J) x).toLinearMap

/-- The radial correction is the genuine radial derivative divided by `N`.
The identity is pathwise, before invoking any Gaussian law or posterior. -/
theorem corrected_basisIntrinsicMatrix_eq_ambient {n P : ℕ}
    (c : Degree P → ℝ) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x))
    (J : Disorder (n+1) P) :
    basisIntrinsicMatrix c x hx B J +
      radialMultiplier (field c J) x • (1 : Matrix (Fin n) (Fin n) ℝ) =
      hessianMatrix c x (basisFrame B) J := by
  rw [basisIntrinsicMatrix,
    intrinsicHessian_toMatrix_basis (by omega : n+1 ≠ 0) c J x hx B]
  exact sub_add_cancel _ _

/-- The manuscript's corrected Hessian has the full finite-`N` GOE law in
every complete tangent basis, without conditioning. -/
theorem corrected_basisIntrinsicMatrix_goeLaw {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    HasLaw (fun J : Disorder (n+1) μ.maxDegree =>
        basisIntrinsicMatrix c x hx B J +
          radialMultiplier (field c J) x • (1 : Matrix (Fin n) (Fin n) ℝ))
      (goeLaw n (n+1) (Q^2 * μ.xi2 Q)) (disorderLaw (n+1) μ.maxDegree) := by
  dsimp only
  have h := center_hessian_matrix_hasLaw (by omega) μ hQ.le x hx
    (basisFrame B) (basisFrame_orthonormal B) (basisFrame_tangent B)
  exact h.congr (Filter.Eventually.of_forall (fun J =>
    corrected_basisIntrinsicMatrix_eq_ambient
      (centerCoefficients (mixtureCoefficients μ) Q) x hx B J))

/-- Literal value, radial jet, and all tangent-gradient coordinates of the
original field.  The first two coordinates are `H_Q(u)` and `K_Q(u)`;
the last coordinate family is the full spherical gradient in basis `B`. -/
def sourceObservations {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x))
    (J : Disorder (n+1) P) : ℝ × ℝ × (Fin n → ℝ) :=
  let z := valueGradient c x (Fin.cons x (basisFrame B)) J;
  (z none, z (some 0), fun i => z (some i.succ))

/-- The observation tuple is literally the field value, radial derivative,
and basis coordinates of the actual surface gradient. -/
theorem sourceObservations_eq_actual {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x))
    (J : Disorder (n+1) P) :
    sourceObservations c x B J =
      (field c J x, jet c 1 x (fun _ => x) J,
        fun i => inner ℝ (basisFrame B i) (surfaceGradient (field c J) x)) := by
  apply Prod.ext
  · change jet c 0 x (fun i => Fin.elim0 i) J = field c J x
    simp only [jet, iteratedFDeriv_zero_apply]
  · apply Prod.ext
    · rfl
    · funext i
      have hi := intrinsicGamma_inner c x (euclideanDisorder J) (B i)
      rw [unpack_euclideanDisorder] at hi
      change inner ℝ (basisFrame B i)
          (intrinsicGamma c x (euclideanDisorder J) : Vector (n+1)) =
        jet c 1 x (fun _ => basisFrame B i) J at hi
      rw [intrinsicGamma_coe (by omega : n+1 ≠ 0) c x hx,
        unpack_euclideanDisorder] at hi
      exact hi.symm

/-- The corrected Hessian is independent of the actual complete
value/radial/tangent-gradient observation tuple, in any tangent basis. -/
theorem corrected_basisIntrinsicMatrix_independent_sourceObservations
    {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    IndepFun
      (fun J : Disorder (n+1) μ.maxDegree =>
        basisIntrinsicMatrix c x hx B J +
          radialMultiplier (field c J) x • (1 : Matrix (Fin n) (Fin n) ℝ))
      (sourceObservations c x B) (disorderLaw (n+1) μ.maxDegree) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let w : Fin (n+1) → Vector (n+1) := Fin.cons x (basisFrame B)
  have hraw := (hessian_independent_valueGradient c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le)
    x (basisFrame B) (basisFrame_tangent B) w).comp
      (symmetricMatrix_measurable n)
      (show Measurable (fun z : Option (Fin (n+1)) → ℝ =>
        (z none, z (some 0), fun i : Fin n => z (some i.succ))) from by fun_prop)
  have heq : (fun J : Disorder (n+1) μ.maxDegree =>
      symmetricMatrix (upperEntries c x (basisFrame B) J)) =
      (fun J => basisIntrinsicMatrix c x hx B J +
        radialMultiplier (field c J) x • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    funext J
    rw [← hessianMatrix_eq_symmetricMatrix]
    exact (corrected_basisIntrinsicMatrix_eq_ambient c x hx B J).symm
  change IndepFun
    (fun J : Disorder (n+1) μ.maxDegree =>
      symmetricMatrix (upperEntries c x (basisFrame B) J))
    (fun J => let z := valueGradient c x w J;
      (z none, z (some 0), fun i : Fin n => z (some i.succ)))
    (disorderLaw (n+1) μ.maxDegree) at hraw
  rw [heq] at hraw
  change IndepFun
    (fun J : Disorder (n+1) μ.maxDegree =>
      basisIntrinsicMatrix c x hx B J +
        radialMultiplier (field c J) x • (1 : Matrix (Fin n) (Fin n) ℝ))
    (fun J =>
      (valueGradient c x w J none, valueGradient c x w J (some 0),
        fun i : Fin n => valueGradient c x w J (some i.succ)))
    (disorderLaw (n+1) μ.maxDegree)
  exact hraw

/-- Any nonpure source mixture, any normalized marks `(e,k)`, and any
complete tangent basis: the true one-point posterior has intrinsic Hessian
law `GOE - k I`.  The posterior fixes value `N*e`, radial jet `N*k`, and
every tangent-gradient coordinate to zero. -/
theorem mixed_basisIntrinsicMatrix_conditional_law {n : ℕ}
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x))
    (z : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let e := basisFrame B
    let a := jointScoreTarget n (((n+1 : ℕ) : ℝ) • z)
    HasLaw (basisIntrinsicMatrix c x hx B)
      ((goeLaw n (n+1) (Q^2 * μ.xi2 Q)).map
        (fun W => W - z 1 • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (coefficientKernel (jointCLM c x e) a) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let e := basisFrame B
  let a := jointScoreTarget n (((n+1 : ℕ) : ℝ) • z)
  have hH := center_conditioned_ambient_hasLaw (by omega) μ hQ.le x hx e
    (basisFrame_orthonormal B) (basisFrame_tangent B) a
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      W - z 1 • 1) := by fun_prop
  have hshift := (hasLaw_map hm.aemeasurable).fun_comp hH
  apply hshift.congr
  filter_upwards [coefficientKernel_observation_ae _
    (center_joint_surjective (by omega) μ hQ hnp x hx e
      (basisFrame_orthonormal B) (basisFrame_tangent B)) a] with J hJ
  have hk := congrArg
    (fun y : EuclideanSpace ℝ (Sum (Fin 2) (Fin n)) => y (Sum.inl 1)) hJ
  change scoreCLM c x (euclideanDisorder J) 1 = a (Sum.inl 1) at hk
  rw [scoreCLM_apply_one, unpack_euclideanDisorder] at hk
  have hmark : jet c 1 x (fun _ => x) J / (n+1 : ℕ) = z 1 := by
    rw [hk]
    change (((n+1 : ℕ) : ℝ) * z 1) / (n+1 : ℕ) = z 1
    field_simp
  change basisIntrinsicMatrix c x hx B J = _
  rw [basisIntrinsicMatrix,
    intrinsicHessian_toMatrix_basis (by omega : n+1 ≠ 0) c J x hx B,
    radialMultiplier_eq_jet, hmark]
  rfl

/-- The pure-model radial mark equals degree times the actual field value,
pathwise for the original tensor sample. -/
theorem pure_radial_score_eq_degree_value {N : ℕ} (p : ℕ)
    (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha) (Q : ℝ)
    (x : Vector N)
    (J : Disorder N (FiniteMixture.pure p hp alpha halpha).maxDegree) :
    let c := centerCoefficients
      (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
    jet c 1 x (fun _ => x) J = (p : ℝ) * field c J x := by
  simpa only [jet, iteratedFDeriv_zero_apply] using
    PureConditionedHessian.pure_radial_jet p hp alpha halpha Q J x

/-- In the pure model the actual Euler identity forces `K=pH`.  Thus the
proper posterior conditions only on value `N*h` and the full tangent
gradient, in any complete tangent basis, and shifts by `-p*h I`. -/
theorem pure_basisIntrinsicMatrix_conditional_law {n : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (B : OrthonormalBasis (Fin n) ℝ (tangentPlane x)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let e := basisFrame B
    HasLaw (basisIntrinsicMatrix c x hx B)
      ((goeLaw n (n+1) (Q^2 * μ.xi2 Q)).map
        (fun W => W - ((p : ℝ) * h) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (coefficientKernel (valueTangentCLM c x e) (valueTarget n h)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let e := basisFrame B
  have hH := valueTangent_conditioned_ambient_hasLaw (by omega) μ hQ.le x hx e
    (basisFrame_orthonormal B) (basisFrame_tangent B) (valueTarget n h)
  have hm : Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      W - ((p : ℝ) * h) • 1) := by fun_prop
  have hshift := (hasLaw_map hm.aemeasurable).fun_comp hH
  apply hshift.congr
  filter_upwards [coefficientKernel_observation_ae _
    (center_valueTangent_surjective (by omega) μ hQ x hx e
      (basisFrame_orthonormal B) (basisFrame_tangent B)) (valueTarget n h)] with J hJ
  have hv := congrArg
    (fun y : EuclideanSpace ℝ (Sum (Fin 1) (Fin n)) => y (Sum.inl 0)) hJ
  change valueTangentCLM c x e (euclideanDisorder J) (Sum.inl 0) =
    valueTarget n h (Sum.inl 0) at hv
  rw [valueTangentCLM_apply_value, unpack_euclideanDisorder] at hv
  have hmark : (p : ℝ) * jet c 0 x (fun i => Fin.elim0 i) J /
      (n+1 : ℕ) = (p : ℝ) * h := by
    rw [hv]
    change (p : ℝ) * (((n+1 : ℕ) : ℝ) * h) / (n+1 : ℕ) = _
    field_simp
  change basisIntrinsicMatrix c x hx B J = _
  rw [basisIntrinsicMatrix,
    intrinsicHessian_toMatrix_basis (by omega : n+1 ≠ 0) c J x hx B,
    radialMultiplier_eq_jet,
    PureConditionedHessian.pure_radial_jet p hp alpha halpha Q J x, hmark]
  rfl

/-- The printed strict-contact square formula, positivity, and the exact
infimum of the source interval `U₀`. -/
theorem certified_hessian_interval_source (μ : FiniteMixture)
    {β x Q : ℝ} (h : Certificate μ β x Q) :
    let g₀ := markK μ β Q - 2 * Real.sqrt (markB μ Q)
    g₀ = (markY β Q - Real.sqrt (markB μ Q)) ^ 2 / markY β Q ∧
      0 < g₀ ∧
      sInf (Ioo (markK μ β Q - g₀/4) (markK μ β Q + g₀/4)) =
        2 * Real.sqrt (markB μ Q) + 3*g₀/4 := by
  dsimp only
  refine ⟨h.edge_margin.2.1, h.edge_margin.2.2, ?_⟩
  have hg := h.edge_margin.2.2
  have hlt : markK μ β Q -
      (markK μ β Q - 2 * Real.sqrt (markB μ Q))/4 <
      markK μ β Q +
        (markK μ β Q - 2 * Real.sqrt (markB μ Q))/4 := by linarith
  rw [csInf_Ioo hlt]
  ring

end SlowEquilibration.SphericalTAPPhysicalHessianSource
