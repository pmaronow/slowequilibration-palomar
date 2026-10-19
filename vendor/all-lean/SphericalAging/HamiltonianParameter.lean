module

public import SphericalAging.CutoffSDE

public section

/-! Actual finite-tensor disorder dependence of the manuscript Hamiltonian
and of the smooth cutoff coefficients. These identities and uniform
bounds supply the coefficients for measurable SDE parameter families.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace ContDiff
namespace SphericalAging.HamiltonianParameter
open HardSphereDynamics FiniteModel
set_option maxHeartbeats 1600000
variable {N p : ℕ}

lemma Hamiltonian_add (J K : Disorder N p) :
    Hamiltonian N p (J+K) = fun x => Hamiltonian N p J x + Hamiltonian N p K x := by
  funext x
  simp only [Hamiltonian, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma Hamiltonian_smul (c : ℝ) (J : Disorder N p) :
    Hamiltonian N p (c • J) = c • Hamiltonian N p J := by
  funext x
  simp only [Hamiltonian, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

lemma Hamiltonian_zero : Hamiltonian N p (0 : Disorder N p) = 0 := by
  funext x
  simp [Hamiltonian]

lemma gradient_add (J K : Disorder N p) :
    hamiltonianGradient (J+K) = hamiltonianGradient J + hamiltonianGradient K := by
  funext x
  unfold hamiltonianGradient gradient
  rw [Hamiltonian_add, fderiv_fun_add
    ((Hamiltonian_contDiff J).differentiable (by simp) x)
    ((Hamiltonian_contDiff K).differentiable (by simp) x), map_add]
  rfl

lemma gradient_smul (c : ℝ) (J : Disorder N p) :
    hamiltonianGradient (c • J) = c • hamiltonianGradient J := by
  funext x
  unfold hamiltonianGradient gradient
  rw [Hamiltonian_smul, fderiv_const_smul_field]
  simp only [Pi.smul_apply, map_smul]

lemma gradient_zero : hamiltonianGradient (0 : Disorder N p) = 0 := by
  funext x
  unfold hamiltonianGradient gradient
  rw [Hamiltonian_zero]
  simp

lemma gradient_sum {ι : Type*} (s : Finset ι) (J : ι → Disorder N p) :
    hamiltonianGradient (∑ i ∈ s, J i) = ∑ i ∈ s, hamiltonianGradient (J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, gradient_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, gradient_add, ih]

@[expose] def disorderBasis (I : TensorIndex N p) : Disorder N p := Pi.single I 1

lemma disorder_sum_basis (J : Disorder N p) : ∑ I, J I • disorderBasis I = J := by
  funext K
  simp [disorderBasis, Pi.single_apply]

lemma gradient_sum_basis (J : Disorder N p) :
    hamiltonianGradient J = ∑ I, J I • hamiltonianGradient (disorderBasis I) := by
  calc
    _ = hamiltonianGradient (∑ I, J I • disorderBasis I) := congrArg hamiltonianGradient (disorder_sum_basis J).symm
    _ = ∑ I, hamiltonianGradient (J I • disorderBasis I) := gradient_sum _ _
    _ = _ := Finset.sum_congr rfl (fun I _ => gradient_smul _ _)

/-- The part of the cutoff drift that is linear in a single actual tensor
coupling; the fixed curvature drift is retained separately. -/
@[expose] def couplingDrift (β : ℝ) (R : ℝ) (hR : 0 < R) (I : TensorIndex N p) : State N → State N :=
  fun x => coefficientBump (N := N) R hR x •
    (β • projection x (hamiltonianGradient (disorderBasis I) x))

lemma couplingDrift_contDiff (β : ℝ) (R : ℝ) (hR : 0 < R) (I : TensorIndex N p) :
    ContDiff ℝ ∞ (couplingDrift β R hR I) := by
  have hg : ContDiff ℝ ∞ (hamiltonianGradient (disorderBasis I)) :=
    (hamiltonianGradient_contDiff (disorderBasis I)).of_le (by simp)
  exact (coefficientBump (N := N) R hR).contDiff.smul
    (((contDiff_projection_pair.of_le (by simp)).comp (contDiff_id.prodMk hg)).const_smul β)

lemma couplingDrift_compactSupport (β : ℝ) (R : ℝ) (hR : 0 < R) (I : TensorIndex N p) :
    HasCompactSupport (couplingDrift β R hR I) :=
  (coefficientBump (N := N) R hR).hasCompactSupport.smul_right

lemma projection_sum (x : State N) {ι : Type*} (s : Finset ι) (v : ι → State N) :
    projection x (∑ i ∈ s, v i) = ∑ i ∈ s, projection x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [projection]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, projection_add, ih]

lemma cutoffDrift_vector_affine (β : ℝ) (J : Disorder N p) (R : ℝ) (hR : 0 < R) (x : State N) :
    cutoffCoefficient R hR (hamiltonianDrift β J) x =
      cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) x +
        ∑ I, J I • couplingDrift β R hR I x := by
  have hg := congrFun (gradient_sum_basis J) x
  simp only [Finset.sum_apply, Pi.smul_apply] at hg
  unfold cutoffCoefficient hamiltonianDrift drift
  rw [hg, projection_sum]
  have hp0 : projection x (0 : State N) = 0 := by simp [projection]
  simp only [projection_smul, couplingDrift, Finset.smul_sum, smul_sub,
    gradient_zero, Pi.zero_apply, hp0, smul_zero, zero_sub]
  have heq : (∑ I, (coefficientBump (N := N) R hR x) • β • J I •
      projection x (hamiltonianGradient (disorderBasis I) x)) =
      ∑ I, J I • (coefficientBump (N := N) R hR x) • β •
        projection x (hamiltonianGradient (disorderBasis I) x) := by
    apply Finset.sum_congr rfl
    intro I _
    module
  simp only [heq]
  module

lemma cutoffDrift_vector_sub (β : ℝ) (J K : Disorder N p) (R : ℝ) (hR : 0 < R) (x : State N) :
    cutoffCoefficient R hR (hamiltonianDrift β J) x -
      cutoffCoefficient R hR (hamiltonianDrift β K) x =
        ∑ I, (J I - K I) • couplingDrift β R hR I x := by
  rw [cutoffDrift_vector_affine β J, cutoffDrift_vector_affine β K]
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

lemma couplingDrift_bounded (β : ℝ) (R : ℝ) (hR : 0 < R) (I : TensorIndex N p) :
    ∃ C : ℝ≥0, ∀ x, ‖couplingDrift β R hR I x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (couplingDrift_compactSupport β R hR I).exists_bound_of_continuous
    (couplingDrift_contDiff β R hR I).continuous
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun x => (hC x).trans (le_max_left _ _)⟩

/-- The actual cutoff drift is globally Lipschitz in the finite Gaussian
tensor parameters, uniformly over the entire state space. -/
theorem cutoffDrift_disorder_lipschitz (β : ℝ) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0, ∀ J K : Disorder N p, ∀ x : State N,
      ‖cutoffCoefficient R hR (hamiltonianDrift β J) x -
        cutoffCoefficient R hR (hamiltonianDrift β K) x‖ ≤ C * ‖J-K‖ := by
  have hC : ∀ I : TensorIndex N p, ∃ C : ℝ≥0, ∀ x, ‖couplingDrift β R hR I x‖ ≤ C :=
    couplingDrift_bounded β R hR
  choose C hC using hC
  refine ⟨∑ I, C I, fun J K x => ?_⟩
  rw [cutoffDrift_vector_sub]
  calc
    _ ≤ ∑ I, ‖(J I-K I) • couplingDrift β R hR I x‖ := norm_sum_le _ _
    _ ≤ ∑ I, ‖J-K‖ * (C I : ℝ) := by
      apply Finset.sum_le_sum
      intro I _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm (J-K) I) (hC I x) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [NNReal.coe_sum, ← Finset.mul_sum]; ring

lemma couplingDrift_lipschitz (β : ℝ) (R : ℝ) (hR : 0 < R) (I : TensorIndex N p) :
    ∃ K : ℝ≥0, LipschitzWith K (couplingDrift β R hR I) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (couplingDrift_compactSupport β R hR I)
    (couplingDrift_contDiff β R hR I) (by simp)

/-- Uniform state Lipschitz constants are proved for the actual Hamiltonian
cutoff drift on every bounded disorder set. The noise is independent of
disorder and already has its proved uniform cutoff constant. -/
theorem cutoffDrift_uniform_state_lipschitz (β : ℝ) (R : ℝ) (hR : 0 < R) (A : ℝ≥0) :
    ∃ K : ℝ≥0, ∀ J : Disorder N p, ‖J‖ ≤ A →
      LipschitzWith K (cutoffCoefficient R hR (hamiltonianDrift β J)) := by
  obtain ⟨K0, hK0⟩ := cutoffCoefficient_lipschitz R hR (hamiltonianDrift β (0 : Disorder N p))
    ((contDiff_hamiltonianDrift β (0 : Disorder N p)).of_le (by simp))
  have hKi : ∀ I : TensorIndex N p, ∃ K : ℝ≥0, LipschitzWith K (couplingDrift β R hR I) :=
    couplingDrift_lipschitz β R hR
  choose Ki hKi using hKi
  refine ⟨K0 + A * ∑ I, Ki I, fun J hJ => LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sum]
  have heq : cutoffCoefficient R hR (hamiltonianDrift β J) x -
      cutoffCoefficient R hR (hamiltonianDrift β J) y =
      (cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) x -
        cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) y) +
      ∑ I, J I • (couplingDrift β R hR I x - couplingDrift β R hR I y) := by
    rw [cutoffDrift_vector_affine β J R hR x, cutoffDrift_vector_affine β J R hR y]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [heq]
  calc
    _ ≤ ‖cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) x -
        cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) y‖ +
        ∑ I, ‖J I • (couplingDrift β R hR I x - couplingDrift β R hR I y)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (K0 : ℝ)*‖x-y‖ + ∑ I, (A : ℝ) * ((Ki I : ℝ)*‖x-y‖) := by
      apply add_le_add
      · simpa only [dist_eq_norm] using hK0.dist_le_mul x y
      · apply Finset.sum_le_sum
        intro I _
        rw [norm_smul]
        apply mul_le_mul ((norm_le_pi_norm J I).trans hJ)
          (by simpa only [dist_eq_norm] using (hKi I).dist_le_mul x y) (norm_nonneg _)
          A.coe_nonneg
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

lemma cutoffDrift_joint_continuous (β : ℝ) (R : ℝ) (hR : 0 < R) :
    Continuous (fun q : Disorder N p × State N => cutoffCoefficient R hR (hamiltonianDrift β q.1) q.2) := by
  have heq : (fun q : Disorder N p × State N => cutoffCoefficient R hR (hamiltonianDrift β q.1) q.2) =
      fun q => cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) q.2 +
        ∑ I, q.1 I • couplingDrift β R hR I q.2 := by
    funext q
    exact cutoffDrift_vector_affine β q.1 R hR q.2
  rw [heq]
  apply Continuous.add
  · exact (cutoffCoefficient_contDiff R hR _ ((contDiff_hamiltonianDrift β (0 : Disorder N p)).of_le (by simp))).continuous.comp continuous_snd
  · apply continuous_finsetSum
    intro I _
    exact ((continuous_apply I).comp continuous_fst).smul
      ((couplingDrift_contDiff β R hR I).continuous.comp continuous_snd)

end SphericalAging.HamiltonianParameter
