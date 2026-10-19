-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDynamics
public import SphericalAging.HamiltonianParameter

/-! Actual finite mixed tensor parameter dependence of cutoff coefficients.
The finite-basis argument adapts the pinned all-lean
`SphericalAging/HamiltonianParameter.lean` (Apache-2.0) to the actual dependent
product of all allowed degrees. Both parities and zero mixture coefficients
are retained. No uniform coefficient bound is assumed. -/

@[expose] public section
namespace SlowEquilibration.SphericalDynamics

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal BigOperators InnerProductSpace ContDiff
open SphericalAging SphericalModel HardSphereDynamics CutoffSDE
open SphericalAging.HamiltonianParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable {N : ℕ}

abbrev MixedCoefficientIndex (μ : FiniteMixture) :=
  Sigma (fun p : Degree μ.maxDegree => FiniteModel.TensorIndex N p.val.val)

def mixedDisorderBasis (μ : FiniteMixture) (a : MixedCoefficientIndex (N := N) μ) :
    Disorder N μ.maxDegree := Pi.single a.1 (Pi.single a.2 1)

lemma mixed_disorder_sum_basis (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    (∑ a : MixedCoefficientIndex (N := N) μ,J a.1 a.2 • mixedDisorderBasis μ a)=J := by
  classical
  funext p I
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mixedDisorderBasis]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single p]
  · simp only [Pi.single_eq_same]
    simp [Pi.single_apply]
  · intro q hq hqp
    have hpq : p≠q := hqp.symm
    simp only [Pi.single_eq_of_ne hpq,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  · simp

lemma mixedGradient_add (μ : FiniteMixture) (J K : Disorder N μ.maxDegree) :
    mixedGradient μ (J+K)=mixedGradient μ J+mixedGradient μ K := by
  funext x
  have hf : fieldOfMixture μ (J+K)=fun x => fieldOfMixture μ J x+fieldOfMixture μ K x := by
    funext y
    simpa only [fieldCLM_apply,fieldOfMixture] using (fieldCLM (mixtureCoefficients μ) y).map_add J K
  unfold mixedGradient gradient
  rw [hf,fderiv_fun_add ((fieldOfMixture_contDiff μ J).differentiable (by simp) x)
    ((fieldOfMixture_contDiff μ K).differentiable (by simp) x),map_add]
  rfl

lemma mixedGradient_smul (μ : FiniteMixture) (r : ℝ) (J : Disorder N μ.maxDegree) :
    mixedGradient μ (r • J)=r • mixedGradient μ J := by
  funext x
  have hf : fieldOfMixture μ (r • J)=r • fieldOfMixture μ J := by
    funext y
    simpa only [fieldCLM_apply,fieldOfMixture,Pi.smul_apply,smul_eq_mul] using (fieldCLM (mixtureCoefficients μ) y).map_smul r J
  unfold mixedGradient gradient
  rw [hf,fderiv_const_smul_field]
  simp only [Pi.smul_apply,map_smul]

lemma mixedGradient_zero (μ : FiniteMixture) : mixedGradient μ (0 : Disorder N μ.maxDegree)=0 := by
  funext x
  have hf : fieldOfMixture μ (0 : Disorder N μ.maxDegree)=0 := by
    funext y
    simpa only [fieldCLM_apply,fieldOfMixture,Pi.zero_apply] using (fieldCLM (mixtureCoefficients μ) y).map_zero
  unfold mixedGradient gradient
  rw [hf]
  simp

lemma mixedGradient_sum (μ : FiniteMixture) {ι : Type*} (s : Finset ι)
    (J : ι → Disorder N μ.maxDegree) :
    mixedGradient μ (∑ i∈s,J i)=∑ i∈s,mixedGradient μ (J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,mixedGradient_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,mixedGradient_add,ih]

lemma mixedGradient_sum_basis (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    mixedGradient μ J=∑ a : MixedCoefficientIndex (N := N) μ,
      J a.1 a.2 • mixedGradient μ (mixedDisorderBasis μ a) := by
  calc
    _=mixedGradient μ (∑ a : MixedCoefficientIndex (N := N) μ,J a.1 a.2 • mixedDisorderBasis μ a) :=
      congrArg (mixedGradient μ) (mixed_disorder_sum_basis μ J).symm
    _=∑ a : MixedCoefficientIndex (N := N) μ,mixedGradient μ (J a.1 a.2 • mixedDisorderBasis μ a) :=
      mixedGradient_sum μ _ _
    _=_ := Finset.sum_congr rfl (fun a _ => mixedGradient_smul μ _ _)

/-- A literal cutoff coupling of one actual ordered tensor coefficient. -/
def mixedCouplingDrift (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R)
    (a : MixedCoefficientIndex (N := N) μ) : State N → State N :=
  fun x => coefficientBump (N := N) R hR x •
    (β • projection x (mixedGradient μ (mixedDisorderBasis μ a) x))

lemma mixedCouplingDrift_contDiff (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R)
    (a : MixedCoefficientIndex (N := N) μ) : ContDiff ℝ ∞ (mixedCouplingDrift μ β R hR a) := by
  have hg : ContDiff ℝ ∞ (mixedGradient μ (mixedDisorderBasis μ a)) :=
    (mixedGradient_contDiff μ _).of_le (by simp)
  exact (coefficientBump (N := N) R hR).contDiff.smul
    (((contDiff_projection_pair.of_le (by simp)).comp (contDiff_id.prodMk hg)).const_smul β)

lemma mixedCouplingDrift_compactSupport (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R)
    (a : MixedCoefficientIndex (N := N) μ) : HasCompactSupport (mixedCouplingDrift μ β R hR a) :=
  (coefficientBump (N := N) R hR).hasCompactSupport.smul_right

lemma mixed_cutoffDrift_vector_affine (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (R : ℝ) (hR : 0 < R) (x : State N) :
    cutoffCoefficient R hR (drift β (mixedGradient μ J)) x=
      cutoffCoefficient R hR (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree))) x+
        ∑ a : MixedCoefficientIndex (N := N) μ,J a.1 a.2 • mixedCouplingDrift μ β R hR a x := by
  have hg := congrFun (mixedGradient_sum_basis μ J) x
  simp only [Finset.sum_apply,Pi.smul_apply] at hg
  unfold cutoffCoefficient drift
  rw [hg,projection_sum]
  have hp0 : projection x (0 : State N)=0 := by simp [projection]
  simp only [projection_smul,mixedCouplingDrift,Finset.smul_sum,smul_sub,
    mixedGradient_zero,Pi.zero_apply,hp0,smul_zero,zero_sub]
  have he : (∑ a : MixedCoefficientIndex (N := N) μ,
      coefficientBump (N := N) R hR x • β • J a.1 a.2 •
        projection x (mixedGradient μ (mixedDisorderBasis μ a) x))=
      ∑ a : MixedCoefficientIndex (N := N) μ,J a.1 a.2 •
        coefficientBump (N := N) R hR x • β •
          projection x (mixedGradient μ (mixedDisorderBasis μ a) x) := by
    apply Finset.sum_congr rfl
    intro a _
    module
  simp only [he]
  module

lemma mixed_cutoffDrift_vector_sub (μ : FiniteMixture) (β : ℝ)
    (J K : Disorder N μ.maxDegree) (R : ℝ) (hR : 0 < R) (x : State N) :
    cutoffCoefficient R hR (drift β (mixedGradient μ J)) x-
      cutoffCoefficient R hR (drift β (mixedGradient μ K)) x=
        ∑ a : MixedCoefficientIndex (N := N) μ,(J a.1 a.2-K a.1 a.2) • mixedCouplingDrift μ β R hR a x := by
  rw [mixed_cutoffDrift_vector_affine μ β J,mixed_cutoffDrift_vector_affine μ β K]
  simp only [sub_smul,Finset.sum_sub_distrib]
  abel

lemma mixedCouplingDrift_bounded (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R)
    (a : MixedCoefficientIndex (N := N) μ) :
    ∃ C : ℝ≥0,∀ x,‖mixedCouplingDrift μ β R hR a x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (mixedCouplingDrift_compactSupport μ β R hR a).exists_bound_of_continuous
    (mixedCouplingDrift_contDiff μ β R hR a).continuous
  exact ⟨⟨max C 0,le_max_right _ _⟩,fun x => (hC x).trans (le_max_left _ _)⟩

lemma mixed_coefficient_norm_le (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (a : MixedCoefficientIndex (N := N) μ) : ‖J a.1 a.2‖ ≤ ‖J‖ :=
  (norm_le_pi_norm (J a.1) a.2).trans (norm_le_pi_norm J a.1)

/-- The actual mixed vector drift is globally Lipschitz in its finite
ordered tensor disorder, uniformly over the whole state space. -/
theorem mixed_cutoffDrift_vector_disorder_lipschitz (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0,∀ J K : Disorder N μ.maxDegree,∀ x : State N,
      ‖cutoffCoefficient R hR (drift β (mixedGradient μ J)) x-
        cutoffCoefficient R hR (drift β (mixedGradient μ K)) x‖ ≤ C*‖J-K‖ := by
  have hC : ∀ a : MixedCoefficientIndex (N := N) μ,∃ C : ℝ≥0,
      ∀ x,‖mixedCouplingDrift μ β R hR a x‖ ≤ C := mixedCouplingDrift_bounded μ β R hR
  choose C hC using hC
  refine ⟨∑ a,C a,fun J K x => ?_⟩
  rw [mixed_cutoffDrift_vector_sub]
  calc
    _ ≤ ∑ a : MixedCoefficientIndex (N := N) μ,
      ‖(J a.1 a.2-K a.1 a.2) • mixedCouplingDrift μ β R hR a x‖ := norm_sum_le _ _
    _ ≤ ∑ a : MixedCoefficientIndex (N := N) μ,‖J-K‖*(C a : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul]
      exact mul_le_mul (mixed_coefficient_norm_le μ (J-K) a) (hC a x)
        (norm_nonneg _) (norm_nonneg _)
    _=_ := by rw [NNReal.coe_sum,← Finset.mul_sum];ring

/-- Scalar-coordinate API for the genuine parameterized Picard coefficients. -/
theorem mixed_cutoffDrift_disorder_lipschitz (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0,∀ J K : Disorder N μ.maxDegree,∀ i : Fin N,∀ x : State N,
      ‖cutoffDrift β (mixedGradient μ J) R hR i x-
        cutoffDrift β (mixedGradient μ K) R hR i x‖ ≤ C*‖J-K‖ := by
  obtain ⟨C,hC⟩ := mixed_cutoffDrift_vector_disorder_lipschitz (N := N) μ β R hR
  refine ⟨C,fun J K i x => ?_⟩
  have hc := (CutoffSDE.coordinate_lipschitz i).dist_le_mul
    (cutoffCoefficient R hR (drift β (mixedGradient μ J)) x)
    (cutoffCoefficient R hR (drift β (mixedGradient μ K)) x)
  simp only [dist_eq_norm,NNReal.coe_one,one_mul] at hc
  exact hc.trans (hC J K x)

lemma mixedCouplingDrift_lipschitz (μ : FiniteMixture) (β R : ℝ) (hR : 0 < R)
    (a : MixedCoefficientIndex (N := N) μ) :
    ∃ K : ℝ≥0,LipschitzWith K (mixedCouplingDrift μ β R hR a) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (mixedCouplingDrift_compactSupport μ β R hR a)
    (mixedCouplingDrift_contDiff μ β R hR a) (by simp)

/-- A uniform state Lipschitz constant on every bounded actual mixed tensor
set; all finite degree blocks are included explicitly. -/
theorem mixed_cutoffDrift_vector_uniform_state_lipschitz (μ : FiniteMixture)
    (β R : ℝ) (hR : 0 < R) (A : ℝ≥0) :
    ∃ K : ℝ≥0,∀ J : Disorder N μ.maxDegree,‖J‖ ≤ A →
      LipschitzWith K (cutoffCoefficient R hR (drift β (mixedGradient μ J))) := by
  obtain ⟨K0,hK0⟩ := cutoffCoefficient_lipschitz R hR
    (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree)))
    ((contDiff_drift β _ (mixedGradient_contDiff μ _)).of_le (by simp))
  have hKi : ∀ a : MixedCoefficientIndex (N := N) μ,∃ K : ℝ≥0,
      LipschitzWith K (mixedCouplingDrift μ β R hR a) := mixedCouplingDrift_lipschitz μ β R hR
  choose Ki hKi using hKi
  refine ⟨K0+A*∑ a,Ki a,fun J hJ => LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_sum]
  have heq : cutoffCoefficient R hR (drift β (mixedGradient μ J)) x-
      cutoffCoefficient R hR (drift β (mixedGradient μ J)) y=
      (cutoffCoefficient R hR (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree))) x-
        cutoffCoefficient R hR (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree))) y)+
      ∑ a : MixedCoefficientIndex (N := N) μ,J a.1 a.2 •
        (mixedCouplingDrift μ β R hR a x-mixedCouplingDrift μ β R hR a y) := by
    rw [mixed_cutoffDrift_vector_affine μ β J R hR x,mixed_cutoffDrift_vector_affine μ β J R hR y]
    simp only [smul_sub,Finset.sum_sub_distrib]
    abel
  rw [heq]
  calc
    _ ≤ ‖cutoffCoefficient R hR (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree))) x-
        cutoffCoefficient R hR (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree))) y‖+
      ∑ a : MixedCoefficientIndex (N := N) μ,
        ‖J a.1 a.2 • (mixedCouplingDrift μ β R hR a x-mixedCouplingDrift μ β R hR a y)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (K0:ℝ)*‖x-y‖+∑ a : MixedCoefficientIndex (N := N) μ,(A:ℝ)*((Ki a:ℝ)*‖x-y‖) := by
      apply add_le_add
      · simpa only [dist_eq_norm] using hK0.dist_le_mul x y
      · apply Finset.sum_le_sum
        intro a _
        rw [norm_smul]
        exact mul_le_mul ((mixed_coefficient_norm_le μ J a).trans hJ)
          (by simpa only [dist_eq_norm] using (hKi a).dist_le_mul x y)
          (norm_nonneg _) A.coe_nonneg
    _=_ := by rw [← Finset.mul_sum,← Finset.sum_mul];ring

/-- The exact coordinate-wise uniform state bound requested by the generic
Picard family construction. -/
theorem mixed_cutoffDrift_uniform_state_lipschitz (μ : FiniteMixture)
    (β R : ℝ) (hR : 0 < R) (A : ℝ≥0) :
    ∃ K : ℝ≥0,∀ J : Disorder N μ.maxDegree,‖J‖ ≤ A →
      ∀ i : Fin N,LipschitzWith K (cutoffDrift β (mixedGradient μ J) R hR i) := by
  obtain ⟨K,hK⟩ := mixed_cutoffDrift_vector_uniform_state_lipschitz (N := N) μ β R hR A
  refine ⟨K,fun J hJ i => ?_⟩
  change LipschitzWith K (fun x => (cutoffCoefficient R hR (drift β (mixedGradient μ J)) x) i)
  simpa only [one_mul,Function.comp_def] using (CutoffSDE.coordinate_lipschitz i).comp (hK J hJ)

/-- Actual joint continuity in the full mixed disorder and state. -/
theorem mixed_cutoffDrift_vector_joint_continuous (μ : FiniteMixture)
    (β R : ℝ) (hR : 0 < R) :
    Continuous (fun q : Disorder N μ.maxDegree × State N =>
      cutoffCoefficient R hR (drift β (mixedGradient μ q.1)) q.2) := by
  have he : (fun q : Disorder N μ.maxDegree × State N =>
      cutoffCoefficient R hR (drift β (mixedGradient μ q.1)) q.2)=fun q =>
      cutoffCoefficient R hR (drift β (mixedGradient μ (0 : Disorder N μ.maxDegree))) q.2+
        ∑ a : MixedCoefficientIndex (N := N) μ,q.1 a.1 a.2 • mixedCouplingDrift μ β R hR a q.2 := by
    funext q
    exact mixed_cutoffDrift_vector_affine μ β q.1 R hR q.2
  rw [he]
  apply Continuous.add
  · exact (cutoffCoefficient_contDiff R hR _
      ((contDiff_drift β _ (mixedGradient_contDiff μ _)).of_le (by simp))).continuous.comp continuous_snd
  · apply continuous_finsetSum
    intro a _
    have hcoef : Continuous (fun q : Disorder N μ.maxDegree × State N => q.1 a.1 a.2) := by
      fun_prop
    exact hcoef.smul ((mixedCouplingDrift_contDiff μ β R hR a).continuous.comp continuous_snd)

end
end SlowEquilibration.SphericalDynamics
