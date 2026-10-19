-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedIntrinsicHessian
public import SlowEquilibration.GaussianRegressionCovariance

/-! Literal trace covariance of the actual full tangent Hessian and its true
covariance contraction under canonical full-coefficient Gaussian regression. -/

@[expose] public section
namespace SlowEquilibration.SphericalHessianTraceCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open GaussianRegressionCovariance SymmetricGaussianCovariance GOEAsymptotics
open OAI.CriticalSK
open scoped BigOperators Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- Every entry of the actual tangent ambient Hessian, as one genuine
coefficient-linear matrix observation in its Frobenius Hilbert space. -/
def hessianGaussianCLM {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] GOEAsymptotics.GaussianMatrix m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => EuclideanSpace ℝ (Fin m))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun j => flatJetCLM c 2 x ![e i,e j]))))

@[simp] lemma hessianGaussianCLM_apply {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P) (i j : Fin m) :
    hessianGaussianCLM c x e g i j=hessianEntry c x e i j (unpackDisorder g) := by
  simp [hessianGaussianCLM,hessianEntry]

lemma hessianGaussianCLM_symmetric {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P) :
    ∀ i j,hessianGaussianCLM c x e g i j=hessianGaussianCLM c x e g j i := by
  intro i j
  simp only [hessianGaussianCLM_apply]
  exact hessianEntry_symm c x e i j _

lemma hessian_trace_eq {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (M : GOEAsymptotics.GaussianMatrix m)
    (hM : ∀ i j,M i j=M j i) (g : EuclideanDisorder N P) :
    Matrix.trace (entries (hessianGaussianCLM c x e g)*entries M)=
      ∑ i,∑ j,M i j*hessianEntry c x e i j (unpackDisorder g) := by
  rw [trace_mul_eq_inner _ M hM]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hessianGaussianCLM_apply,mul_comm]

/-- The genuine exact trace variance of the actual ambient tangent Hessian
is (2 xi''(r)/N) Tr(M²), under the original full tensor disorder law. -/
theorem actual_hessian_trace_variance {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖^2=(N:ℝ)*r) (e : Fin m → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (M : GOEAsymptotics.GaussianMatrix m) (hM : ∀ i j,M i j=M j i) :
    Var[fun J : Disorder N P => ∑ i,∑ j,M i j*hessianEntry c x e i j J;disorderLaw N P]=
      (2*secondCovariance c r/N)*Matrix.trace (entries M*entries M) := by
  let f := fun ij : Fin m × Fin m => fun J : Disorder N P => M ij.1 ij.2*hessianEntry c x e ij.1 ij.2 J
  have hf (ij : Fin m × Fin m) : MemLp (f ij) 2 (disorderLaw N P) :=
    (jet_memLp c 2 x ![e ij.1,e ij.2]).const_mul (M ij.1 ij.2)
  have h := variance_fun_sum hf
  simp only [f,covariance_const_mul_left,covariance_const_mul_right,
    hessianEntry_covariance hN c hc x hx e he htan,Fintype.sum_prod_type] at h
  rw [h,trace_sq_eq_norm_sq M hM]
  have hinner (i j : Fin m) :
      (∑ l,∑ q,M l q*(M i j*(secondCovariance c r/N*
        ((if i=l then 1 else 0)*(if j=q then 1 else 0)+
          (if i=q then 1 else 0)*(if j=l then 1 else 0)))))=
      (secondCovariance c r/N)*(M i j*M i j+M i j*M j i) := by
    simp [add_mul,mul_add,Finset.sum_add_distrib,mul_ite,ite_mul,mul_comm,mul_assoc]
  simp only [hinner,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hM j i]
  ring

/-- The exact same trace law holds under the actual standard Gaussian
flattening; no new disorder model is substituted. -/
theorem hessianGaussianCLM_trace_variance {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖^2=(N:ℝ)*r) (e : Fin m → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (M : GOEAsymptotics.GaussianMatrix m) (hM : ∀ i j,M i j=M j i) :
    Var[fun W => Matrix.trace (entries W*entries M);
      (stdGaussian (EuclideanDisorder N P)).map (hessianGaussianCLM c x e)]=
      (2*secondCovariance c r/N)*Matrix.trace (entries M*entries M) := by
  have hm : Measurable (fun W : GOEAsymptotics.GaussianMatrix m => Matrix.trace (entries W*entries M)) := by
    simp_rw [trace_mul_eq_inner _ M hM]
    fun_prop
  rw [variance_map hm.aemeasurable (hessianGaussianCLM c x e).continuous.measurable.aemeasurable]
  have ht : (fun g => Matrix.trace (entries (hessianGaussianCLM c x e g)*entries M))=
      fun g => ∑ i,∑ j,M i j*hessianEntry c x e i j (unpackDisorder g) := funext (hessian_trace_eq c x e M hM)
  simp only [Function.comp_def]
  rw [ht]
  have hcoeff : Measurable (fun g : EuclideanDisorder N P =>
      ∑ i,∑ j,M i j*hessianEntry c x e i j (unpackDisorder g)) := by
    rw [← ht]
    exact hm.comp (hessianGaussianCLM c x e).continuous.measurable
  have hflat : Measurable (euclideanDisorder (N := N) (P := P)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P)
  have hv := (actual_flattened_gaussian N P).covariance_fun_comp
    (f := fun g => ∑ i,∑ j,M i j*hessianEntry c x e i j (unpackDisorder g))
    (g := fun g => ∑ i,∑ j,M i j*hessianEntry c x e i j (unpackDisorder g))
    hcoeff.aemeasurable hcoeff.aemeasurable
  have hJ : AEMeasurable (fun J : Disorder N P => ∑ i,∑ j,M i j*
      hessianEntry c x e i j (unpackDisorder (euclideanDisorder J))) (disorderLaw N P) := by
    simpa only [Function.comp_def] using (hcoeff.comp hflat).aemeasurable
  rw [covariance_self hJ,covariance_self hcoeff.aemeasurable] at hv
  rw [← hv]
  simpa only [unpack_euclideanDisorder] using actual_hessian_trace_variance hN c hc x hx e he htan M hM

/-- Conditioning on any actual surjective observation, including a pair of
mixed or proper pure critical observations, preserves the genuine covariance
upper bound for the full centered tangent Hessian. -/
theorem conditioned_hessian_trace_variance_bound {N P m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖^2=(N:ℝ)*r) (e : Fin m → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (M : GOEAsymptotics.GaussianMatrix m) (hM : ∀ i j,M i j=M j i) :
    Var[fun W => Matrix.trace (entries W*entries M);centeredLaw A (hessianGaussianCLM c x e)] ≤
      (2*secondCovariance c r/N)*Matrix.trace (entries M*entries M) :=
  (centered_matrix_trace_variance_le A hA (hessianGaussianCLM c x e) M hM).trans_eq
    (hessianGaussianCLM_trace_variance hN c hc x hx e he htan M hM)

end
end SlowEquilibration.SphericalHessianTraceCovariance
