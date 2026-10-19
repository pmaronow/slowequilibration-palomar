-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaCalculus

@[expose] public section

/-! # Genuine fresh-replica factorization

Appending one independent sample to the literal finite-product Gibbs law
turns a product of expectations into a single (n+1)-replica expectation.
The construction is the actual finite-product measurable equivalence.
-/

namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {V H : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]

def initialReplicas {n : ℕ} (σ : Fin (n+1) → V) : Fin n → V := fun j => σ j.castSucc

theorem initialReplicas_measurable (n : ℕ) : Measurable (initialReplicas (V := V) (n := n)) :=
  Measurable.of_eval fun j => measurable_pi_apply j.castSucc

theorem integral_pi_append (G : Measure V) [IsProbabilityMeasure G] (n : ℕ)
    (F : (Fin n → V) → ℝ) (g : V → ℝ) :
    (∫ σ,F (initialReplicas σ)*g (σ (Fin.last n)) ∂Measure.pi (fun _ : Fin (n+1) => G)) =
      (∫ σ,F σ ∂Measure.pi (fun _ : Fin n => G))*(∫ z,g z ∂G) := by
  calc
    _ = ∫ x : V × (Fin n → V),g x.1*F x.2 ∂G.prod (Measure.pi (fun _ : Fin n => G)) := by
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => G) (Fin.last n)).symm).integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Equiv.coe_fn_mk,Fin.insertNth_last',Fin.snoc_last]
      congr 1
      ext x
      have hs : initialReplicas (Fin.snoc x.2 x.1)=x.2 := funext fun j => Fin.snoc_castSucc _ _ j
      rw [hs];ring
    _ = _ := by rw [integral_prod_mul]; ring

theorem replicaExpectation_append (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (w : H)
    (F : (Fin n → V) → ℝ) (g : V → ℝ) :
    replicaExpectation ν L (n+1) (fun σ => F (initialReplicas σ)*g (σ (Fin.last n))) w =
      replicaExpectation ν L n F w*GaussianSpinInterpolation.expectation ν g L w := by
  let _ := GaussianSpinInterpolation.gibbsMeasure_probability ν L hL hb w
  rw [replicaExpectation,replicaExpectation,
    integral_pi_append,GaussianSpinInterpolation.integral_gibbsMeasure ν L hL hb]

theorem replicaExpectation_coordinate (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (j : Fin n) (w : H)
    (g : V → ℝ) (hg : Measurable g) :
    replicaExpectation ν L n (fun σ => g (σ j)) w =
      GaussianSpinInterpolation.expectation ν g L w := by
  let _ := GaussianSpinInterpolation.gibbsMeasure_probability ν L hL hb w
  rw [replicaExpectation,integral_comp_eval hg.aestronglyMeasurable,
    GaussianSpinInterpolation.integral_gibbsMeasure ν L hL hb]

theorem replicaObservable_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (f : (Fin n → V) → ℝ)
    (hf : Measurable f) (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w : H) :
    Integrable f (Measure.pi (fun _ : Fin n => GaussianSpinInterpolation.gibbsMeasure ν L w)) := by
  let _ := GaussianSpinInterpolation.gibbsMeasure_probability ν L hL hb w
  have hac : Measure.pi (fun _ : Fin n => GaussianSpinInterpolation.gibbsMeasure ν L w) ≪ replicaBase ν n := by
    rw [← replica_gibbsMeasure_eq_pi ν L hL hK hb n w]
    exact GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous _ _ _
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact (hfb.mono fun σ hσ => by simpa only [Real.norm_eq_abs] using hσ).filter_mono hac.ae_le

theorem replicaExpectation_finiteSum {κ : Type*} [Fintype κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (f : κ → (Fin n → V) → ℝ)
    (hf : ∀ j,Measurable (f j)) (hfb : ∀ j,∀ᵐ σ ∂replicaBase ν n, |f j σ| ≤ C) (w : H) :
    replicaExpectation ν L n (fun σ => ∑ j,f j σ) w = ∑ j,replicaExpectation ν L n (f j) w := by
  unfold replicaExpectation
  exact integral_finsetSum Finset.univ fun j _ => replicaObservable_integrable ν L hL hK hb n _ (hf j) (hfb j) w

theorem replicaExpectation_linear_apply (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (w d : H) :
    replicaExpectation ν L n (fun σ => replicaLinear L n σ d) w =
      (n : ℝ)*GaussianSpinInterpolation.expectation ν (fun z => L z d) L w := by
  let G := GaussianSpinInterpolation.gibbsMeasure ν L w
  let _ := GaussianSpinInterpolation.gibbsMeasure_probability ν L hL hb w
  have hg : Measurable (fun z => L z d) :=
    (ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL
  have hi : Integrable (fun z => L z d) G := by
    apply Integrable.of_bound hg.aestronglyMeasurable (K*‖d‖)
    have hbd := hb.mono fun z hz =>
      ((L z).le_opNorm d).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg d))
    exact hbd.filter_mono (GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν L w).ae_le
  have hi' (j : Fin n) : Integrable (fun σ : Fin n → V => L (σ j) d)
      (Measure.pi (fun _ : Fin n => G)) :=
    integrable_comp_eval (μ := fun _ : Fin n => G) (i := j) (f := fun z => L z d) hi
  unfold replicaExpectation
  simp only [replicaLinear,sum_apply]
  rw [integral_finsetSum Finset.univ (fun j _ => hi' j)]
  calc
    _ = ∑ _j : Fin n,GaussianSpinInterpolation.expectation ν (fun z => L z d) L w := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_comp_eval (μ := fun _ : Fin n => G) (i := j)
        (f := fun z => L z d) hg.aestronglyMeasurable]
      exact GaussianSpinInterpolation.integral_gibbsMeasure ν L hL hb w _
    _ = _ := by simp

end
end SlowEquilibration.GaussianReplicaCalculus
