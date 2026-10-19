-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairResidualValueDensity
public import SlowEquilibration.PairObservationTargets

/-! Actual pair-value density comparison with the product of its literal
one-point densities, including the physical sqrt N height targets. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedObservationCoercivity PairObservationTargets
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma referenceValuePair_density_eq_actual_marginals {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) 
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (w : ValuePairSpace) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    realObservationDensity (referenceValuePair μ Q) w=
      realObservationDensity (normalizedValue c x) w.fst*realObservationDensity (normalizedValue c y) w.snd := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hRef : Surjective (referenceValue μ Q) :=
    SphericalSequentialRegression.center_value_surjective μ hQ referencePoint (by simpa using referencePoint_norm_sq)
  have hxGram : gram (normalizedValue c x)=gram (referenceValue μ Q) :=
    normalizedValue_gram_eq_reference hN μ hQ.le x hx
  have hyGram : gram (normalizedValue c y)=gram (referenceValue μ Q) :=
    normalizedValue_gram_eq_reference hN μ hQ.le y hy
  have hA : Surjective (normalizedValue c x) :=
    surjective_of_gram_det_ne_zero _ (by rw [hxGram];exact (gram_det_pos _ hRef).ne')
  have hB : Surjective (normalizedValue c y) :=
    surjective_of_gram_det_ne_zero _ (by rw [hyGram];exact (gram_det_pos _ hRef).ne')
  rw [referenceValuePair,realObservationDensity_independentPair _ hRef _ hRef,
    ← realObservationDensity_eq_of_gram _ hA _ hRef hxGram,
    ← realObservationDensity_eq_of_gram _ hB _ hRef hyGram]

def valueScorePairTarget (N : ℕ) (h1 h2 : ℝ) : ValuePairSpace :=
  WithLp.toLp 2 (Real.sqrt (N:ℝ)*h1,Real.sqrt (N:ℝ)*h2)

lemma valueScorePairTarget_norm_le (N : ℕ) {M h1 h2 : ℝ}
    (hh1 : |h1| ≤ M) (hh2 : |h2| ≤ M) :
    ‖valueScorePairTarget N h1 h2‖ ≤ 2*M*Real.sqrt (N:ℝ) := by
  have hfst:=WithLp.norm_fst_le _
    (hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin 0)) (valuePairTarget N 0 h1 h2))
  rw [LinearIsometryEquiv.norm_map] at hfst
  exact hfst.trans (valuePairTarget_norm_le N 0 hh1 hh2)

end
end SlowEquilibration.NormalizedPairObservations

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The actual conditional value density divided by both actual marginal
value densities has the source O(N|overlap|^d) error on every bounded mark box. -/
theorem uniform_physical_pair_value_density (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ h1 h2 : ℝ,|h1| ≤ M → |h2| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let w:=valueScorePairTarget N h1 h2
      |Real.log (realObservationDensity (residualPairValue c x y e f) w /
        (realObservationDensity (normalizedValue c x) w.fst*realObservationDensity (normalizedValue c y) w.snd))| ≤
          K*(N:ℝ)*|overlap x y|^μ.minDegree := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=uniform_residual_pair_value_density μ hQ hdeg
  refine ⟨ρ0,K*(1+4*M^2),hρ0,by positivity,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ h1 h2 hh1 hh2
  let w:=valueScorePairTarget N h1 h2
  have h:= (hall N m hN x y hx hy e f he hf htanx htany hρ).2 w
  rw [referenceValuePair_density_eq_actual_marginals hN μ hQ x y hx hy w] at h
  have hn : ‖w‖ ≤ 2*M*Real.sqrt (N:ℝ) := valueScorePairTarget_norm_le N hh1 hh2
  have hs : ‖w‖^2 ≤ 4*M^2*(N:ℝ) := by
    have hh:=(sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*M*Real.sqrt (N:ℝ))).mpr hn
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)] at hh
    norm_num at hh
    exact hh
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  apply h.trans
  have hh:=mul_le_mul_of_nonneg_left (show 1+‖w‖^2 ≤ (1+4*M^2)*(N:ℝ) by nlinarith) hK.le
  exact mul_le_mul_of_nonneg_right (by convert hh using 1; ring) (by positivity)

end
end SlowEquilibration.PairObservationSmallOverlap
