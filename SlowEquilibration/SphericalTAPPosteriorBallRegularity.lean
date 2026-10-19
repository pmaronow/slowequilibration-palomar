-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorLandscapeConcentration
public import SlowEquilibration.SphericalModel

@[expose] public section

/-! Uniform ambient derivative bounds on the original field under the
actual Gaussian coefficient posterior. This is the deterministic bridge
from the proved posterior tensor-norm tail to source Lemma 12.3. -/

namespace SlowEquilibration.SphericalTAPPosteriorBallRegularity
noncomputable section
open SlowEquilibration.SphericalModel
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SphericalAging.GaussianLandscape
open NormalizedPairObservations PairObservationTargets
set_option autoImplicit false

/-- The second derivative of the original field along any smooth path is
controlled by its actual ambient first and second jets. -/
theorem field_curve_second_deriv_norm_bound
    {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (σ : ℝ → Vector N) (a : ℝ) (hσ : ContDiffAt ℝ 2 σ a) :
    |iteratedDeriv 2 (fun t => field c J (σ t)) a| ≤
      ‖iteratedFDeriv ℝ 2 (field c J) (σ a)‖ * ‖deriv σ a‖^2 +
        ‖fderiv ℝ (field c J) (σ a)‖ * ‖iteratedDeriv 2 σ a‖ := by
  have hchain := iteratedDeriv_vcomp_two
    ((field_contDiff c J).of_le (by norm_num)).contDiffAt hσ
  change iteratedDeriv 2 (fun t => field c J (σ t)) a = _ at hchain
  rw [hchain]
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖iteratedFDeriv ℝ 2 (field c J) (σ a)
        (fun _ => deriv σ a)‖ +
        ‖fderiv ℝ (field c J) (σ a) (iteratedDeriv 2 σ a)‖ := norm_add_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 (field c J) (σ a)‖ * ‖deriv σ a‖^2 +
        ‖fderiv ℝ (field c J) (σ a)‖ * ‖iteratedDeriv 2 σ a‖ := by
      apply add_le_add
      · simpa only [Fin.prod_univ_two, Fin.isValue, pow_two] using
          (iteratedFDeriv ℝ 2 (field c J) (σ a)).le_opNorm
            (fun _ => deriv σ a)
      · exact (fderiv ℝ (field c J) (σ a)).le_opNorm _

def posteriorDerivativeConstant {P : ℕ} (c : Degree P → ℝ) (K : ℝ) : ℝ :=
  1 + ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ)^3 *
    (2*((p.val.val : ℝ)+1)+1+K)

theorem posteriorDerivativeConstant_pos {P : ℕ} (c : Degree P → ℝ)
    {K : ℝ} (hK : 0 ≤ K) : 0 < posteriorDerivativeConstant c K := by
  unfold posteriorDerivativeConstant
  have hsum : 0 ≤ ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ)^3 *
      (2*((p.val.val : ℝ)+1)+1+K) := by
    apply Finset.sum_nonneg
    intro p hp
    positivity
  linarith

/-- Every derivative order through three obeys the same source-dimensional
scaling on the whole physical ball, whenever the actual coefficient sample
lies in the previously constructed posterior tensor regularity event. -/
theorem field_posteriorOrderedRegularity_derivatives
    {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) {K : ℝ}
    (hJ : J ∈ sourcePosteriorOrderedRegularity K)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ))
    (order : ℕ) (horder : order ≤ 3) :
    Real.sqrt (N : ℝ)^order *
      ‖iteratedFDeriv ℝ order (field c J) x‖ ≤
        posteriorDerivativeConstant c K * (N : ℝ) := by
  have hsum : (∑ p : Degree P, Real.sqrt (c p) *
      (Nat.descFactorial p.val.val order : ℝ) *
      landscapeNorm N p.val.val (J p)) ≤ posteriorDerivativeConstant c K := by
    apply le_trans (b := ∑ p : Degree P, Real.sqrt (c p) *
      (p.val.val : ℝ)^3 * (2*((p.val.val : ℝ)+1)+1+K))
    · apply Finset.sum_le_sum
      intro p hp
      have hfac : (Nat.descFactorial p.val.val order : ℝ) ≤
          (p.val.val : ℝ)^3 := by
        exact_mod_cast (Nat.descFactorial_le_pow p.val.val order).trans
          (pow_le_pow_right' (show 1 ≤ p.val.val by omega) horder)
      have hreg : landscapeNorm N p.val.val (J p) ≤
          2*((p.val.val : ℝ)+1)+1+K := hJ p
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
      · exact hreg
      · exact landscapeNorm_nonnegative _ _ _
      · positivity
    · unfold posteriorDerivativeConstant
      linarith
  exact (field_iteratedFDeriv_ball_bound hN c J x hx order).trans
    ((mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)).trans_eq (by ring))

theorem field_posteriorOrderedRegularity_ball_bounds
    {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) {K : ℝ}
    (hJ : J ∈ sourcePosteriorOrderedRegularity K)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) :
    |field c J x| ≤ posteriorDerivativeConstant c K * (N : ℝ) ∧
    ‖gradient (field c J) x‖ ≤
      posteriorDerivativeConstant c K * Real.sqrt (N : ℝ) ∧
    ‖iteratedFDeriv ℝ 2 (field c J) x‖ ≤ posteriorDerivativeConstant c K ∧
    ‖iteratedFDeriv ℝ 3 (field c J) x‖ ≤
      posteriorDerivativeConstant c K / Real.sqrt (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq : Real.sqrt (N : ℝ)^2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hzero := field_posteriorOrderedRegularity_derivatives hN c J hJ x hx 0 (by norm_num)
  have hone := field_posteriorOrderedRegularity_derivatives hN c J hJ x hx 1 (by norm_num)
  have htwo := field_posteriorOrderedRegularity_derivatives hN c J hJ x hx 2 (by norm_num)
  have hthree := field_posteriorOrderedRegularity_derivatives hN c J hJ x hx 3 (by norm_num)
  have hgrad : ‖gradient (field c J) x‖ =
      ‖iteratedFDeriv ℝ 1 (field c J) x‖ := by
    rw [gradient, LinearIsometryEquiv.norm_map, norm_iteratedFDeriv_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hzero
  · rw [hgrad]
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ posteriorDerivativeConstant c K * (N : ℝ) := by simpa only [pow_one] using hone
      _ = Real.sqrt (N : ℝ) *
          (posteriorDerivativeConstant c K * Real.sqrt (N : ℝ)) := by
        calc
          _ = posteriorDerivativeConstant c K * Real.sqrt (N : ℝ)^2 :=
            congrArg (fun z => posteriorDerivativeConstant c K * z) hsq.symm
          _ = _ := by ring
  · rw [hsq] at htwo
    rw [mul_comm (posteriorDerivativeConstant c K) (N : ℝ)] at htwo
    exact (mul_le_mul_iff_right₀ hNr).mp htwo
  · apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hNr).mp
    calc
      _ = Real.sqrt (N : ℝ)^3 *
          ‖iteratedFDeriv ℝ 3 (field c J) x‖ := by
        calc
          _ = Real.sqrt (N : ℝ)^2 *
              (‖iteratedFDeriv ℝ 3 (field c J) x‖ * Real.sqrt (N : ℝ)) :=
            congrArg (fun z => z *
              (‖iteratedFDeriv ℝ 3 (field c J) x‖ * Real.sqrt (N : ℝ))) hsq.symm
          _ = _ := by ring
      _ ≤ posteriorDerivativeConstant c K * (N : ℝ) := hthree
      _ = _ := by ring

theorem field_posterior_curve_second_bound
    {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) {K : ℝ} (hK : 0 ≤ K)
    (hJ : J ∈ sourcePosteriorOrderedRegularity K)
    (σ : ℝ → Vector N) (a : ℝ) (hσ : ContDiffAt ℝ 2 σ a)
    (hball : ‖σ a‖ ≤ Real.sqrt (N : ℝ))
    {A B : ℝ}
    (hspeed : ‖deriv σ a‖ ≤ A * Real.sqrt (N : ℝ))
    (hacc : ‖iteratedDeriv 2 σ a‖ ≤ B * Real.sqrt (N : ℝ)) :
    |iteratedDeriv 2 (fun t => field c J (σ t)) a| ≤
      posteriorDerivativeConstant c K * (A^2+B) * (N : ℝ) := by
  let C := posteriorDerivativeConstant c K
  have hC : 0 ≤ C := (posteriorDerivativeConstant_pos c hK).le
  obtain ⟨_, hgrad, hH, _⟩ :=
    field_posteriorOrderedRegularity_ball_bounds hN c J hJ (σ a) hball
  have hfirst : ‖fderiv ℝ (field c J) (σ a)‖ ≤ C * Real.sqrt (N : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hgrad
  have hsq : Real.sqrt (N : ℝ)^2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  calc
    _ ≤ ‖iteratedFDeriv ℝ 2 (field c J) (σ a)‖ * ‖deriv σ a‖^2 +
        ‖fderiv ℝ (field c J) (σ a)‖ * ‖iteratedDeriv 2 σ a‖ :=
      field_curve_second_deriv_norm_bound c J σ a hσ
    _ ≤ C * (A*Real.sqrt (N : ℝ))^2 +
        (C*Real.sqrt (N : ℝ)) * (B*Real.sqrt (N : ℝ)) := by
      gcongr
    _ = C*(A^2+B)*Real.sqrt (N : ℝ)^2 := by ring
    _ = C*(A^2+B)*(N : ℝ) := by rw [hsq]

/-- Compact-mark mixed critical conditioning retains a single measurable
event on which the *original* Hamiltonian and its ambient derivatives obey
the physical scaling throughout the entire ball. The event's conditioned
failure probability is exponentially small with a dimension-free constant. -/
theorem source_mixed_posterior_ball_regular
    (μ : FiniteMixture) {Q M : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (N m : ℕ), 0 < N → ∀ (x : Vector N), ‖x‖^2 = (N : ℝ) →
      ∀ (e : Fin m → Vector N), Orthonormal ℝ e →
        (∀ i, inner ℝ (e i) x = 0) →
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        let good := sourcePosteriorOrderedRegularity (N := N) (P := μ.maxDegree) K
        MeasurableSet good ∧
        (coefficientKernel (singleMixedObservation c x e)
          (mixedPointTarget N m h k)).real goodᶜ ≤
          (Fintype.card (Degree μ.maxDegree) : ℝ) * Real.exp (-(N : ℝ)/2) ∧
        ∀ J ∈ good, ∀ y : Vector N, ‖y‖ ≤ Real.sqrt (N : ℝ) →
          |field (mixtureCoefficients μ) J y| ≤ C * (N : ℝ) ∧
          ‖gradient (field (mixtureCoefficients μ) J) y‖ ≤
            C * Real.sqrt (N : ℝ) ∧
          ‖iteratedFDeriv ℝ 2 (field (mixtureCoefficients μ) J) y‖ ≤ C ∧
          ‖iteratedFDeriv ℝ 3 (field (mixtureCoefficients μ) J) y‖ ≤
            C / Real.sqrt (N : ℝ) := by
  obtain ⟨K, hK, htail⟩ := source_mixed_posterior_orderedRegularity μ hQ hnp hM
  let C := posteriorDerivativeConstant (mixtureCoefficients μ) K
  refine ⟨K, C, hK, posteriorDerivativeConstant_pos _ hK.le, ?_⟩
  intro N m hN x hx e he htan h k hh hk
  dsimp only
  refine ⟨sourcePosteriorOrderedRegularity_measurable N μ.maxDegree K,
    htail N m hN x hx e he htan h k hh hk, ?_⟩
  intro J hJ y hy
  exact field_posteriorOrderedRegularity_ball_bounds (by omega)
    (mixtureCoefficients μ) J hJ y hy

/-- The proper-pure value and zero-tangent-gradient posterior has the same
uniform physical-ball regularity, with the correct value-only observation. -/
theorem source_value_posterior_ball_regular
    (μ : FiniteMixture) {Q M : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (N m : ℕ), 0 < N → ∀ (x : Vector N), ‖x‖^2 = (N : ℝ) →
      ∀ (e : Fin m → Vector N), Orthonormal ℝ e →
        (∀ i, inner ℝ (e i) x = 0) →
      ∀ (h : ℝ), |h| ≤ M →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        let good := sourcePosteriorOrderedRegularity (N := N) (P := μ.maxDegree) K
        MeasurableSet good ∧
        (coefficientKernel (singleValueObservation c x e)
          (valuePointTarget N m h)).real goodᶜ ≤
          (Fintype.card (Degree μ.maxDegree) : ℝ) * Real.exp (-(N : ℝ)/2) ∧
        ∀ J ∈ good, ∀ y : Vector N, ‖y‖ ≤ Real.sqrt (N : ℝ) →
          |field (mixtureCoefficients μ) J y| ≤ C * (N : ℝ) ∧
          ‖gradient (field (mixtureCoefficients μ) J) y‖ ≤
            C * Real.sqrt (N : ℝ) ∧
          ‖iteratedFDeriv ℝ 2 (field (mixtureCoefficients μ) J) y‖ ≤ C ∧
          ‖iteratedFDeriv ℝ 3 (field (mixtureCoefficients μ) J) y‖ ≤
            C / Real.sqrt (N : ℝ) := by
  obtain ⟨K, hK, htail⟩ := source_value_posterior_orderedRegularity μ hQ hM
  let C := posteriorDerivativeConstant (mixtureCoefficients μ) K
  refine ⟨K, C, hK, posteriorDerivativeConstant_pos _ hK.le, ?_⟩
  intro N m hN x hx e he htan h hh
  dsimp only
  refine ⟨sourcePosteriorOrderedRegularity_measurable N μ.maxDegree K,
    htail N m hN x hx e he htan h hh, ?_⟩
  intro J hJ y hy
  exact field_posteriorOrderedRegularity_ball_bounds (by omega)
    (mixtureCoefficients μ) J hJ y hy

end
end SlowEquilibration.SphericalTAPPosteriorBallRegularity
