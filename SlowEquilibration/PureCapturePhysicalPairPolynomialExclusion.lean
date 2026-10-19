-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
public import SlowEquilibration.PureCapturePhysicalFullArrayCubeSupport

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
open SlowEquilibration.PureCapturePhysicalFullArrayCubeSupport
open scoped Topology

namespace SlowEquilibration.PureCapturePhysicalPairPolynomialExclusion

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

def pairPolynomial (Q r : ℝ) : ℝ := r ^ 2 * (r ^ 2 - Q ^ 2) ^ 2

theorem pairPolynomial_nonneg (Q r : ℝ) : 0 ≤ pairPolynomial Q r := by
  unfold pairPolynomial
  positivity

theorem pairPolynomial_expand (Q r : ℝ) :
    pairPolynomial Q r = r ^ 6 - 2 * Q ^ 2 * r ^ 4 + Q ^ 4 * r ^ 2 := by
  unfold pairPolynomial
  ring

/-- At every strictly positive overlap away from Q, one fixed neighborhood
has a strictly positive sixth-degree polynomial gap. -/
theorem exists_pairPolynomial_gap {Q q : ℝ}
    (hQ : 0 < Q) (hq : 0 < q) (hne : q ≠ Q) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧
      ∀ r : ℝ, |r - q| < ρ → δ ≤ pairPolynomial Q r := by
  let ρ : ℝ := min (q / 2) (|q - Q| / 2)
  have hqQ : 0 < |q - Q| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  let δ : ℝ := (q / 2) ^ 2 * (|q - Q| / 2) ^ 2 * (q / 2 + Q) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨ρ, δ, hρ, hδ, ?_⟩
  intro r hr
  have hrq : |r - q| < q / 2 := lt_of_lt_of_le hr (min_le_left _ _)
  have hrQ : |r - q| < |q - Q| / 2 := lt_of_lt_of_le hr (min_le_right _ _)
  have hrpos : q / 2 ≤ r := by
    have hh := (abs_lt.mp hrq).1
    linarith
  have hdist : |q - Q| / 2 ≤ |r - Q| := by
    have hh : |q - Q| ≤ |q - r| + |r - Q| := by
      calc
        |q - Q| = |(q - r) + (r - Q)| := by ring
        _ ≤ |q - r| + |r - Q| := abs_add_le _ _
    rw [abs_sub_comm q r] at hh
    linarith
  have hsum : q / 2 + Q ≤ r + Q := by linarith
  have hs1 : (q / 2) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - q / 2)]
  have hs2 : (|q - Q| / 2) ^ 2 ≤ (r - Q) ^ 2 := by
    nlinarith [sq_abs (r - Q)]
  have hs3 : (q / 2 + Q) ^ 2 ≤ (r + Q) ^ 2 := by
    nlinarith [sq_nonneg (r + Q - (q / 2 + Q))]
  have hprod : δ ≤ r ^ 2 * (r - Q) ^ 2 * (r + Q) ^ 2 := by
    dsimp [δ]
    apply mul_le_mul (mul_le_mul hs1 hs2 (sq_nonneg _) (sq_nonneg _)) hs3
      (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    δ ≤ r ^ 2 * (r - Q) ^ 2 * (r + Q) ^ 2 := hprod
    _ = pairPolynomial Q r := by unfold pairPolynomial; ring

/-- An elementary probability bound for a nonnegative observable that has
a fixed positive gap on a measurable event. -/
theorem event_mass_mul_le_integral {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (E : Set X) (hE : MeasurableSet E) (g : X → ℝ)
    (hg : Integrable g ν) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hg0 : ∀ᵐ z ∂ν, 0 ≤ g z)
    (hgap : ∀ᵐ z ∂ν, z ∈ E → δ ≤ g z) :
    δ * ν.real E ≤ ∫ z, g z ∂ν := by
  have hi : Integrable (E.indicator (fun _ : X => δ)) ν :=
    (integrable_const δ).indicator hE
  have hle : E.indicator (fun _ : X => δ) ≤ᵐ[ν] g := by
    filter_upwards [hg0, hgap] with z hz hgz
    by_cases h : z ∈ E
    · simpa only [Set.indicator_of_mem h] using hgz h
    · simpa [Set.indicator, h] using hz
  have hh := integral_mono_ae hi hg hle
  rw [integral_indicator_const δ hE, smul_eq_mul] at hh
  simpa only [mul_comm] using hh

private theorem pairPower_integrable
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ c ∂ν, c ∈ fullOverlapCube 2) (p : ℕ) :
    Integrable (fun c : FullOverlapCoordinates 2 => (c 0 1) ^ p) ν := by
  have hc : Continuous (fun c : FullOverlapCoordinates 2 => (c 0 1) ^ p) :=
    (((continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2))).pow p)
  have hi := hc.continuousOn.integrableOn_compact (fullOverlapCube_compact 2) (μ := ν)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hcube] using hi

private theorem pairPolynomial_integrable
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ c ∂ν, c ∈ fullOverlapCube 2) (Q : ℝ) :
    Integrable (fun c : FullOverlapCoordinates 2 => pairPolynomial Q (c 0 1)) ν := by
  have hc : Continuous (fun c : FullOverlapCoordinates 2 => pairPolynomial Q (c 0 1)) := by
    unfold pairPolynomial
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact (fullOverlapCube_compact 2) (μ := ν)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hcube] using hi

theorem pairPolynomial_integral_eq_moments
    (ν : Measure (FullOverlapCoordinates 2)) [IsProbabilityMeasure ν]
    (hcube : ∀ᵐ c ∂ν, c ∈ fullOverlapCube 2) (Q : ℝ) :
    (∫ c, pairPolynomial Q (c 0 1) ∂ν) =
      (∫ c, (c 0 1) ^ 6 ∂ν) - 2 * Q ^ 2 *
      (∫ c, (c 0 1) ^ 4 ∂ν) + Q ^ 4 *
      (∫ c, (c 0 1) ^ 2 ∂ν) := by
  have h6 := pairPower_integrable ν hcube 6
  have h4 := pairPower_integrable ν hcube 4
  have h2 := pairPower_integrable ν hcube 2
  simp_rw [pairPolynomial_expand]
  have hA : Integrable (fun c : FullOverlapCoordinates 2 =>
      (c 0 1) ^ 6 - 2 * Q ^ 2 * (c 0 1) ^ 4) ν :=
    h6.sub (h4.const_mul (2 * Q ^ 2))
  have hB : Integrable (fun c : FullOverlapCoordinates 2 =>
      Q ^ 4 * (c 0 1) ^ 2) ν := h2.const_mul (Q ^ 4)
  change (∫ c, ((fun d : FullOverlapCoordinates 2 =>
    (d 0 1) ^ 6 - 2 * Q ^ 2 * (d 0 1) ^ 4) c) +
      ((fun d : FullOverlapCoordinates 2 => Q ^ 4 * (d 0 1) ^ 2) c) ∂ν) = _
  rw [integral_add hA hB, integral_sub h6 (h4.const_mul (2 * Q ^ 2)),
    integral_const_mul, integral_const_mul]

theorem physical_pairPolynomial_integral_tendsto_zero_of_moments
    (μ : FiniteMixture) (β x Q : ℝ)
    (h2 : Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1) ^ 2 ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ 2)))
    (h4 : Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1) ^ 4 ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ 4)))
    (h6 : Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1) ^ 6 ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ 6))) :
    Tendsto (fun n : ℕ =>
      ∫ c, pairPolynomial Q (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 0) := by
  have hh := (h6.sub (h4.const_mul (2 * Q ^ 2))).add
    (h2.const_mul (Q ^ 4))
  have hv : (1 - x) * Q ^ 6 - 2 * Q ^ 2 * ((1 - x) * Q ^ 4) +
      Q ^ 4 * ((1 - x) * Q ^ 2) = 0 := by ring
  rw [hv] at hh
  convert hh using 1
  ext n
  exact pairPolynomial_integral_eq_moments _
    (physicalFullOverlapLaw_cube_ae μ β) Q

/-- Three actual physical even pair moments suffice to exclude every
positive overlap except Q. This gives k=2, stronger than the manuscript's
generalized-TAP route when these moment premises are available. -/
theorem physical_pair_exclusion_of_three_even_moments
    (μ : FiniteMixture) (β x Q : ℝ) (hQ : 0 < Q)
    (h2 : Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1) ^ 2 ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ 2)))
    (h4 : Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1) ^ 4 ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ 4)))
    (h6 : Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1) ^ 6 ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1 - x) * Q ^ 6))) :
    ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun n : ℕ =>
          (physicalFullOverlapLaw (n := n) (m := 2) μ β :
            Measure (FullOverlapCoordinates 2)) (fullEquilateralEvent 2 q ρ))
          atTop (𝓝 0) := by
  intro q hq hne
  obtain ⟨ρ, δ, hρ, hδ, hgap⟩ := exists_pairPolynomial_gap hQ hq.1 hne
  refine ⟨ρ, hρ, ?_⟩
  have hpoly := physical_pairPolynomial_integral_tendsto_zero_of_moments μ β x Q h2 h4 h6
  let E := fullEquilateralEvent 2 q ρ
  have hreal : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)).real E) atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ =>
        (∫ c, pairPolynomial Q (c 0 1) ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) / δ)
        atTop (𝓝 0) := by
      simpa only [zero_div] using hpoly.div_const δ
    apply squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hup
    let ν : Measure (FullOverlapCoordinates 2) := physicalFullOverlapLaw (n := n) (m := 2) μ β
    have hE : MeasurableSet E := (fullEquilateralEvent_open 2 q ρ).measurableSet
    have hg := pairPolynomial_integrable ν (physicalFullOverlapLaw_cube_ae μ β) Q
    have hbound := event_mass_mul_le_integral ν E hE _ hg δ hδ.le
      (.of_forall fun c => pairPolynomial_nonneg Q (c 0 1))
      (.of_forall fun c hc => hgap (c 0 1) (hc 0 1 (by decide)))
    exact (le_div_iff₀ hδ).2 (by simpa [ν, mul_comm] using hbound)
  have hENN := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  have hEq (n : ℕ) : ENNReal.ofReal
      ((physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)).real E) =
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)) E :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  simp only [Function.comp_def, ENNReal.ofReal_zero] at hENN
  simpa only [hEq, E] using hENN

end
end SlowEquilibration.PureCapturePhysicalPairPolynomialExclusion
