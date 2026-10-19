-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeAverages

@[expose] public section

/-! # Literal weighted latitude error from actual bad-mass tails -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def amplitudeLatitudeBadRegion (x : Vector (n+1)) (q ε : ℝ) : Set (Vector (n+1)) :=
  {u | ε ≤ |overlap x u-q|}

theorem amplitudeLatitudeBadRegion_measurable (x : Vector (n+1)) (q ε : ℝ) :
    MeasurableSet (amplitudeLatitudeBadRegion x q ε) := by
  apply measurableSet_le measurable_const
  apply Continuous.measurable
  unfold overlap
  fun_prop

def amplitudeLatitudeBadMass (μ : FiniteMixture) (β J δ q₁ q₂ q ε : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) : ℝ :=
  (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D).real (amplitudeLatitudeBadRegion x q ε)

theorem amplitudeLatitudeBadMass_measurable (μ : FiniteMixture) (β J δ q₁ q₂ q ε : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Measurable (amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s) := by
  have h := ((amplitudeWeightedKernel μ β J δ q₁ q₂ x e p₀ s).measurable_coe
    (amplitudeLatitudeBadRegion_measurable x q ε)).ennreal_toReal
  change Measurable (fun D : BankDisorder n μ =>
    ((amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D) (amplitudeLatitudeBadRegion x q ε)).toReal)
  simpa only [amplitudeWeightedKernel_apply] using h

theorem amplitudeLatitudeBadMass_nonneg (μ : FiniteMixture) (β J δ q₁ q₂ q ε : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    0 ≤ amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s D := measureReal_nonneg

theorem amplitudeLatitudeBadMass_le_one (μ : FiniteMixture) (β J δ q₁ q₂ q ε : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s D ≤ 1 := by
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  exact measureReal_le_one

theorem amplitudeLatitudeBadMass_integrable (μ : FiniteMixture) (β J δ q₁ q₂ q ε : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Integrable (amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s) (bankLaw n μ) :=
  Integrable.of_bound (amplitudeLatitudeBadMass_measurable μ β J δ q₁ q₂ q ε x e p₀ s).aestronglyMeasurable 1
    (.of_forall fun D => by
      rw [Real.norm_eq_abs,abs_of_nonneg (amplitudeLatitudeBadMass_nonneg μ β J δ q₁ q₂ q ε x e p₀ s D)]
      exact amplitudeLatitudeBadMass_le_one μ β J δ q₁ q₂ q ε x e p₀ s D)

theorem amplitudeLatitudeSingleError_le_badMass (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    {q ε : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hε : 0 ≤ ε)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s (fun u => |overlap x u-q|) D ≤
      ε+2*amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s D := by
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  let E := amplitudeLatitudeBadRegion x q ε
  have hE : MeasurableSet E := amplitudeLatitudeBadRegion_measurable x q ε
  have hφ : Continuous (fun u : Vector (n+1) => |overlap x u-q|) := by unfold overlap;fun_prop
  have hi := amplitudeSingleObservable_integrable μ β J δ q₁ q₂ x e p₀ s _ hφ D
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) W := (integrable_const 1).indicator hE
  have hh := integral_mono_ae hi ((integrable_const ε).add (hI.const_mul 2)) (by
    filter_upwards [weightedLaw_support (by omega : 1≤n+1) β
      (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x] with u hu
    have hr := overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) x u hx hu
    have hBound : |overlap x u-q| ≤ 2 := abs_le.mpr ⟨by linarith [hr.1,hq.2],by linarith [hr.2,hq.1]⟩
    simp only [Pi.add_apply]
    by_cases he : u ∈ E
    · rw [Set.indicator_of_mem he]
      change |overlap x u-q| ≤ ε+2*1
      linarith
    · rw [Set.indicator_of_notMem he]
      change |overlap x u-q| ≤ ε+2*0
      change ¬ε ≤ |overlap x u-q| at he
      simpa only [mul_zero,add_zero] using (not_le.mp he).le)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const ε) (hI.const_mul 2),integral_const_mul,
    integral_indicator hE,setIntegral_const] at hh
  change (∫ u,|overlap x u-q| ∂W) ≤ ε+2*W.real E
  simpa only [integral_const,probReal_univ,one_smul,smul_eq_mul,mul_one,one_mul] using hh

/-- A genuine bounded latitude bad mass has expectation at most a threshold
plus its literal bank bad-event probability. -/
theorem amplitudeLatitudeBadMass_expectation_le_threshold (μ : FiniteMixture)
    (β J δ q₁ q₂ q ε : ℝ) (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ D,amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s D ∂bankLaw n μ) ≤
      θ+(bankLaw n μ).real {D | θ ≤ amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s D} := by
  let f := amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s
  let E : Set (BankDisorder n μ) := {D | θ ≤ f D}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (amplitudeLatitudeBadMass_measurable μ β J δ q₁ q₂ q ε x e p₀ s)
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) (bankLaw n μ) :=
    (integrable_const (1:ℝ)).indicator hE
  have hh := integral_mono (amplitudeLatitudeBadMass_integrable μ β J δ q₁ q₂ q ε x e p₀ s)
    ((integrable_const θ).add hI) (fun D => by
      simp only [Pi.add_apply]
      by_cases he : D ∈ E
      · rw [Set.indicator_of_mem he]
        exact (amplitudeLatitudeBadMass_le_one μ β J δ q₁ q₂ q ε x e p₀ s D).trans (by linarith)
      · rw [Set.indicator_of_notMem he,add_zero]
        exact (not_le.mp he).le)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const θ) hI,integral_indicator hE,setIntegral_const] at hh
  simpa only [integral_const,probReal_univ,one_smul,smul_eq_mul,mul_one,one_mul,E,f] using hh

theorem amplitudeLatitudeL1_le_badMassTail (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    {q ε θ : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    amplitudeLatitudeL1 μ β J δ q₁ q₂ q x e p₀ s ≤ ε+2*θ+
      2*(bankLaw n μ).real {D | θ ≤ amplitudeLatitudeBadMass μ β J δ q₁ q₂ q ε x e p₀ s D} := by
  have hφ : Continuous (fun u : Vector (n+1) => |overlap x u-q|) := by unfold overlap;fun_prop
  have hi := amplitudeSingleAverage_integrable μ β J δ q₁ q₂ x e p₀ s _ hφ
  have hM := amplitudeLatitudeBadMass_integrable μ β J δ q₁ q₂ q ε x e p₀ s
  have hh := integral_mono hi ((integrable_const ε).add (hM.const_mul 2))
    (fun D => amplitudeLatitudeSingleError_le_badMass μ β J δ q₁ q₂ hq hε x hx e p₀ s D)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const ε) (hM.const_mul 2),integral_const_mul] at hh
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have hTail := amplitudeLatitudeBadMass_expectation_le_threshold μ β J δ q₁ q₂ q ε x e p₀ s hθ
  change amplitudeLatitudeL1 μ β J δ q₁ q₂ q x e p₀ s ≤ _ at hh
  linarith

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
