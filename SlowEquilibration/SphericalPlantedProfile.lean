-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeUniformMean

@[expose] public section

/-! The actual planted latitude mean including its exact coarea entropy.
On compact latitude ranges its upper is the manuscript's literal Psi profile.
The finite-dimensional entropy error is retained and proved to vanish. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def plantedLatitudeMeanProfile (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) : ℝ :=
  plantedLatitudeQuenchedPressure n μ β u e q+
    ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ))*Real.log (1-q^2)

def plantedProfileTrial (μ : FiniteMixture) (β q : ℝ) : ℝ :=
  (β^2*(μ.xi 1+μ.xi q)+q+Real.log (1-q))/2

theorem plantedProfileTrial_eq (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Ico 0 1) :
    (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+Real.log (1-q^2)/2 =
      plantedProfileTrial μ β q := by
  have hp : 0 < 1-q := by linarith [hq.2]
  have hm : 0 < 1+q := by linarith [hq.1]
  have hprod : 1-q^2=(1-q)*(1+q) := by ring
  rw [hprod, Real.log_mul hp.ne' hm.ne']
  unfold plantedProfileTrial
  ring

theorem latitudeEntropyCoefficient_eq {n : ℕ} (hn : 2 ≤ n) :
    ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ)) =
      1/2-3/(2*((n+1 : ℕ) : ℝ)) := by
  rw [Nat.cast_sub hn]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

/-- The exact finite-dimensional entropy correction, with its uniform
compact-latitude error displayed explicitly. -/
theorem plantedLatitudeMeanProfile_le {n : ℕ} (hn : 2 ≤ n)
    (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    {q ρ ε : ℝ} (hρ : ρ ∈ Ioo 0 1) (hq : q ∈ Icc 0 ρ)
    (hmean : plantedLatitudeQuenchedPressure n μ β u e q ≤
      (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+ε) :
    plantedLatitudeMeanProfile n μ β u e q ≤ plantedProfileTrial μ β q+ε+
      (-3*Real.log (1-ρ^2))/(2*((n+1 : ℕ) : ℝ)) := by
  have hq1 : q < 1 := hq.2.trans_lt hρ.2
  have hρarg : 0 < 1-ρ^2 := by nlinarith [hρ.1, hρ.2]
  have harg : 1-ρ^2 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  have hlog : Real.log (1-ρ^2) ≤ Real.log (1-q^2) := Real.log_le_log hρarg harg
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have he : 0 ≤ 3/(2*((n+1 : ℕ) : ℝ)) := by positivity
  have herr := mul_le_mul_of_nonneg_left hlog he
  have htrial := plantedProfileTrial_eq μ β ⟨hq.1,hq1⟩
  unfold plantedLatitudeMeanProfile
  rw [latitudeEntropyCoefficient_eq hn]
  have heq : (-3*Real.log (1-ρ^2))/(2*((n+1 : ℕ) : ℝ)) =
      -(3/(2*((n+1 : ℕ) : ℝ))*Real.log (1-ρ^2)) := by ring
  rw [heq]
  nlinarith

theorem latitudeEntropyError_tendsto (ρ : ℝ) :
    Tendsto (fun n : ℕ => (-3*Real.log (1-ρ^2))/(2*((n+1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (-3*Real.log (1-ρ^2)/2)
  convert hh using 1
  · funext n
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
  · simp only [mul_zero]

/-- The actual mean latitude profile has the manuscript's Psi upper
uniformly on compact positive latitudes at least one half. -/
theorem plantedLatitudeMeanProfile_eventually_uniform_upper (μ : FiniteMixture)
    {β ρ ε : ℝ} (hβ : 0 < β) (hρ : ρ ∈ Ioo (1/2 : ℝ) 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (1/2 : ℝ) ρ, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeMeanProfile n μ β u e q ≤ plantedProfileTrial μ β q+ε := by
  have hsmall := (latitudeEntropyError_tendsto ρ).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [plantedLatitudeQuenchedPressure_eventually_uniform_upper μ hβ (half_pos hε),
    hsmall, eventually_ge_atTop 2] with n hmean hsmall hn
  intro q hq u hu e he
  have hp := plantedLatitudeMeanProfile_le hn μ β u e
    ⟨by linarith [hρ.1],hρ.2⟩ ⟨by linarith [hq.1],hq.2⟩
    (hmean q ⟨hq.1,hq.2.trans hρ.2.le⟩ u hu e he)
  linarith

theorem plantedLatitudeMeanProfile_eventually_uniform_upper_of_even
    (μ : FiniteMixture) {β ρ ε : ℝ} (hβ : 0 < β)
    (heven : ∀ p ∈ μ.coeff.support, Even p) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (0 : ℝ) ρ, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeMeanProfile n μ β u e q ≤ plantedProfileTrial μ β q+ε := by
  have hsmall := (latitudeEntropyError_tendsto ρ).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [plantedLatitudeQuenchedPressure_eventually_uniform_upper_of_even μ hβ heven (half_pos hε),
    hsmall, eventually_ge_atTop 2] with n hmean hsmall hn
  intro q hq u hu e he
  have hp := plantedLatitudeMeanProfile_le hn μ β u e hρ hq
    (hmean q ⟨hq.1,hq.2.trans hρ.2.le⟩ u hu e he)
  linarith

end
end SlowEquilibration.SphericalModel
