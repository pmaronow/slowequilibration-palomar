-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCapMass

@[expose] public section

/-! Actual Gibbs masses as ratios of restricted partition integrals.
The normalization step in Section 13 is proved with its literal cap, core
and collar exponents; no abstract probability masses are substituted. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def partitionOn {N : ℕ} (β : ℝ) (H : Vector N → ℝ) (B : Set (Vector N)) : ℝ :=
  ∫ x in B, Real.exp (β*H x) ∂sphereLaw N

theorem partitionOn_nonneg {N : ℕ} (β : ℝ) (H : Vector N → ℝ) (B : Set (Vector N)) :
    0 ≤ partitionOn β H B := integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem gibbsLaw_real_eq_partitionOn_div {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {B : Set (Vector N)} (hB : MeasurableSet B) :
    (gibbsLaw N β H).real B = partitionOn β H B/partition N β H := by
  calc
    _ = ∫ x, B.indicator (fun _ : Vector N => (1 : ℝ)) x ∂gibbsLaw N β H := by
      rw [integral_indicator hB, integral_const]
      simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.real,
        smul_eq_mul, mul_one]
    _ = ∫ x, gibbsDensity N β H x*B.indicator (fun _ => (1 : ℝ)) x ∂sphereLaw N :=
      integral_gibbsLaw hN β hH _
    _ = ∫ x, B.indicator (fun x => Real.exp (β*H x)/partition N β H) x ∂sphereLaw N := by
      apply integral_congr_ae
      exact .of_forall fun x => by
        by_cases hx : x ∈ B <;> simp [hx, gibbsDensity]
    _ = _ := by rw [integral_indicator hB, integral_div]; rfl

theorem partition_bounds_of_pressure_tolerance {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) {F δ : ℝ}
    (hp : |Real.log (partition N β H)/(N : ℝ)-F| ≤ δ) :
    Real.exp ((N : ℝ)*(F-δ)) ≤ partition N β H ∧
      partition N β H ≤ Real.exp ((N : ℝ)*(F+δ)) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hZ : 0 < partition N β H := partition_pos hN β hH
  obtain ⟨hlo,hhi⟩ := abs_le.mp hp
  have hl : (N : ℝ)*(F-δ) ≤ Real.log (partition N β H) := by
    have hh : F-δ ≤ Real.log (partition N β H)/(N : ℝ) := by linarith
    have hh' := (le_div_iff₀ hN0).mp hh
    linarith
  have hu : Real.log (partition N β H) ≤ (N : ℝ)*(F+δ) := by
    have hh : Real.log (partition N β H)/(N : ℝ) ≤ F+δ := by linarith
    have hh' := (div_le_iff₀ hN0).mp hh
    linarith
  constructor
  · simpa only [Real.exp_log hZ] using Real.exp_le_exp.mpr hl
  · simpa only [Real.exp_log hZ] using Real.exp_le_exp.mpr hu

/-- Exact upper mass normalization used for caps and collars in prop:pr-good. -/
theorem gibbsLaw_mass_le_of_partition_upper {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {B : Set (Vector N)} (hB : MeasurableSet B)
    {F J δ : ℝ} (hp : |Real.log (partition N β H)/(N : ℝ)-F| ≤ δ)
    (hrestricted : partitionOn β H B ≤ Real.exp ((N : ℝ)*(F-J+δ))) :
    (gibbsLaw N β H).real B ≤ Real.exp (-(N : ℝ)*(J-2*δ)) := by
  rw [gibbsLaw_real_eq_partitionOn_div hN β hH hB]
  have hZ := partition_pos hN β hH
  have hz := (partition_bounds_of_pressure_tolerance hN β hH hp).1
  calc
    _ ≤ Real.exp ((N : ℝ)*(F-J+δ))/partition N β H :=
      div_le_div_of_nonneg_right hrestricted hZ.le
    _ ≤ Real.exp ((N : ℝ)*(F-J+δ))/Real.exp ((N : ℝ)*(F-δ)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hz
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- Exact lower mass normalization used for the core band in prop:pr-good. -/
theorem gibbsLaw_mass_ge_of_partition_lower {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {B : Set (Vector N)} (hB : MeasurableSet B)
    {F J δ : ℝ} (hp : |Real.log (partition N β H)/(N : ℝ)-F| ≤ δ)
    (hrestricted : Real.exp ((N : ℝ)*(F-J-δ)) ≤ partitionOn β H B) :
    Real.exp (-(N : ℝ)*(J+2*δ)) ≤ (gibbsLaw N β H).real B := by
  rw [gibbsLaw_real_eq_partitionOn_div hN β hH hB]
  have hZ := partition_pos hN β hH
  have hz := (partition_bounds_of_pressure_tolerance hN β hH hp).2
  calc
    _ = Real.exp ((N : ℝ)*(F-J-δ))/Real.exp ((N : ℝ)*(F+δ)) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp ((N : ℝ)*(F-J-δ))/partition N β H :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hZ hz
    _ ≤ _ := div_le_div_of_nonneg_right hrestricted hZ.le

def coreBand {N : ℕ} (u : Vector N) (q w : ℝ) : Set (Vector N) :=
  {x | |overlap x u-q| ≤ w}

def collar {N : ℕ} (u : Vector N) (q₁ q₂ : ℝ) : Set (Vector N) :=
  {x | overlap x u ∈ Icc q₁ q₂}

theorem coreBand_measurable {N : ℕ} (u : Vector N) (q w : ℝ) :
    MeasurableSet (coreBand u q w) := by
  exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet

theorem collar_measurable {N : ℕ} (u : Vector N) (q₁ q₂ : ℝ) :
    MeasurableSet (collar u q₁ q₂) := by
  exact measurableSet_Icc.preimage (by unfold overlap; fun_prop)

/-- The exact simultaneous cap/core/collar normalization in the manuscript,
for the actual Gibbs density and actual restricted partition functions. -/
theorem gibbsLaw_cap_core_collar_bounds {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (u : Vector N)
    {F J G δ q₁ q₂ q w : ℝ}
    (hp : |Real.log (partition N β H)/(N : ℝ)-F| ≤ δ)
    (hcap : partitionOn β H (cap u q₁) ≤ Real.exp ((N : ℝ)*(F-J+δ)))
    (hcore : Real.exp ((N : ℝ)*(F-J-δ)) ≤ partitionOn β H (coreBand u q w))
    (hcollar : partitionOn β H (collar u q₁ q₂) ≤ Real.exp ((N : ℝ)*(F-J-G+δ))) :
    (gibbsLaw N β H).real (cap u q₁) ≤ Real.exp (-(N : ℝ)*(J-2*δ)) ∧
      Real.exp (-(N : ℝ)*(J+2*δ)) ≤ (gibbsLaw N β H).real (coreBand u q w) ∧
      (gibbsLaw N β H).real (collar u q₁ q₂) ≤ Real.exp (-(N : ℝ)*(J+G-2*δ)) := by
  refine ⟨gibbsLaw_mass_le_of_partition_upper hN β hH (cap_measurable u q₁) hp hcap,
    gibbsLaw_mass_ge_of_partition_lower hN β hH (coreBand_measurable u q w) hp hcore, ?_⟩
  have hc : partitionOn β H (collar u q₁ q₂) ≤ Real.exp ((N : ℝ)*(F-(J+G)+δ)) := by
    have heq : F-J-G+δ=F-(J+G)+δ := by ring
    simpa only [heq] using hcollar
  exact gibbsLaw_mass_le_of_partition_upper hN β hH (collar_measurable u q₁ q₂) hp hc

end
end SlowEquilibration.SphericalModel
