module

public import FourPapersCommon.FilteredItoContinuous
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-!
# Adapted continuous modifications without a completed filtration

A continuous modification of an adapted process need not itself be adapted
to an uncompleted filtration. The construction below takes measurable limits
along a countable rational grid from the past. This gives an adapted version
and retains continuous paths on the common full-measure grid agreement set.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology

namespace SphericalAging.AdaptedContinuous

@[expose] def gridTime (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n + 1)

@[expose] def pastGrid (t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  gridTime n ⌊t * (n + 1)⌋₊

lemma pastGrid_le (t : ℝ≥0) (n : ℕ) : pastGrid t n ≤ t := by
  unfold pastGrid gridTime
  apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)).2
  exact Nat.floor_le (by positivity)

lemma pastGrid_lower (t : ℝ≥0) (n : ℕ) :
    (t : ℝ) - 1 / ((n : ℝ) + 1) ≤ (pastGrid t n : ℝ) := by
  have h := Nat.lt_floor_add_one (t * (n + 1))
  have hreal : (t : ℝ) * ((n : ℝ) + 1) <
      (⌊t * (n + 1)⌋₊ : ℝ) + 1 := by exact_mod_cast h
  change (t : ℝ) - 1 / ((n : ℝ) + 1) ≤
    (⌊t * (n + 1)⌋₊ : ℝ) / ((n : ℝ) + 1)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  have hpos : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith

lemma tendsto_pastGrid (t : ℝ≥0) : Tendsto (pastGrid t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.1
  have hlo : Tendsto (fun n : ℕ => (t : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
    simpa using (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · exact fun n => pastGrid_lower t n
  · exact fun n => by exact_mod_cast pastGrid_le t n

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def adaptedVersion (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => X (pastGrid t n) ω)

lemma adaptedVersion_stronglyAdapted {X : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted 𝓕 X) : StronglyAdapted 𝓕 (adaptedVersion X) := by
  intro t
  let : MeasurableSpace Ω := 𝓕 t
  exact StronglyMeasurable.limUnder
    (fun n => hX.stronglyMeasurable_le (pastGrid_le t n))

omit [MeasurableSpace Ω] in
lemma adaptedVersion_eq_continuous {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hgrid : ∀ n k : ℕ, X (gridTime n k) ω = Y (gridTime n k) ω)
    (hY : Continuous (fun t => Y t ω)) (t : ℝ≥0) :
    adaptedVersion X t ω = Y t ω := by
  have hlim : Tendsto (fun n => X (pastGrid t n) ω) atTop (𝓝 (Y t ω)) := by
    have heq : (fun n => X (pastGrid t n) ω) = (fun n => Y (pastGrid t n) ω) := by
      funext n
      exact hgrid n _
    rw [heq]
    exact hY.continuousAt.tendsto.comp (tendsto_pastGrid t)
  exact hlim.limUnder_eq

/-- A continuous modification of a strongly adapted real process has a
strongly adapted continuous modification in the original filtration. -/
theorem exists_stronglyAdapted_continuousModification {X Y : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted 𝓕 X) (hXY : IsContinuousProcessModification X Y P) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      StronglyAdapted 𝓕 Z ∧ IsContinuousProcessModification X Z P := by
  have hgrid : ∀ᵐ ω ∂P, ∀ n k : ℕ,
      X (gridTime n k) ω = Y (gridTime n k) ω :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => hXY.fixedTime_ae_eq _))
  refine ⟨adaptedVersion X, adaptedVersion_stronglyAdapted hX, ?_⟩
  constructor
  · intro t
    filter_upwards [hXY.fixedTime_ae_eq t, hgrid, hXY.continuous_paths] with ω hω hg hc
    rw [adaptedVersion_eq_continuous hg hc t]
    exact hω
  · filter_upwards [hgrid, hXY.continuous_paths] with ω hg hc
    have heq : (fun t => adaptedVersion X t ω) = (fun t => Y t ω) :=
      funext (fun t => adaptedVersion_eq_continuous hg hc t)
    rw [heq]
    exact hc

theorem exists_continuous_martingale_modification {X Y : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓕 P) (hXY : IsContinuousProcessModification X Y P) :
    ∃ Z : ℝ≥0 → Ω → ℝ, Martingale Z 𝓕 P ∧ IsContinuousProcessModification X Z P := by
  obtain ⟨Z, hZ, hmod⟩ := exists_stronglyAdapted_continuousModification hX.stronglyAdapted hXY
  exact ⟨Z, hX.congr hZ hmod.fixedTime_ae_eq, hmod⟩

end SphericalAging.AdaptedContinuous
