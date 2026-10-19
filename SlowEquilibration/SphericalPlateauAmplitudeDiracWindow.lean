-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeDiracTrial

@[expose] public section

/-! # Compact parameters of the actual perturbed-bank Dirac trial

The amplitude box and signed positive latitude window are actual compact
sets. The covariance, its derivative at the original atom and the Dirac
trial have the genuine continuity and sign properties used by the finite
Gaussian endpoint comparison.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set
open SphericalModel
open scoped Topology
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev AmplitudeDiracParameter := (Fin 2 → ℝ) × ℝ

def amplitudeDiracParameterSet (δ ρ : ℝ) : Set AmplitudeDiracParameter :=
  (Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => (2 : ℝ))).prod
    ((Icc (-ρ) ρ)∩{r : ℝ | δ≤|r|})

theorem amplitudeDiracParameterSet_compact (δ ρ : ℝ) : IsCompact (amplitudeDiracParameterSet δ ρ) :=
  (isCompact_Icc).prod ((isCompact_Icc).inter_right (isClosed_le continuous_const continuous_abs))

theorem mem_amplitudeDiracParameterSet_iff (δ ρ : ℝ) (z : AmplitudeDiracParameter) :
    z∈amplitudeDiracParameterSet δ ρ ↔ (∀ j,|z.1 j|≤2) ∧ |z.2|∈Icc δ ρ := by
  constructor
  · rintro ⟨hs,hr⟩
    exact ⟨fun j => abs_le.mpr ⟨hs.1 j,hs.2 j⟩,⟨hr.2,abs_le.mpr hr.1⟩⟩
  · rintro ⟨hs,hr⟩
    exact ⟨⟨fun j => (abs_le.mp (hs j)).1,fun j => (abs_le.mp (hs j)).2⟩,⟨abs_le.mp hr.2,hr.1⟩⟩

theorem amplitudeDiracAtom_upper {ρ r : ℝ} (hρ : 0≤ρ) (hr : |r|≤ρ) :
    amplitudeDiracAtom r≤ρ/(1+ρ) := by
  unfold amplitudeDiracAtom
  apply (div_le_div_iff₀ (by positivity : 0<1+|r|) (by linarith : 0<1+ρ)).mpr
  nlinarith

theorem amplitudeDiracAtom_range {δ ρ : ℝ} (hδ : 0<δ) (hδρ : δ≤ρ)
    (z : AmplitudeDiracParameter) (hz : z∈amplitudeDiracParameterSet δ ρ) :
    amplitudeDiracAtom z.2∈Icc (δ/(1+δ)) (ρ/(1+ρ)) := by
  have hr := ((mem_amplitudeDiracParameterSet_iff δ ρ z).mp hz).2
  exact ⟨amplitudeDiracAtom_lower hδ hr.1,amplitudeDiracAtom_upper (hδ.le.trans hδρ) hr.2⟩

theorem amplitudeDirac_first_continuous (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) :
    Continuous (fun z : AmplitudeDiracParameter => amplitudeLatitudeCovarianceFirst μ p₀ z.1 z.2 (amplitudeDiracAtom z.2)) := by
  have hA : Continuous (fun z : AmplitudeDiracParameter => amplitudeDiracAtom z.2) :=
    amplitudeDiracAtom_continuous.comp (continuous_snd : Continuous (fun z : AmplitudeDiracParameter => z.2))
  have ht : Continuous (fun z : AmplitudeDiracParameter => (z,amplitudeDiracAtom z.2)) :=
    (continuous_id : Continuous (fun z : AmplitudeDiracParameter => z)).prodMk hA
  simpa only [Function.comp_def] using (amplitudeLatitudeCovarianceFirst_joint_continuous μ p₀).comp ht

/-- Actual limiting linear variance in the fixed original Dirac trial. -/
def amplitudeDiracLimitingVariance (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree)
    (z : AmplitudeDiracParameter) : ℝ :=
  β^2*amplitudeLatitudeCovarianceFirst μ p₀ z.1 z.2 (amplitudeDiracAtom z.2)

theorem amplitudeDiracLimitingVariance_continuous (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) : Continuous (amplitudeDiracLimitingVariance μ β p₀) :=
  (amplitudeDirac_first_continuous μ p₀).const_mul (β^2)

theorem amplitudeDiracLimitingVariance_nonneg (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) {δ ρ : ℝ} (hρ : ρ<1)
    (z : AmplitudeDiracParameter) (hz : z∈amplitudeDiracParameterSet δ ρ) :
    0≤amplitudeDiracLimitingVariance μ β p₀ z := by
  have hr := ((mem_amplitudeDiracParameterSet_iff δ ρ z).mp hz).2
  exact mul_nonneg (sq_nonneg β) (amplitudeLatitudeCovarianceFirst_nonneg μ p₀ z.1 (hr.2.trans hρ.le)
    (amplitudeDiracAtom_mem z.2).1)

theorem amplitudeLatitudeCovariance_nonneg (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r t : ℝ} (hr : |r|≤1) (ht : 0≤t) :
    0≤amplitudeLatitudeCovariance μ p₀ s r t := by
  rw [amplitudeLatitudeCovariance_eq_polynomial]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (amplitudeLatitudeCoefficient_nonneg μ p₀ s hr i) (pow_nonneg ht _)

/-- Source amplitude lines in [-1/2,1/2] stay inside the true compact
parameter box before any pressure limit is taken. -/
theorem amplitudeAt_mem_DiracParameterSet (k : Fin 2) {τ δ ρ r : ℝ}
    (hτ : τ∈Icc (-1/2 : ℝ) (1/2)) (hr : |r|∈Icc δ ρ) :
    (amplitudeAt k τ,r)∈amplitudeDiracParameterSet δ ρ := by
  apply (mem_amplitudeDiracParameterSet_iff δ ρ _).mpr
  refine ⟨?_,hr⟩
  intro j
  unfold amplitudeAt
  dsimp only
  split_ifs
  · apply abs_le.mpr
    constructor <;> linarith [hτ.1,hτ.2]
  · norm_num

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
