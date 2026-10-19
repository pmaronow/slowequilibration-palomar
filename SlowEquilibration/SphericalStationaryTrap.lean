-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.StationaryTrap
public import SlowEquilibration.SphericalVectorSpectral
public import SlowEquilibration.SphericalTrapGeometry
public import SlowEquilibration.SphericalObservableDisplacement

/-!
# Trapping for the actual spherical mixed Langevin kernel

This is the measure-theoretic part of `lem:sp-trap`. Every transition below
is the constructed physical diffusion kernel, and its Gibbs invariance and
semigroup identity are proved properties of that kernel. The displacement
moment is the genuine stationary two-time moment; the spectral form adapter
supplies its energy estimate for smooth observables.
-/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalStationaryTrap

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalPhysicalSpectral SphericalForm
open SphericalBarycenter SphericalLaplaceIdentification
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal Topology InnerProductSpace

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

/-- The source supremum over every actual spherical cap center. -/
def capMassSup (π : Measure (Vector N)) (s : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ v : Vector N, OnSphere v ∧ r = π.real (cap v s)}

lemma cap_mass_le_sup (π : Measure (Vector N)) [IsProbabilityMeasure π]
    (s : ℝ) {v : Vector N} (hv : OnSphere v) :
    π.real (cap v s) ≤ capMassSup π s := by
  apply le_csSup (a := π.real (cap v s))
  · refine ⟨1, ?_⟩
    rintro r ⟨v, _, rfl⟩
    exact measureReal_le_one
  · exact ⟨v, hv, rfl⟩

lemma capMassSup_nonneg (π : Measure (Vector N)) [IsProbabilityMeasure π]
    (s : ℝ) : 0 ≤ capMassSup π s := by
  by_cases he : {r : ℝ | ∃ v : Vector N, OnSphere v ∧ r = π.real (cap v s)} = ∅
  · simp [capMassSup, he]
  · obtain ⟨r, v, hv, rfl⟩ := Set.nonempty_iff_ne_empty.mpr he
    exact (measureReal_nonneg (μ := π)).trans (cap_mass_le_sup π s hv)

/-- The literal Borel set of spherical initial states with acceptable
endpoint displacement probability. -/
def goodStartingSet (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (T : ℝ≥0) (B : Vector N → Vector N) (ρ η : ℝ) : Set (Vector N) :=
  {x | OnSphere x} ∩ StationaryTrap.goodStartingSet
    (mixedTransitionKernel μ J β T) B ρ η

theorem goodStartingSet_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (T : ℝ≥0) {B : Vector N → Vector N} (hB : Measurable B) (ρ η : ℝ) :
    MeasurableSet (goodStartingSet μ J β T B ρ η) :=
  (sphere_measurableSet N).inter (StationaryTrap.goodStartingSet_measurable _ hB ρ η)

/-- The source Dₓ, as a literal Borel subset of the physical sphere. -/
def displacementBall (B : Vector N → Vector N) (ρ : ℝ) (x : Vector N) : Set (Vector N) :=
  {y | OnSphere y} ∩ StationaryTrap.imageBall B ρ x

lemma displacementBall_measurable {B : Vector N → Vector N} (hB : Measurable B)
    (ρ : ℝ) (x : Vector N) : MeasurableSet (displacementBall B ρ x) :=
  (sphere_measurableSet N).inter (StationaryTrap.imageBall_measurable hB ρ x)

theorem displacementBall_transition_mass (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (T : ℝ≥0)
    {B : Vector N → Vector N} (hB : Measurable B) (ρ η : ℝ) {x : Vector N}
    (hx : x ∈ goodStartingSet μ J β T B ρ η) :
    1 - η ≤ (mixedTransitionKernel μ J β T x).real (displacementBall B ρ x) := by
  have hs : ∀ᵐ y ∂mixedTransitionKernel μ J β T x, OnSphere y :=
    (ae_mem_iff_measure_eq (sphere_measurableSet N).nullMeasurableSet).mpr (by
      simpa using mixedTransitionKernel_support (show N ≠ 0 by omega) μ J β x hx.1 T)
  have heq : displacementBall B ρ x =ᵐ[mixedTransitionKernel μ J β T x]
      StationaryTrap.imageBall B ρ x := by
    filter_upwards [hs] with y hy
    simp [displacementBall, hy]
  rw [measureReal_congr heq]
  exact StationaryTrap.imageBall_transition_mass _ hB ρ η hx.2

/-- First conclusion of `lem:sp-trap`, with the genuine stationary
displacement bound stated before its independently proved measure reduction. -/
theorem goodStartingSet_compl_mass_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (T : ℝ≥0)
    {B : Vector N → Vector N} (hB : Measurable B) {ρ η E : ℝ}
    (hρ : 0 < ρ) (hη : 0 < η)
    (hI : Integrable (fun z : Vector N × Vector N => ‖B z.2 - B z.1‖ ^ 2)
      (twoTimeLaw μ J β T))
    (hEnergy : (∫ z, ‖B z.2 - B z.1‖ ^ 2 ∂twoTimeLaw μ J β T) ≤ 2 * (T : ℝ) * E) :
    (mixtureGibbsLaw μ β J).real (goodStartingSet μ J β T B ρ η)ᶜ ≤
      2 * (T : ℝ) * E / (ρ ^ 2 * η) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  have heq : (goodStartingSet μ J β T B ρ η)ᶜ =ᵐ[mixtureGibbsLaw μ β J]
      (StationaryTrap.goodStartingSet (mixedTransitionKernel μ J β T) B ρ η)ᶜ := by
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
    simp [goodStartingSet, hx]
  rw [measureReal_congr heq]
  exact StationaryTrap.goodStartingSet_compl_mass_le _ _ hB hρ hη hI hEnergy

lemma physical_semigroup (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    ∀ s t, mixedTransitionKernel μ J β (s + t) =
      mixedTransitionKernel μ J β s ∘ₖ mixedTransitionKernel μ J β t := by
  intro s t
  apply Kernel.ext
  intro x
  simpa [add_comm s t] using mixedTransitionKernel_semigroup μ J β t s x

/-- Actual Gibbs mass of the image ball is bounded by the mass of the
unaligned set plus the source supremum of genuine spherical cap masses. -/
theorem imageBall_gibbs_mass_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N)
    (G : Set (Vector N)) (q ρ : ℝ) (hρ : 0 ≤ ρ) (hρq : ρ < q)
    (hB : ∀ y, OnSphere y → ‖B y‖ ≤ 1)
    (hA : ∀ y ∈ G, OnSphere y → q ≤ inner ℝ (spin y) (B y))
    (x : Vector N) (hx : OnSphere x) (hxG : x ∈ G) :
    (mixtureGibbsLaw μ β J).real (StationaryTrap.imageBall B ρ x) ≤
      (mixtureGibbsLaw μ β J).real Gᶜ + capMassSup (mixtureGibbsLaw μ β J) (q - ρ) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  obtain ⟨v, hv, hcap⟩ := SphericalBarycenter.displacementBall_cap
    hN B G q ρ hρ hρq hB hA x hx hxG
  have hsub : StationaryTrap.imageBall B ρ x ≤ᵐ[mixtureGibbsLaw μ β J]
      Gᶜ ∪ cap v (q - ρ) := by
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with y hy
    intro hnear
    by_cases hyG : y ∈ G
    · exact Or.inr (hcap y hy hyG hnear)
    · exact Or.inl hyG
  have hmeasure : (mixtureGibbsLaw μ β J).real (StationaryTrap.imageBall B ρ x) ≤
      (mixtureGibbsLaw μ β J).real (Gᶜ ∪ cap v (q - ρ)) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hmeasure.trans ((measureReal_union_le Gᶜ (cap v (q - ρ))).trans
    (add_le_add le_rfl (cap_mass_le_sup _ _ hv)))

theorem displacementBall_gibbs_mass_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N)
    (G : Set (Vector N)) (q ρ : ℝ) (hρ : 0 ≤ ρ) (hρq : ρ < q)
    (hB : ∀ y, OnSphere y → ‖B y‖ ≤ 1)
    (hA : ∀ y ∈ G, OnSphere y → q ≤ inner ℝ (spin y) (B y))
    (x : Vector N) (hx : OnSphere x) (hxG : x ∈ G) :
    (mixtureGibbsLaw μ β J).real (displacementBall B ρ x) ≤
      (mixtureGibbsLaw μ β J).real Gᶜ + capMassSup (mixtureGibbsLaw μ β J) (q - ρ) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  exact (measureReal_mono (show displacementBall B ρ x ⊆ StationaryTrap.imageBall B ρ x from
    inter_subset_right)).trans (imageBall_gibbs_mass_le hN μ J β B G q ρ hρ hρq hB hA x hx hxG)

/-- Second conclusion of `lem:sp-trap`: literal diffusion marginals
remain separated from Gibbs throughout [0,T]. The source w is exactly the
unaligned Gibbs mass plus the supremum of the actual cap masses. -/
theorem separation_all_times (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (T : ℝ≥0)
    (B : Vector N → Vector N) (hBm : Measurable B)
    (G : Set (Vector N)) (q ρ η : ℝ) (hρ : 0 ≤ ρ) (hρq : ρ < q) (hη : η < 1)
    (hB : ∀ y, OnSphere y → ‖B y‖ ≤ 1)
    (hA : ∀ y ∈ G, OnSphere y → q ≤ inner ℝ (spin y) (B y))
    (x : Vector N) (hx : x ∈ goodStartingSet μ J β T B ρ η) (hxG : x ∈ G) :
    let w := (mixtureGibbsLaw μ β J).real Gᶜ + capMassSup (mixtureGibbsLaw μ β J) (q - ρ)
    ∀ t ≤ T, 1 - η - w ≤ totalVariation (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) ∧
      StationaryTrap.entropyBound η w ≤
        InformationTheory.klDiv (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  have hw : 0 ≤ (mixtureGibbsLaw μ β J).real Gᶜ + capMassSup (mixtureGibbsLaw μ β J) (q - ρ) :=
    add_nonneg measureReal_nonneg (capMassSup_nonneg _ _)
  exact StationaryTrap.endpoint_separation_all_times_of_nonneg
    (mixedTransitionKernel μ J β) (mixtureGibbsLaw μ β J) (physical_semigroup μ J β)
    (mixedTransitionKernel_gibbs_invariant hN μ J β) T x
    (StationaryTrap.imageBall_measurable hBm ρ x) hη hw
    (StationaryTrap.imageBall_transition_mass _ hBm ρ η hx.2)
    (imageBall_gibbs_mass_le hN μ J β B G q ρ hρ hρq hB hA x hx.1 hxG)

/-- Full `lem:sp-trap` for an actual smooth spherical observable and the
constructed mixed Langevin process. Its energy is the integral of the
actual tangent Jacobian, by `vectorDirichletEnergy_eq_integral`. -/
theorem smooth_trap (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (T : ℝ≥0)
    (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (G : Set (Vector N)) (q ρ η : ℝ) (hρ : 0 < ρ) (hρq : ρ < q)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hB : ∀ y, OnSphere y → ‖B y‖ ≤ 1)
    (hA : ∀ y ∈ G, OnSphere y → q ≤ inner ℝ (spin y) (B y)) :
    ∃ Y : Set (Vector N), MeasurableSet Y ∧ Y ⊆ {x | OnSphere x} ∧
      (mixtureGibbsLaw μ β J).real Yᶜ ≤
        2 * (T : ℝ) * SphericalForm.vectorDirichletEnergy β (potential μ J) B / (ρ ^ 2 * η) ∧
      ∀ x ∈ Y ∩ G,
        let w := (mixtureGibbsLaw μ β J).real Gᶜ + capMassSup (mixtureGibbsLaw μ β J) (q - ρ)
        ∀ t ≤ T, 1 - η - w ≤ totalVariation (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) ∧
          StationaryTrap.entropyBound η w ≤
            InformationTheory.klDiv (mixedTransitionKernel μ J β t x) (mixtureGibbsLaw μ β J) := by
  have hN1 : 1 ≤ N := by omega
  refine ⟨goodStartingSet μ J β T B ρ η,
    goodStartingSet_measurable μ J β T hBs.continuous.measurable ρ η, inter_subset_left, ?_, ?_⟩
  · exact goodStartingSet_compl_mass_le hN1 μ J β T hBs.continuous.measurable hρ hη0
      (SphericalForm.smooth_vector_stationary_displacement_integrable hN1 μ J β B hBs T)
      (SphericalForm.smooth_vector_stationary_displacement_energy_le hN μ J β B hBs T)
  · intro x hx
    exact separation_all_times hN1 μ J β T B hBs.continuous.measurable
      G q ρ η hρ.le hρq hη1 hB hA x hx.1 hx.2

end SlowEquilibration.SphericalStationaryTrap
