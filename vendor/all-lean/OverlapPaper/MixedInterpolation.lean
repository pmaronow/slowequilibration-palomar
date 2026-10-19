module
public import OverlapPaper.MixedDisorderRealization
public import OverlapPaper.ThermodynamicLimit
public import FourPapersCommon.MixedGuerraBounds
public import FourPapersCommon.MixedMinimizer

@[expose] public section

/-! The mixed Guerra interpolation under the actual canonical disorder law.

The probability space changes with the system size. Each occurrence below uses
the genuine Gaussian law of the corresponding finite mixed Hamiltonian.
-/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass SpinGlass.Targets Set Filter
open scoped Topology
namespace OverlapPaper
open FourPapersCommon
set_option maxHeartbeats 600000

def physicalMixedPhi (ξ : AdmissibleEvenMixture) (h : ℝ) {k : ℕ}
    (s : RSBScheme k) (N : ℕ) (t : ℝ) : ℝ :=
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h id t

def physicalMixedRemainder (ξ : AdmissibleEvenMixture) (h : ℝ) {k : ℕ}
    (s : RSBScheme k) (N : ℕ) (t : ℝ) : ℝ :=
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  mixedGuerraRemainder (N := N) ξ s h (id : Disorder N → EnergySpace N) t

def mixedGuerraPsi (ξ : AdmissibleEvenMixture) (h : ℝ) {k : ℕ}
    (s : RSBScheme k) (t : ℝ) : ℝ :=
  Real.log 2 + parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
    t * mixedSchemeCorrection ξ s

theorem canonicalMixedDisorder_freeEntropy (ξ : AdmissibleEvenMixture) (N : ℕ) (h : ℝ) :
    (letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
     letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
     free_entropy (Ω := Disorder N) (N := N) (β := mixedBeta ξ) (h := h)
       (canonicalMixedDisorder ξ N).U = expectedFreeEnergy ξ h N) := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  change (∫ g : Disorder N, free_energy_density (N := N)
    (skEnergy (N := N) (β := mixedBeta ξ) (h := h) g) ∂disorderLaw ξ N) = _
  unfold skEnergy
  simp only [neg_one_smul, gaussian_freeEnergy_eq_physical]
  rfl

theorem physicalMixedPhi_zero (ξ : AdmissibleEvenMixture) {N : ℕ} (hN : 0 < N)
    (h : ℝ) {k : ℕ} (s : RSBScheme k) :
    physicalMixedPhi ξ h s N 0 =
      Real.log 2 + parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  exact guerraPhi_zero N hN (mixedClockScheme ξ s) (mixedBeta ξ) h id

theorem physicalMixedPhi_one (ξ : AdmissibleEvenMixture) {N : ℕ} (hN : 0 < N)
    (h : ℝ) {k : ℕ} (s : RSBScheme k) :
    physicalMixedPhi ξ h s N 1 = expectedFreeEnergy ξ h N := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  change guerraPhi N (mixedClockScheme ξ s) (mixedBeta ξ) h id 1 = _
  rw [guerraPhi_one N hN]
  exact canonicalMixedDisorder_freeEntropy ξ N h

theorem physicalMixedInterpolation_identity (ξ : AdmissibleEvenMixture) {N : ℕ}
    (hN : 0 < N) (h : ℝ) {k : ℕ} (s : RSBScheme k) :
    ContinuousOn (physicalMixedPhi ξ h s N) (Icc (0 : ℝ) 1) ∧
      (∀ t, 0 ≤ physicalMixedRemainder ξ h s N t) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (physicalMixedPhi ξ h s N)
          (-mixedSchemeCorrection ξ s - physicalMixedRemainder ξ h s N t) t := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  unfold physicalMixedPhi physicalMixedRemainder
  simpa only [canonicalMixedDisorder_U] using!
    mixed_guerra_identity hN ξ (canonicalMixedDisorder ξ N) s h

theorem physicalMixedPhi_endpoint_lower (ξ : AdmissibleEvenMixture) {N : ℕ}
    (hN : 0 < N) (h : ℝ) {k : ℕ} (s : RSBScheme k) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    physicalMixedPhi ξ h s N t - mixedGuerraDerivativeBound ξ * (1 - t) ≤
      expectedFreeEnergy ξ h N := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  have hh := mixedGuerraPhi_endpoint_lower hN ξ (canonicalMixedDisorder ξ N) s h ht
  rw [canonicalMixedDisorder_freeEntropy ξ N h] at hh
  exact hh

theorem mixedGuerraPsi_one (ξ : AdmissibleEvenMixture) (h : ℝ) {k : ℕ} (s : RSBScheme k) :
    mixedGuerraPsi ξ h s 1 = mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  rw [mixedFunctional_scheme]
  simp [mixedGuerraPsi]

theorem mixedGuerraPsi_ge_pressure (ξ : AdmissibleEvenMixture) (h : ℝ) {k : ℕ}
    (s : RSBScheme k) {t : ℝ} (ht : t ≤ 1) : mixedPressure ξ h ≤ mixedGuerraPsi ξ h s t := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h (Paper.parisiSchemeMeasure s)
  rw [← mixedGuerraPsi_one] at hp
  have hc := (mixedSchemeCorrection_bounds ξ s).1
  unfold mixedGuerraPsi at hp ⊢
  nlinarith

end OverlapPaper
