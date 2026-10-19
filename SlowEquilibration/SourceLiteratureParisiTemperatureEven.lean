-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureParisi

/-!
# Temperature evenness of the physical pressure and its variational value

Chen's spherical Parisi theorem is cited for nonnegative inverse
temperatures. Several physical wrappers in this repository consume the
pressure limit at every real temperature. Both sides of that limit are
even in the temperature: the ordered Gaussian tensor law is invariant under
`J ↦ -J`, the field is linear in `J`, and the Crisanti–Sommers functional
depends on `β` only through `β^2`. Hence the nonnegative-temperature
citation already gives the all-real statement, with no further input.
-/

@[expose] public section

namespace SlowEquilibration.SourceLiteratureParisiTemperatureEven

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel CrisantiSommers SourceLiteratureParisi
open scoped Topology
set_option autoImplicit false

/-- One ordered Gaussian tensor block is invariant under sign reversal. -/
theorem finiteDisorderLaw_map_neg (N p : ℕ) :
    (SphericalAging.FiniteModel.disorderLaw N p).map
      (fun J : SphericalAging.FiniteModel.Disorder N p => -J) =
      SphericalAging.FiniteModel.disorderLaw N p := by
  unfold SphericalAging.FiniteModel.disorderLaw
  have h := Measure.pi_map_pi
    (μ := fun _ : SphericalAging.FiniteModel.TensorIndex N p => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => -x) (fun _ => measurable_neg.aemeasurable)
  simp only [gaussianReal_map_neg, neg_zero] at h
  exact h

/-- The whole product disorder law is invariant under sign reversal. -/
theorem disorderLaw_map_neg (N P : ℕ) :
    (disorderLaw N P).map (fun J : Disorder N P => -J) = disorderLaw N P := by
  unfold disorderLaw
  have h := Measure.pi_map_pi
    (μ := fun p : Degree P => SphericalAging.FiniteModel.disorderLaw N p.val.val)
    (f := fun p (J : SphericalAging.FiniteModel.Disorder N p.val.val) => -J)
    (fun _ => measurable_neg.aemeasurable)
  simp only [finiteDisorderLaw_map_neg] at h
  exact h

theorem disorderLaw_neg_measurePreserving (N P : ℕ) :
    MeasurePreserving (MeasurableEquiv.neg (Disorder N P))
      (disorderLaw N P) (disorderLaw N P) :=
  ⟨measurable_neg, disorderLaw_map_neg N P⟩

/-- The literal mixed field is linear in the disorder. -/
theorem field_neg {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) : field c (-J) x = -field c J x := by
  rw [← fieldCLM_apply, ← fieldCLM_apply, map_neg]

theorem mixturePartition_neg_beta {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) :
    mixturePartition μ (-β) J = mixturePartition μ β (-J) := by
  unfold mixturePartition partition fieldOfMixture
  congr 1
  funext x
  rw [field_neg, neg_mul, mul_neg]

/-- The finite-dimensional quenched pressure is an even function of the
inverse temperature, in every dimension. -/
theorem quenchedPressure_neg (N : ℕ) (μ : FiniteMixture) (β : ℝ) :
    quenchedPressure N μ (-β) = quenchedPressure N μ β := by
  unfold quenchedPressure
  congr 1
  simp_rw [mixturePartition_neg_beta]
  exact (disorderLaw_neg_measurePreserving N μ.maxDegree).integral_comp'
    (fun J => Real.log (mixturePartition μ β J))

theorem functional_neg (β : ℝ) (η : ℝ → ℝ) (ζ : Measure ℝ) (q : ℝ) :
    CrisantiSommers.functional (-β) η ζ q = CrisantiSommers.functional β η ζ q := by
  simp only [CrisantiSommers.functional, neg_sq]

theorem admissible_value_neg (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ) :
    ζ.value (-β) η = ζ.value β η := by
  simp only [Admissible.value, functional_neg]

/-- The Crisanti–Sommers minimum is an even function of the temperature. -/
theorem variationalValue_neg (μ : FiniteMixture) (β : ℝ) :
    CSParisiMeasure.variationalValue μ (-β) =
      CSParisiMeasure.variationalValue μ β := by
  unfold CSParisiMeasure.variationalValue
  have h₁ := CSParisiMeasure.canonicalMinimizer_isMinimizer μ (-β)
    (CSParisiMeasure.canonicalMinimizer μ β)
  have h₂ := CSParisiMeasure.canonicalMinimizer_isMinimizer μ β
    (CSParisiMeasure.canonicalMinimizer μ (-β))
  rw [admissible_value_neg, admissible_value_neg] at h₁
  rw [admissible_value_neg]
  exact le_antisymm h₁ h₂

/-- Chen's nonnegative-temperature theorem gives the pressure limit at every
real inverse temperature. -/
theorem finite_pressure_limit_all_real (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) (β : ℝ) :
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop
      (𝓝 (CSParisiMeasure.variationalValue μ β)) := by
  rcases le_total 0 β with hβ | hβ
  · exact hChen μ β hβ
  · have h := hChen μ (-β) (neg_nonneg.mpr hβ)
    simpa only [quenchedPressure_neg, variationalValue_neg] using h

/-- The shifted-dimension form consumed by the physical wrappers. -/
theorem finite_pressure_limit_all_real_shift (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) (β : ℝ) :
    Tendsto (fun n : ℕ => quenchedPressure (n+2) μ β) atTop
      (𝓝 (CSParisiMeasure.variationalValue μ β)) :=
  (finite_pressure_limit_all_real hChen μ β).comp (tendsto_add_atTop_nat 2)

end
end SlowEquilibration.SourceLiteratureParisiTemperatureEven
