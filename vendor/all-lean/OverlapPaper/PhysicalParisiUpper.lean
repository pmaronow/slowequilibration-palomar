module
public import OverlapPaper.ThermodynamicLimit
public import FourPapersCommon.MixedGuerra
public import FourPapersCommon.MixedMinimizer
public import FRSB.ParisiGridTopology
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! The physical even-mixture Guerra upper bound, with actual model/PDE bridges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped Topology BigOperators
namespace OverlapPaper
open FourPapersCommon
set_option maxHeartbeats 800000

theorem expectedFreeEnergy_le_mixedFunctional_scheme (ξ : AdmissibleEvenMixture)
    {N : ℕ} (hN : 0 < N) (h : ℝ) {k : ℕ} (s : RSBScheme k) :
    expectedFreeEnergy ξ h N ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  letI : IsGaussian (volume : Measure (Disorder N)) := disorderLaw_isGaussian ξ N
  let sk : MixedDisorder (Ω := Disorder N) N ξ :=
    { U := id
      hU := IsGaussianHilbert.of_hasGaussianLaw id measurable_id IsGaussian.hasGaussianLaw_id
        (integral_disorder_eq_zero ξ N)
      covariance := by
        intro σ τ
        change (∫ g : Disorder N, g σ * g τ ∂disorderLaw ξ N) =
          (N : ℝ) * ξ.value (SpinGlass.overlap N σ τ)
        simpa only [hamiltonian, overlap, SpinGlass.overlap, spin, SpinGlass.spin,
          div_eq_mul_inv, mul_comm, one_mul, mul_one]
          using integral_hamiltonian_product ξ σ τ }
  have hh := mixed_guerra_rsb_bound hN ξ sk s h
  have he : free_entropy (Ω := Disorder N) (N := N) (β := mixedBeta ξ) (h := h) sk.U =
      expectedFreeEnergy ξ h N := by
    change (∫ g : Disorder N, free_energy_density (N := N)
      (skEnergy (N := N) (β := mixedBeta ξ) (h := h) g) ∂disorderLaw ξ N) = _
    unfold skEnergy
    simp only [neg_one_smul, gaussian_freeEnergy_eq_physical]
    rfl
  rwa [he] at hh

theorem expectedFreeEnergy_le_mixedFunctional (ξ : AdmissibleEvenMixture)
    {N : ℕ} (hN : 0 < N) (h : ℝ) (μ : Paper.ParisiMeasure) :
    expectedFreeEnergy ξ h N ≤ mixedFunctional ξ h μ := by
  have ht := (continuous_mixedFunctional ξ h).tendsto μ |>.comp (FRSB.tendsto_parisiGridMeasure μ)
  apply ge_of_tendsto ht
  filter_upwards with n
  change expectedFreeEnergy ξ h N ≤ mixedFunctional ξ h (Paper.parisiGridMeasure μ n)
  rw [← FRSB.parisiSchemeMeasure_grid_eq μ n]
  exact expectedFreeEnergy_le_mixedFunctional_scheme ξ hN h (Paper.parisiGridRSBScheme μ n)

theorem thermodynamicPressure_le_mixedFunctional (ξ : AdmissibleEvenMixture)
    (h : ℝ) (μ : Paper.ParisiMeasure) :
    thermodynamicPressure ξ h ≤ mixedFunctional ξ h μ := by
  exact le_of_tendsto (tendsto_expectedFreeEnergy ξ h) (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact expectedFreeEnergy_le_mixedFunctional ξ hN h μ)

theorem expectedFreeEnergy_le_mixedPressure (ξ : AdmissibleEvenMixture)
    {N : ℕ} (hN : 0 < N) (h : ℝ) : expectedFreeEnergy ξ h N ≤ mixedPressure ξ h := by
  rw [← mixedMinimizer_value ξ h]
  exact expectedFreeEnergy_le_mixedFunctional ξ hN h (mixedMinimizer ξ h)

theorem thermodynamicPressure_le_mixedPressure (ξ : AdmissibleEvenMixture) (h : ℝ) :
    thermodynamicPressure ξ h ≤ mixedPressure ξ h := by
  rw [← mixedMinimizer_value ξ h]
  exact thermodynamicPressure_le_mixedFunctional ξ h (mixedMinimizer ξ h)

end OverlapPaper
