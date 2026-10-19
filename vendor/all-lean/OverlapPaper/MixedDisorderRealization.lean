module
public import OverlapPaper.FiniteMoments
public import FourPapersCommon.MixedGuerraDisorder
public import Lemmas.Gaussian.CanonicalModel

@[expose] public section

/-! Actual canonical mixed Gaussian disorder in the generic Guerra interface. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass
open PhysLean.Probability.GaussianIBP
namespace OverlapPaper
open FourPapersCommon

def canonicalMixedDisorder (ξ : AdmissibleEvenMixture) (N : ℕ) :
    (letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
     letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
     MixedDisorder (Ω := Disorder N) N ξ) := by
  letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
  letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
  letI : IsGaussian (volume : Measure (Disorder N)) := disorderLaw_isGaussian ξ N
  refine { U := id
           hU := IsGaussianHilbert.of_hasGaussianLaw id measurable_id IsGaussian.hasGaussianLaw_id
             (integral_disorder_eq_zero ξ N)
           covariance := ?_ }
  intro σ τ
  change (∫ g : Disorder N, g σ * g τ ∂disorderLaw ξ N) =
    (N : ℝ) * ξ.value (SpinGlass.overlap N σ τ)
  simpa only [hamiltonian, overlap, SpinGlass.overlap, spin, SpinGlass.spin,
    div_eq_mul_inv, mul_comm, one_mul, mul_one] using integral_hamiltonian_product ξ σ τ

@[simp] theorem canonicalMixedDisorder_U (ξ : AdmissibleEvenMixture) (N : ℕ) :
    (letI : MeasureSpace (Disorder N) := ⟨disorderLaw ξ N⟩
     letI : IsProbabilityMeasure (volume : Measure (Disorder N)) := disorderLaw_isProbabilityMeasure ξ N
     (canonicalMixedDisorder ξ N).U = id) := rfl

end OverlapPaper
