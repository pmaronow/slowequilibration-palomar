module
public import FourPapersCommon.MixedFiniteDiffusionLaw
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-! Concrete finite two-group branching laws and their exact marginals.
Both independent continuations start from the common sampled state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open SpinGlass SpinGlass.Targets
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedSchemeEndpointKernel_add {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p n m : ℕ) :
    mixedSchemeEndpointKernel ξ s p (n + m) =
      mixedSchemeEndpointKernel ξ s (p + n) m ∘ₖ mixedSchemeEndpointKernel ξ s p n := by
  induction m with
  | zero => simp only [Nat.add_zero, mixedSchemeEndpointKernel, Kernel.id_comp]
  | succ m ih =>
      change mixedSchemeScalarStep ξ s (p + (n + m)) ∘ₖ mixedSchemeEndpointKernel ξ s p (n + m) =
        (mixedSchemeScalarStep ξ s ((p + n) + m) ∘ₖ mixedSchemeEndpointKernel ξ s (p + n) m) ∘ₖ
          mixedSchemeEndpointKernel ξ s p n
      rw [ih, Kernel.comp_assoc, Nat.add_assoc]

def mixedTwoGroupEndpointLaw {k : ℕ} (ξ : AdmissibleEvenMixture) (h : ℝ)
    (s : RSBScheme k) (p n : ℕ) : Measure (ℝ × ℝ) :=
  (mixedSchemeEndpointKernel ξ s p n ×ₖ mixedSchemeEndpointKernel ξ s p n) ∘ₘ
    mixedSchemeEndpointKernel ξ s 0 p h

theorem isProbabilityMeasure_mixedTwoGroupEndpointLaw {k : ℕ}
    (ξ : AdmissibleEvenMixture) (h : ℝ) (s : RSBScheme k) (p n : ℕ)
    (hn : p + n ≤ k + 2) : IsProbabilityMeasure (mixedTwoGroupEndpointLaw ξ h s p n) := by
  letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p n hn
  letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s 0 p (by omega)
  unfold mixedTwoGroupEndpointLaw
  infer_instance

theorem mixedTwoGroupEndpointLaw_fst {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) (p n : ℕ) (hn : p + n ≤ k + 2) :
    (mixedTwoGroupEndpointLaw ξ h s p n).map Prod.fst =
      mixedSchemeEndpointKernel ξ s 0 (p + n) h := by
  letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p n hn
  letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s 0 p (by omega)
  rw [mixedTwoGroupEndpointLaw, Measure.map_comp _ _ measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]
  change (mixedSchemeEndpointKernel ξ s p n ∘ₖ mixedSchemeEndpointKernel ξ s 0 p) h = _
  simpa only [Nat.zero_add] using congrArg (fun K : Kernel ℝ ℝ => K h)
    (mixedSchemeEndpointKernel_add ξ s 0 p n).symm

theorem mixedTwoGroupEndpointLaw_snd {k : ℕ} (ξ : AdmissibleEvenMixture)
    (h : ℝ) (s : RSBScheme k) (p n : ℕ) (hn : p + n ≤ k + 2) :
    (mixedTwoGroupEndpointLaw ξ h s p n).map Prod.snd =
      mixedSchemeEndpointKernel ξ s 0 (p + n) h := by
  letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p n hn
  letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s 0 p (by omega)
  rw [mixedTwoGroupEndpointLaw, Measure.map_comp _ _ measurable_snd]
  rw [← Kernel.snd_eq, Kernel.snd_prod]
  change (mixedSchemeEndpointKernel ξ s p n ∘ₖ mixedSchemeEndpointKernel ξ s 0 p) h = _
  simpa only [Nat.zero_add] using congrArg (fun K : Kernel ℝ ℝ => K h)
    (mixedSchemeEndpointKernel_add ξ s 0 p n).symm

theorem mixedTwoGroupEndpointLaw_marginal_actual {k : ℕ}
    (ξ : AdmissibleEvenMixture) (h : ℝ) (s : RSBScheme k) (p n : ℕ)
    (hn : p + n ≤ k + 2) :
    (mixedTwoGroupEndpointLaw ξ h s p n).map Prod.fst =
      Paper.canonicalBrownianMeasure.map (fun ω => mixedState ξ h (Paper.parisiSchemeMeasure s) ω (s.q (p + n))) ∧
    (mixedTwoGroupEndpointLaw ξ h s p n).map Prod.snd =
      Paper.canonicalBrownianMeasure.map (fun ω => mixedState ξ h (Paper.parisiSchemeMeasure s) ω (s.q (p + n))) := by
  rw [mixedState_schemeEndpoint_law ξ h s hn]
  exact ⟨mixedTwoGroupEndpointLaw_fst ξ h s p n hn,
    mixedTwoGroupEndpointLaw_snd ξ h s p n hn⟩

end FourPapersCommon
