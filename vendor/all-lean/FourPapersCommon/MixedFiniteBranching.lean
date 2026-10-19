module
public import FourPapersCommon.MixedScalarTransition
public import FourPapersCommon.MixedScheme
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Actual scalar finite-scheme branching transitions and their terminal
magnetization identity. Each transition is a normalized Gaussian kernel,
and coincident overlap levels are actual identity kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open SpinGlass SpinGlass.Targets
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def mixedSchemeScalarStep {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (p : ℕ) : Kernel ℝ ℝ :=
  mixedScalarTransition ξ (Paper.parisiSchemeMeasure s) (s.q p) (s.q (p + 1)) (s.m p)

theorem isMarkovKernel_mixedSchemeScalarStep {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 1) : IsMarkovKernel (mixedSchemeScalarStep ξ s p) :=
  isMarkovKernel_mixedScalarTransition ξ _ _ _ _
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩

theorem mixedSchemeScalarStep_of_equal {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 1) (he : s.q p = s.q (p + 1)) :
    mixedSchemeScalarStep ξ s p = Kernel.id := by
  have hb : s.q (p + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  unfold mixedSchemeScalarStep mixedScalarTransition
  rw [he, sub_self, Real.toNNReal_zero]
  exact FRSB.constantMassKernel_zero_variance _ _ (continuous_mixedPotential_section ξ _ _)
    (mixedPotential_hasLinearGrowth ξ _ hb)

theorem mixedGradient_eq_schemeStep_average {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 1) (x : ℝ) :
    mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q p, x) =
      ∫ y, mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q (p + 1), y)
        ∂mixedSchemeScalarStep ξ s p x := by
  have ha : s.q p ∈ Icc (0 : ℝ) 1 := ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have hb : s.q (p + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  rcases lt_or_eq_of_le (s.q_mono p hp) with hlt | he
  · exact mixedGradient_eq_transition_average ξ _ ha hb hlt
      (fun _ hy => Paper.parisiCDF_scheme_cell s hp hy) x
  · rw [mixedSchemeScalarStep_of_equal ξ s hp he, Kernel.id_apply, integral_dirac, he]

def mixedSchemeEndpointKernel {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (p : ℕ) : ℕ → Kernel ℝ ℝ
  | 0 => Kernel.id
  | n + 1 => mixedSchemeScalarStep ξ s (p + n) ∘ₖ mixedSchemeEndpointKernel ξ s p n

theorem isMarkovKernel_mixedSchemeEndpointKernel {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p n : ℕ) (hn : p + n ≤ k + 2) :
    IsMarkovKernel (mixedSchemeEndpointKernel ξ s p n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel ℝ ℝ); infer_instance
  | succ n ih =>
      letI := isMarkovKernel_mixedSchemeScalarStep ξ s (p := p + n) (by omega)
      letI := ih (by omega)
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance

theorem mixedGradient_eq_endpointKernel_average {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (p n : ℕ) (hn : p + n ≤ k + 2) (x : ℝ) :
    mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q p, x) =
      ∫ y, mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q (p + n), y)
        ∂mixedSchemeEndpointKernel ξ s p n x := by
  induction n with
  | zero => rw [mixedSchemeEndpointKernel, Kernel.id_apply, integral_dirac, Nat.add_zero]
  | succ n ih =>
      letI := isMarkovKernel_mixedSchemeScalarStep ξ s (p := p + n) (by omega)
      letI := isMarkovKernel_mixedSchemeEndpointKernel ξ s p n (by omega)
      have hf : Measurable (fun y => mixedGradient ξ (Paper.parisiSchemeMeasure s)
          (s.q (p + (n + 1)), y)) := by
        change Measurable (fun y => Paper.parisiGradient (mixedBeta ξ)
          (mixedMeasure ξ (Paper.parisiSchemeMeasure s)) (ξ.clock (s.q (p + (n + 1))), y))
        exact ((Paper.continuous_parisiGradient _ _).comp
          (continuous_const.prodMk continuous_id)).measurable
      have hi : Integrable (fun y => mixedGradient ξ (Paper.parisiSchemeMeasure s)
          (s.q (p + (n + 1)), y))
          ((mixedSchemeScalarStep ξ s (p + n) ∘ₖ mixedSchemeEndpointKernel ξ s p n) x) :=
        (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
          (.of_forall (fun y => norm_mixedGradient_le_one ξ _ _))
      rw [mixedSchemeEndpointKernel, Kernel.integral_comp hi]
      simp_rw [show p + (n + 1) = p + n + 1 by omega,
        ← mixedGradient_eq_schemeStep_average ξ s (p := p + n) (by omega)]
      exact ih (by omega)

theorem mixedGradient_eq_terminalTanh_average {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 2) (x : ℝ) :
    mixedGradient ξ (Paper.parisiSchemeMeasure s) (s.q p, x) =
      ∫ y, Real.tanh y ∂mixedSchemeEndpointKernel ξ s p (k + 2 - p) x := by
  have H := mixedGradient_eq_endpointKernel_average ξ s p (k + 2 - p) (by omega) x
  simpa only [Nat.add_sub_of_le hp, s.q_top, mixedGradient, ξ.clock_one,
    Paper.parisiGradient_terminal] using H

end FourPapersCommon
