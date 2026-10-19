module
public import FourPapersCommon.MixedGuerraDisorder
public import FourPapersCommon.MixedScheme

@[expose] public section

/-! The literal interpolation source for arbitrary mixture covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixedGuerraD_top_expectation {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) N ξ) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω, guerraD N s β (sk.U ω) h (k + 2) t 0 ∂ℙ) =
      (N / 2) * (ξ.value 1 - β ^ 2 -
        (∫ ω, guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => ξ.value (overlap N σ τ)) (k + 2) 0 ∂ℙ) +
        β ^ 2 * ∫ ω, guerraReplicaAccum N s β (sk.U ω) h t
          (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0 ∂ℙ) := by
  have hU := mixed_integrable_guerraUD_radial β h sk.U sk.hU s ht (k + 2) 0
  have hQ := mixed_integrable_guerraReplicaAccum β h sk.U sk.hU s ht (abs_q_mul_overlap_le_one hN s) (k + 2) 0
  have h1Q : Integrable (fun ω => 1 - guerraReplicaAccum N s β (sk.U ω) h t
      (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0) ℙ :=
    (integrable_const 1).sub hQ
  have hIQ : Integrable (fun ω => (N * β ^ 2 / 2) * (1 - guerraReplicaAccum N s β (sk.U ω) h t
      (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0)) ℙ := h1Q.const_mul _
  have he : ∀ ω, guerraD N s β (sk.U ω) h (k + 2) t 0 =
      (1 / (2 * t)) * guerraUD N s β (sk.U ω) (sk.U ω) h t (k + 2) 0 -
        (N * β ^ 2 / 2) * (1 - guerraReplicaAccum N s β (sk.U ω) h t
          (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0) := by
    intro ω
    rw [guerraD_eq_radials_overlap hN s β h (sk.U ω) ht,
      guerraYD_eq_sum N s β (sk.U ω) h ht]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero,
      guerraFieldTerm, Nat.sub_self, s.q_zero, add_zero]
  simp_rw [he]
  rw [integral_sub (hU.const_mul _) hIQ,
    integral_const_mul, integral_const_mul, integral_sub (integrable_const 1) hQ,
    mixedGuerra_disorder_expectation hN β h ξ sk s ht]
  simp only [integral_const, probReal_univ, one_smul]
  field_simp [ht.1.ne']
  ring


end FourPapersCommon
