module
public import FourPapersCommon.MixedGuerraDisorder
public import FourPapersCommon.MixedScheme
public import Targets.Section5ZeroInitialReflection

@[expose] public section

/-! Actual spin-reflection symmetry from the mixed covariance. No samplewise
Hamiltonian parity assumption is added to the model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

/-- Every positive-variance spectral direction of exact SK disorder is even. -/
theorem mixedDisorder_basis_even_of_variance_ne_zero {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) (i : sk.hU.ι) (hi : sk.hU.τ i ≠ 0)
    (σ : Config n) : sk.hU.w i (configFlip n σ) = sk.hU.w i σ := by
  have Hff := mixedDisorder_covariance_spectral_sum ξ sk (configFlip n σ) (configFlip n σ)
  have Hfs := mixedDisorder_covariance_spectral_sum ξ sk (configFlip n σ) σ
  have Hss := mixedDisorder_covariance_spectral_sum ξ sk σ σ
  simp only [overlap_configFlip_left, overlap_configFlip_right, neg_neg, ξ.value_even] at Hff Hfs Hss
  have Hsum : (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) *
      (sk.hU.w j (configFlip n σ) - sk.hU.w j σ) ^ 2) = 0 := by
    calc
      _ = (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) *
          (sk.hU.w j (configFlip n σ) * sk.hU.w j (configFlip n σ))) -
        2 * (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) *
          (sk.hU.w j (configFlip n σ) * sk.hU.w j σ)) +
        (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) * (sk.hU.w j σ * sk.hU.w j σ)) := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = 0 := by rw [Hff, Hfs, Hss]; ring
  have Hterm : (sk.hU.τ i : ℝ) * (sk.hU.w i (configFlip n σ) - sk.hU.w i σ) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (sk.hU.τ j).coe_nonneg (sq_nonneg _))).mp Hsum i (Finset.mem_univ i)
  have ht : (sk.hU.τ i : ℝ) ≠ 0 := by exact_mod_cast hi
  have Hz := (mul_eq_zero.mp Hterm).resolve_left ht
  nlinarith [sq_nonneg (sk.hU.w i (configFlip n σ) - sk.hU.w i σ)]

/-- Exact-covariance SK Hamiltonians are even on one common full-measure set. -/
theorem mixedDisorder_even_ae {n : ℕ} (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ) :
    ∀ᵐ ω, ∀ σ, sk.U ω (configFlip n σ) = sk.U ω σ := by
  have hc (i : sk.hU.ι) : ∀ᵐ ω, ∀ σ,
      sk.hU.c i ω * sk.hU.w i (configFlip n σ) = sk.hU.c i ω * sk.hU.w i σ := by
    by_cases hi : sk.hU.τ i = 0
    · have hm := sk.hU.c_gauss i
      change Measure.map (sk.hU.c i) ℙ = gaussianReal 0 (sk.hU.τ i) at hm
      have hz : ∀ᵐ z ∂Measure.map (sk.hU.c i) ℙ, z = 0 := by
        rw [hm, hi, gaussianReal_zero_var]
        simp
      have hz' : ∀ᵐ ω, sk.hU.c i ω = 0 := ae_of_ae_map (sk.hU.c_meas i).aemeasurable hz
      filter_upwards [hz'] with ω hω
      simp [hω]
    · exact Filter.Eventually.of_forall fun ω σ =>
        congrArg (fun x => sk.hU.c i ω * x)
          (mixedDisorder_basis_even_of_variance_ne_zero ξ sk i hi σ)
  filter_upwards [Filter.eventually_all.mpr hc] with ω hω
  intro σ
  have Hrepr := congrFun sk.hU.repr ω
  rw [Hrepr]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => hω i σ

 theorem mixedConstrainedPhi_initial_zero_reflection {n k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (sk : MixedDisorder (Ω:=Ω) n ξ) (hq : s.q 1=0) (t u : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) 0 sk.U (k+1) t u=
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) 0 sk.U (k+1) t (-u) := by
  unfold constrainedPhi
  congr 1
  apply integral_congr_ae
  filter_upwards [mixedDisorder_even_ae ξ sk] with sample hsample
  exact constrainedCascade_initial_zero_reflection (mixedClockScheme ξ s) (mixedBeta ξ)
    (by simp [mixedClockScheme_q,hq,ξ.clock_zero]) (sk.U sample) hsample t u

end FourPapersCommon
