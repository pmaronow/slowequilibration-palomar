module
public import FourPapersCommon.MixedSignedInitialInterpolation
public import Targets.Section5SignedInitialOffDiagonalEndpoint

@[expose] public section

/-! The retained-field signed initial comparison uses the original physical
constraint and multiplier, while its auxiliary fields use the mixed clock. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators
namespace FourPapersCommon
variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

noncomputable def mixedSignedInitialFieldEndpointOffDiagonal
    (n : ℕ) (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (h t u v : ℝ) : ℝ :=
  section5SignedInitialFieldEndpointOffDiagonal n (mixedClockScheme ξ s)
    (mixedBeta ξ) h t u (ξ.clock v)

theorem mixedSignedInitialInterpolationOffDiagonal_zero
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] :
    mixedSignedInitialInterpolationOffDiagonal n ξ s h sk.U t u v 0 =
      mixedSignedInitialFieldEndpointOffDiagonal n ξ s h t u v := by
  rw [← mixedSignedInitialInterpolationOffDiagonal_eq_direct ξ s h sk
    ht hu hv (w := 0) ⟨le_rfl, zero_le_one⟩]
  simp only [mixedSignedInitialInterpolationOffDiagonalDirect, zero_mul,
    Real.sqrt_zero, zero_smul, section5InterpolationVariance_zero, clock_neg,
    sub_neg_eq_add, integral_const, probReal_univ, smul_eq_mul, one_mul,
    mixedSignedInitialFieldEndpointOffDiagonal, section5SignedInitialFieldEndpointOffDiagonal,
    section5Mass, mixedClockScheme_m]

theorem mixedSignedInitialFieldEndpointOffDiagonal_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {t u v : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) (hu' : ∃ σ τ : Config n, overlap n σ τ = u)
    (ell : ℝ) :
    mixedSignedInitialFieldEndpointOffDiagonal n ξ s h t u v ≤
      2 * Real.log 2 + section5RetainedSignedInitialV (mixedClockScheme ξ s) (mixedBeta ξ) h
        (t * ((mixedBeta ξ)^2 * ((mixedClockScheme ξ s).q 1 + ξ.clock v)))
        ((1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
        (t*((mixedBeta ξ)^2*(-ξ.clock v))) ell - ell*u :=
  section5SignedInitialFieldEndpointOffDiagonal_le hn (mixedClockScheme ξ s)
    (mixedBeta ξ) h ht hu (clock_mem_signed_initial ξ s hv) hu' ell

/-- Genuine signed constrained-pressure upper bound, including the retained
positive frozen field and the physical tangent-remainder error. -/
theorem mixedSignedInitial_constrainedPhi_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] (ell : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u ≤
      2 * Real.log 2 + section5RetainedSignedInitialV (mixedClockScheme ξ s) (mixedBeta ξ) h
        (t * ((mixedBeta ξ)^2 * ((mixedClockScheme ξ s).q 1 + ξ.clock v)))
        ((1-t)*((mixedBeta ξ)^2*(mixedClockScheme ξ s).q 1))
        (t*((mixedBeta ξ)^2*(-ξ.clock v))) ell - ell*u -
      t*(2*mixedSchemeCorrection ξ s)+t*ξ.tangentRemainder u v := by
  have he:=mixedSignedInitialInterpolationOffDiagonal_endpoint_bound hn ξ s h sk ht hu hv
  rw [mixedSignedInitialInterpolationOffDiagonal_zero ξ s h sk ht hu hv] at he
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have hh:=mixedSignedInitialFieldEndpointOffDiagonal_le hn ξ s h ht hu hv
    ⟨p.val.1,p.val.2,p.property⟩ ell
  linarith

end FourPapersCommon
