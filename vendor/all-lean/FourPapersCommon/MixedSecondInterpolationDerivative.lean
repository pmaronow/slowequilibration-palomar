module
public import FourPapersCommon.MixedSecondInterpolationPathTrace
public import FourPapersCommon.MixedSecondInterpolationIdentity

@[expose] public section

/-! Genuine actual mixed interpolation derivatives in physical-overlap form. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem mixed_first_increment (ξ : AdmissibleEvenMixture) (q c : ℝ) :
    (mixedBeta ξ)^2*(ξ.clock q-ξ.clock c)=ξ.first q-ξ.first c := by
  rw [mixedBeta_sq]
  simp only [AdmissibleEvenMixture.clock]
  field_simp [ξ.variance_pos.ne']

 theorem section5Rho_clock (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (r : ℕ) (u : ℝ) (p : ℕ) :
    section5Rho (mixedClockScheme ξ s) r (ξ.clock u) p=ξ.clock (section5Rho s r u p) := by
  simp only [section5Rho, mixedClockScheme_q]
  split_ifs <;> rfl

 theorem section5RightRho_clock (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (r : ℕ) (u : ℝ) (p : ℕ) :
    section5RightRho (mixedClockScheme ξ s) r (ξ.clock u) p=ξ.clock (section5RightRho s r u p) :=
  section5Rho_clock ξ s (r+1) u p

set_option maxHeartbeats 800000 in
/-- Actual Gaussian-averaged left pressure derivative, with all heat and
disorder terms under the same normalized split-replica weights. -/
theorem hasDerivAt_mixedLeftInterpolation_replica
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedLeftInterpolation ξ s h sk.U r m t u)
      (mixedAveragedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) ξ u t
        (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
        (fun j => -(t * (ξ.first (section5Rho s r u (k + 2 - j + 1)) -
          ξ.first (section5Rho s r u (k + 2 - j)))))
        (k + 3 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  apply (hasDerivAt_mixedLeftInterpolation_trace ξ s h sk.hU hr hm ht hu hw).congr_deriv
  simpa only [section5Rho_clock, section5RightRho_clock, mul_assoc, mixed_first_increment] using!
    normalized_mixed_trace_heat_eq_replica hn ξ t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
    (fun j => -(t * (mixedBeta ξ)^2 * (section5Rho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - j + 1) -
      section5Rho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - j))))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hu) ⟨hw.1.le, hw.2.le⟩)
    (k + 3 - r) (k + 3)
    (fun l _ hz => section5InterpolationVelocity_zero_of_not_pos (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hu) hw.2 hz)
    (fun _ => h) (fun _ => h)

set_option maxHeartbeats 800000 in
/-- Actual Gaussian-averaged right pressure derivative with the dual cutoff.
Zero-mass and coincident-overlap cases are retained. -/
theorem hasDerivAt_mixedRightInterpolation_replica
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedRightInterpolation ξ s h sk.U r m t u)
      (mixedAveragedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) ξ u t
        (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
        (fun j => -(t * (ξ.first (section5RightRho s r u (k + 2 - j + 1)) -
          ξ.first (section5RightRho s r u (k + 2 - j)))))
        (k + 2 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  apply (hasDerivAt_mixedRightInterpolation_trace ξ s h sk.hU hr hm ht hu hw).congr_deriv
  simpa only [section5Rho_clock, section5RightRho_clock, mul_assoc, mixed_first_increment] using!
    normalized_mixed_trace_heat_eq_replica hn ξ t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
    (fun j => -(t * (mixedBeta ξ)^2 * (section5RightRho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - j + 1) -
      section5RightRho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - j))))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hu) ⟨hw.1.le, hw.2.le⟩)
    (k + 2 - r) (k + 3)
    (fun l _ hz => section5RightInterpolationVelocity_zero_of_not_pos (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hu) hw.2 hz)
    (fun _ => h) (fun _ => h)

end FourPapersCommon
