module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalFormCore
public import SlowEquilibration.ResolventOperator

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology ContDiff

/-- The actual unbounded nonnegative spherical Gibbs generator. Its domain
is the actual weak resolvent range and its value is `A(Rf)=f-Rf`. -/
def sphericalGenerator {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : Lp ℝ 2 (gibbsLaw N β H) →ₗ.[ℝ] Lp ℝ 2 (gibbsLaw N β H) :=
  ResolventOperator.inverseShift (sphericalL2Resolvent hN β H hH)
    (sphericalL2Resolvent_injective hN β H hH)

@[simp] theorem sphericalGenerator_domain {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    (sphericalGenerator hN β H hH).domain = (sphericalL2Resolvent hN β H hH).range := rfl

theorem sphericalGenerator_apply_resolvent {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    sphericalGenerator hN β H hH ⟨sphericalL2Resolvent hN β H hH f, ⟨f, rfl⟩⟩ =
      f - sphericalL2Resolvent hN β H hH f :=
  ResolventOperator.inverseShift_apply (sphericalL2Resolvent hN β H hH)
    (sphericalL2Resolvent_injective hN β H hH) f

/-- Self-adjointness is proved from the actual injective symmetric weak
resolvent, with no supplied self-adjoint realization. -/
theorem sphericalGenerator_selfAdjoint {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : IsSelfAdjoint (sphericalGenerator hN β H hH) :=
  ResolventOperator.inverseShift_selfAdjoint (sphericalL2Resolvent hN β H hH)
    (sphericalL2Resolvent_injective hN β H hH) (sphericalL2Resolvent_symmetric hN β H hH)

theorem sphericalGenerator_isClosed {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : (sphericalGenerator hN β H hH).IsClosed :=
  (sphericalGenerator_selfAdjoint hN β H hH).isClosed

/-- The actual operator and the actual completed form satisfy the
variational identity on the full actual operator domain. -/
theorem sphericalGenerator_resolvent_form {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H))
    (v : sphericalSobolevGraph hN β H hH) :
    sphericalCompletedDirichlet hN β H hH (sphericalWeakSolution hN β H hH f) v =
      inner ℝ (sphericalGenerator hN β H hH
        ⟨sphericalL2Resolvent hN β H hH f, ⟨f, rfl⟩⟩) (sphericalEnergyL2Map hN β H hH v) := by
  rw [sphericalGenerator_apply_resolvent, inner_sub_left]
  have hs := sphericalWeakSolution_spec hN β H hH f v
  change sphericalCompletedDirichlet hN β H hH (sphericalWeakSolution hN β H hH f) v +
    inner ℝ (sphericalL2Resolvent hN β H hH f) (sphericalEnergyL2Map hN β H hH v) =
      inner ℝ f (sphericalEnergyL2Map hN β H hH v) at hs
  linarith only [hs]

theorem sphericalGenerator_resolvent_energy {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    inner ℝ (sphericalGenerator hN β H hH
      ⟨sphericalL2Resolvent hN β H hH f, ⟨f, rfl⟩⟩) (sphericalL2Resolvent hN β H hH f) =
      sphericalCompletedDirichlet hN β H hH
        (sphericalWeakSolution hN β H hH f) (sphericalWeakSolution hN β H hH f) :=
  (sphericalGenerator_resolvent_form hN β H hH f (sphericalWeakSolution hN β H hH f)).symm

/-- Nonnegativity follows from the actual nonnegative completed gradient
energy, rather than an assumed spectral sign. -/
theorem sphericalGenerator_nonneg {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u : (sphericalGenerator hN β H hH).domain) :
    0 ≤ inner ℝ (sphericalGenerator hN β H hH u) (u : Lp ℝ 2 (gibbsLaw N β H)) := by
  obtain ⟨f, hf⟩ := u.property
  have hu : u = (⟨sphericalL2Resolvent hN β H hH f, ⟨f, rfl⟩⟩ :
      (sphericalGenerator hN β H hH).domain) := Subtype.ext hf.symm
  rw [hu]
  change 0 ≤ inner ℝ (sphericalGenerator hN β H hH
    ⟨sphericalL2Resolvent hN β H hH f, ⟨f, rfl⟩⟩) (sphericalL2Resolvent hN β H hH f)
  rw [sphericalGenerator_resolvent_energy]
  exact sphericalCompletedDirichlet_nonneg hN β H hH _

/-- Every actual energy function satisfying the weak generator equation
belongs to the actual operator domain and has the specified operator value.
This is the converse to the full-domain variational identity. -/
theorem sphericalGenerator_of_weakEquation {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u : sphericalSobolevGraph hN β H hH)
    (k : Lp ℝ 2 (gibbsLaw N β H))
    (he : ∀ v, sphericalCompletedDirichlet hN β H hH u v =
      inner ℝ k (sphericalEnergyL2Map hN β H hH v)) :
    ∃ hu : sphericalEnergyL2Map hN β H hH u ∈ (sphericalGenerator hN β H hH).domain,
      sphericalGenerator hN β H hH ⟨sphericalEnergyL2Map hN β H hH u, hu⟩ = k := by
  let f := k + sphericalEnergyL2Map hN β H hH u
  have hs : u = sphericalWeakSolution hN β H hH f := by
    apply sphericalWeakSolution_unique
    intro v
    rw [he v]
    dsimp [f]
    rw [inner_add_left]
  have hr : sphericalL2Resolvent hN β H hH f = sphericalEnergyL2Map hN β H hH u :=
    congrArg (sphericalEnergyL2Map hN β H hH) hs.symm
  refine ⟨⟨f, hr⟩, ?_⟩
  have hz : (⟨sphericalEnergyL2Map hN β H hH u, ⟨f, hr⟩⟩ :
      (sphericalGenerator hN β H hH).domain) =
      ⟨sphericalL2Resolvent hN β H hH f, ⟨f, rfl⟩⟩ := Subtype.ext hr.symm
  rw [hz, sphericalGenerator_apply_resolvent, hr]
  exact add_sub_cancel_right k _

/-- The proved actual self-adjoint form generator acts as `−L` on every
actual smooth spherical test, with no formal differential identity premise. -/
theorem sphericalGenerator_smooth {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) (g : smoothCore N) :
    ∃ hg : gibbsToL2 hN β H hH.continuous g (smoothCore_contDiff g).continuous ∈
        (sphericalGenerator hN β H hH.continuous).domain,
      sphericalGenerator hN β H hH.continuous
        ⟨gibbsToL2 hN β H hH.continuous g (smoothCore_contDiff g).continuous, hg⟩ =
      -gibbsToL2 hN β H hH.continuous (rotationGenerator N β H g)
        (rotationGenerator_continuous β hH ((smoothCore_contDiff g).of_le (by simp))) := by
  let f := smoothResolventForcing hN β H hH g
  have hr := sphericalL2Resolvent_smoothForcing hN β H hH g
  refine ⟨⟨f, hr⟩, ?_⟩
  have hz : (⟨gibbsToL2 hN β H hH.continuous g (smoothCore_contDiff g).continuous, ⟨f, hr⟩⟩ :
      (sphericalGenerator hN β H hH.continuous).domain) =
      ⟨sphericalL2Resolvent hN β H hH.continuous f, ⟨f, rfl⟩⟩ := Subtype.ext hr.symm
  rw [hz, sphericalGenerator_apply_resolvent, hr]
  have hf : f = gibbsToL2 hN β H hH.continuous g (smoothCore_contDiff g).continuous -
      gibbsToL2 hN β H hH.continuous (rotationGenerator N β H g)
        (rotationGenerator_continuous β hH ((smoothCore_contDiff g).of_le (by simp))) := rfl
  rw [hf]
  abel

end
end SlowEquilibration.SphericalForm
