-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.GOEMaximumDeterminant

@[expose] public section

/-! The determinant-weighted Cauchy--Schwarz step in the critical-band Palm
argument. The event may depend on the entire conditioned disorder, including
the same quadratic tensor that enters the intrinsic determinant. -/

namespace SlowEquilibration.SphericalTAPCriticalPalmHolder
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet
open ConditionedDeterminantMoments
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Source equation `mb-palm-cs` under the genuine nonpure conditioned law.
The uniform constant is supplied by physical GOE normalized moments. -/
theorem mixed_critical_determinant_event_bound (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {g Z : ℝ} (hg : 0 < g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (u : Vector (n + 2))
      (hu : ‖u‖ ^ 2 = (n + 2 : ℕ)) (b : EuclideanSpace ℝ (Fin 2)),
      2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) + g ≤ b 1 → b 1 ≤ Z →
      ∀ A : Set (Disorder (n + 2) μ.maxDegree), MeasurableSet A →
      let ν := mixedLaw μ Q u hu b
      let D := intrinsicDet μ Q u
      (∫ J in A, D J ∂ν) ≤
        Real.sqrt C * Real.sqrt (ν.real A) * (∫ J, D J ∂ν) := by
  obtain ⟨C, hC, hM⟩ :=
    mixed_conditioned_determinant_moments μ hQ hnp (Z := Z) (r := 2) hg (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro n u hu b hbg hbZ A hA
  let ν := mixedLaw μ Q u hu b
  let D := intrinsicDet μ Q u
  have hP : IsProbabilityMeasure ν := by
    dsimp [ν, mixedLaw]
    infer_instance
  have hp := hM n u hu b hbg hbZ
  have h := GOEMaximumDeterminant.determinant_event_holder ν D hp.1
    (.of_forall fun _ => abs_nonneg _) hp.2.2.1 A hA hp.2.2.2.1 hp.2.2.2.2
    (le_refl (ν.real A))
  exact (div_le_iff₀ hp.2.2.1).mp h

/-- Proper pure value conditioning yields the same uniform Palm transfer;
the radial mark is the deterministic Euler value `p*h`. -/
theorem pure_critical_determinant_event_bound (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (u : Vector (n + 2))
      (hu : ‖u‖ ^ 2 = (n + 2 : ℕ)) (e : ℝ),
      2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) + g ≤ (p : ℝ) * e →
      (p : ℝ) * e ≤ Z →
      ∀ A : Set (Disorder (n + 2) μ.maxDegree), MeasurableSet A →
      let ν := pureLaw p hp alpha halpha Q u hu e
      let D := intrinsicDet μ Q u
      (∫ J in A, D J ∂ν) ≤
        Real.sqrt C * Real.sqrt (ν.real A) * (∫ J, D J ∂ν) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  obtain ⟨C, hC, hM⟩ :=
    pure_conditioned_determinant_moments p hp alpha halpha hQ (Z := Z) (r := 2)
      hg (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro n u hu e heg heZ A hA
  let ν := pureLaw p hp alpha halpha Q u hu e
  let D := intrinsicDet μ Q u
  have hP : IsProbabilityMeasure ν := by
    dsimp [ν, pureLaw]
    infer_instance
  have hp := hM n u hu e heg heZ
  have h := GOEMaximumDeterminant.determinant_event_holder ν D hp.1
    (.of_forall fun _ => abs_nonneg _) hp.2.2.1 A hA hp.2.2.2.1 hp.2.2.2.2
    (le_refl (ν.real A))
  exact (div_le_iff₀ hp.2.2.1).mp h

end
end SlowEquilibration.SphericalTAPCriticalPalmHolder
