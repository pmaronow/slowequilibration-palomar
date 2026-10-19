module
public import FourPapersCommon.MixedSchemeReduction

@[expose] public section

/-! Exact mixed-model strictness reductions. The smaller scheme is selected
before the probability space, the system size, and the interpolation parameter.
Its actual functional, scalar target, and finite interpolation are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1000000

theorem exists_strict_mass_mixed_reduction {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s') = mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ∧
      (∀ t, mixedInterpolationPsi ξ s' h t = mixedInterpolationPsi ξ s h t) ∧
      (∀ (Ω : Type u) [MeasureSpace Ω], ∀ n (U : Ω → EnergySpace n) t, t ∈ Icc (0 : ℝ) 1 →
        guerraPhi n (mixedClockScheme ξ s') (mixedBeta ξ) h U t =
          guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t) ∧
      ((∀ s'' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
          mixedFunctional ξ h (Paper.parisiSchemeMeasure s'')) →
        ∀ s'' : RSBScheme l, mixedFunctional ξ h (Paper.parisiSchemeMeasure s') ≤
          mixedFunctional ξ h (Paper.parisiSchemeMeasure s'')) := by
  classical
  induction k with
  | zero =>
    refine ⟨0, le_rfl, s, ?_, rfl, fun _ => rfl, ?_, fun H => H⟩
    · intro p hp
      have he : p = 0 := by omega
      subst p
      rw [s.m_zero, show s.m (0 + 1) = 1 from s.m_top]
      norm_num
    · intro Ω _ n U t ht
      rfl
  | succ k ih =>
    by_cases H : ∀ p, p ≤ k + 1 → s.m p < s.m (p + 1)
    · refine ⟨k + 1, le_rfl, s, H, rfl, fun _ => rfl, ?_, fun H => H⟩
      intro Ω _ n U t ht
      rfl
    · push Not at H
      obtain ⟨p, hp, hle⟩ := H
      have hm : s.m p = s.m (p + 1) := le_antisymm (s.m_mono p hp) hle
      obtain ⟨l, hl, s', hstrict, hf, hpsi, hphi, hmin⟩ := ih (s.mergeEqualMass p hp hm)
      refine ⟨l, hl.trans (Nat.le_succ k), s', hstrict,
        hf.trans (mixedFunctional_mergeEqualMass ξ s p hp hm h), ?_, ?_, ?_⟩
      · intro t
        exact (hpsi t).trans (mixedInterpolationPsi_mergeEqualMass ξ s p hp hm h t)
      · intro Ω _ n U t ht
        exact (hphi Ω n U t ht).trans (mixedGuerraPhi_mergeEqualMass ξ s p hp hm h U ht)
      · intro Hmin
        exact hmin (mixed_minimizer_mergeEqualMass ξ s p hp hm h Hmin)

theorem exists_strict_overlap_mixed_reduction {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1)) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      (∀ p, 1 ≤ p → p ≤ l → s'.q p < s'.q (p + 1)) ∧
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s') = mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ∧
      (∀ t, mixedInterpolationPsi ξ s' h t = mixedInterpolationPsi ξ s h t) ∧
      (∀ (Ω : Type u) [MeasureSpace Ω], ∀ n (U : Ω → EnergySpace n) t, t ∈ Icc (0 : ℝ) 1 →
        guerraPhi n (mixedClockScheme ξ s') (mixedBeta ξ) h U t =
          guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t) ∧
      ((∀ s'' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
          mixedFunctional ξ h (Paper.parisiSchemeMeasure s'')) →
        ∀ s'' : RSBScheme l, mixedFunctional ξ h (Paper.parisiSchemeMeasure s') ≤
          mixedFunctional ξ h (Paper.parisiSchemeMeasure s'')) := by
  classical
  induction k with
  | zero =>
    refine ⟨0, le_rfl, s, hmass, (fun p hp hp' => by omega), rfl, fun _ => rfl, ?_, fun H => H⟩
    intro Ω _ n U t ht
    rfl
  | succ k ih =>
    by_cases H : ∀ p, 1 ≤ p → p ≤ k + 1 → s.q p < s.q (p + 1)
    · refine ⟨k + 1, le_rfl, s, hmass, H, rfl, fun _ => rfl, ?_, fun H => H⟩
      intro Ω _ n U t ht
      rfl
    · push Not at H
      obtain ⟨p, hp0, hp, hle⟩ := H
      have hq : s.q (p + 1) = s.q p := le_antisymm hle (s.q_mono p (by omega))
      obtain ⟨l, hl, s', hm', hq', hf, hpsi, hphi, hmin⟩ :=
        ih (s.mergeEqualOverlap p hp0 hp hq) (s.mergeEqualOverlap_strict_mass p hp0 hp hq hmass)
      refine ⟨l, hl.trans (Nat.le_succ k), s', hm', hq',
        hf.trans (mixedFunctional_mergeEqualOverlap ξ s p hp0 hp hq h), ?_, ?_, ?_⟩
      · intro t
        exact (hpsi t).trans (mixedInterpolationPsi_mergeEqualOverlap ξ s p hp0 hp hq h t)
      · intro Ω _ n U t ht
        exact (hphi Ω n U t ht).trans (mixedGuerraPhi_mergeEqualOverlap ξ s p hp0 hp hq h U ht)
      · intro Hmin
        exact hmin (mixed_minimizer_mergeEqualOverlap ξ s p hp0 hp hq h Hmin)

theorem exists_strict_mass_overlap_mixed_reduction {k : ℕ} (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      (∀ p, 1 ≤ p → p ≤ l → s'.q p < s'.q (p + 1)) ∧
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s') = mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ∧
      (∀ t, mixedInterpolationPsi ξ s' h t = mixedInterpolationPsi ξ s h t) ∧
      (∀ (Ω : Type u) [MeasureSpace Ω], ∀ n (U : Ω → EnergySpace n) t, t ∈ Icc (0 : ℝ) 1 →
        guerraPhi n (mixedClockScheme ξ s') (mixedBeta ξ) h U t =
          guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t) ∧
      ((∀ s'' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
          mixedFunctional ξ h (Paper.parisiSchemeMeasure s'')) →
        ∀ s'' : RSBScheme l, mixedFunctional ξ h (Paper.parisiSchemeMeasure s') ≤
          mixedFunctional ξ h (Paper.parisiSchemeMeasure s'')) := by
  obtain ⟨j, hj, sj, hmj, hfj, hpsij, hphij, hminj⟩ := exists_strict_mass_mixed_reduction ξ s h
  obtain ⟨l, hl, s', hm', hq', hf, hpsi, hphi, hmin⟩ := exists_strict_overlap_mixed_reduction ξ sj h hmj
  refine ⟨l, hl.trans hj, s', hm', hq', hf.trans hfj,
    fun t => (hpsi t).trans (hpsij t), ?_, fun H => hmin (hminj H)⟩
  intro Ω _ n U t ht
  exact (hphi Ω n U t ht).trans (hphij Ω n U t ht)

end FourPapersCommon
