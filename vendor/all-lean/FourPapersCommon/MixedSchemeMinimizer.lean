module
public import FourPapersCommon.MixedScheme
public import FourPapersCommon.MixedMinimizer

@[expose] public section

/-! Genuine fixed-level atomic minimizers, with all endpoint degeneracies retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass.Targets Set
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 600000

def admissibleSchemeMeasure (k : ℕ) (p : admissible k) : Paper.ParisiMeasure :=
  Paper.parisiSchemeMeasure (schemeOfPair p.val p.property)

theorem continuous_admissibleSchemeAtom (k : ℕ) (i : Fin (k + 1)) :
    Continuous (fun p : admissible k => Paper.parisiSchemeAtom (schemeOfPair p.val p.property) i) := by
  have hc : Continuous (fun p : admissible k => p.val.2 ((i : ℕ) + 1)) := by fun_prop
  exact hc.subtype_mk _

theorem integral_admissibleSchemeMeasure (k : ℕ) (p : admissible k)
    (f : Paper.Overlap → ℝ) :
    (∫ q, f q ∂(admissibleSchemeMeasure k p : Measure Paper.Overlap)) =
      ∑ i : Fin (k + 1), (p.val.1 (i + 1) - p.val.1 i) *
        f (Paper.parisiSchemeAtom (schemeOfPair p.val p.property) i) := by
  change (∫ q, f q ∂Paper.parisiSchemeRawMeasure (schemeOfPair p.val p.property)) = _
  rw [Paper.parisiSchemeRawMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ((schemeOfPair p.val p.property).m_mono i (by omega)))]
    rfl
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem continuous_admissibleSchemeMeasure (k : ℕ) : Continuous (admissibleSchemeMeasure k) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have he : (fun p : admissible k => ∫ q, f q ∂(admissibleSchemeMeasure k p : Measure Paper.Overlap)) =
      fun p => ∑ i : Fin (k + 1), (p.val.1 (i + 1) - p.val.1 i) *
        f (Paper.parisiSchemeAtom (schemeOfPair p.val p.property) i) := by
    funext p
    exact integral_admissibleSchemeMeasure k p f
  rw [he]
  apply continuous_finsetSum
  intro i _
  have hm : Continuous (fun p : admissible k => p.val.1 ((i : ℕ) + 1) - p.val.1 (i : ℕ)) := by fun_prop
  exact hm.mul (f.continuous.comp (continuous_admissibleSchemeAtom k i))

theorem schemeMeasure_toPair {k : ℕ} (s : RSBScheme k) :
    admissibleSchemeMeasure k ⟨s.toPair, s.toPair_mem⟩ = Paper.parisiSchemeMeasure s := by
  apply Subtype.ext
  change Paper.parisiSchemeRawMeasure (schemeOfPair s.toPair s.toPair_mem) = Paper.parisiSchemeRawMeasure s
  unfold Paper.parisiSchemeRawMeasure
  apply Finset.sum_congr rfl
  intro i _
  have hm0 : (schemeOfPair s.toPair s.toPair_mem).m i = s.m i := by
    change s.m (min i (k + 1)) = s.m i
    rw [Nat.min_eq_left (by omega)]
  have hm1 : (schemeOfPair s.toPair s.toPair_mem).m (i + 1) = s.m (i + 1) := by
    change s.m (min (i + 1) (k + 1)) = s.m (i + 1)
    rw [Nat.min_eq_left (by omega)]
  have ha : Paper.parisiSchemeAtom (schemeOfPair s.toPair s.toPair_mem) i = Paper.parisiSchemeAtom s i := by
    apply Subtype.ext
    change s.q (min (i + 1) (k + 2)) = s.q (i + 1)
    rw [Nat.min_eq_left (by omega)]
  rw [hm0, hm1, ha]

theorem exists_minimizer_mixedFunctional_scheme (ξ : AdmissibleEvenMixture) (k : ℕ) (h : ℝ) :
    ∃ s : RSBScheme k, ∀ s' : RSBScheme k,
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s') := by
  have hc : Continuous (fun p : admissible k => mixedFunctional ξ h (admissibleSchemeMeasure k p)) :=
    (continuous_mixedFunctional ξ h).comp (continuous_admissibleSchemeMeasure k)
  letI : CompactSpace (admissible k) := isCompact_iff_compactSpace.mp (isCompact_admissible k)
  letI : Nonempty (admissible k) := (admissible_nonempty k).to_subtype
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  refine ⟨schemeOfPair p.val p.property, fun s' => ?_⟩
  have hh := hp (show (⟨s'.toPair, s'.toPair_mem⟩ : admissible k) ∈ univ from mem_univ _)
  change mixedFunctional ξ h (admissibleSchemeMeasure k p) ≤
    mixedFunctional ξ h (admissibleSchemeMeasure k ⟨s'.toPair, s'.toPair_mem⟩) at hh
  rw [schemeMeasure_toPair] at hh
  exact hh

end FourPapersCommon
