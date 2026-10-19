module
public import FRSB.MeasureApproximation
public import FRSB.CDFMeasureExt
public import Paper.ParisiSchemeMeasure
public import Paper.ParisiPDEFormula
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Every actual finite overlap law has a finite RSB scheme

Sorted support points, supplemented by zero and one, give literal overlap
nodes. Repeated endpoints retain endpoint atoms and satisfy the backend's
compulsory endpoint masses. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Classical Topology
namespace FRSB
open Paper SpinGlass.Targets

def overlapZero : Overlap := ⟨0, by constructor <;> norm_num⟩
def overlapOne : Overlap := ⟨1, by constructor <;> norm_num⟩

def finiteLawNodes (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite) :
    Finset Overlap := insert overlapZero (insert overlapOne hμ.toFinset)

theorem finiteLawNodes_card_pos (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) : 0 < (finiteLawNodes μ hμ).card :=
  Finset.card_pos.mpr ⟨overlapZero, by simp [finiteLawNodes]⟩

def finiteLawNodeEmbedding (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite) :
    Fin (finiteLawNodes μ hμ).card ↪o Overlap := (finiteLawNodes μ hμ).orderEmbOfFin rfl

theorem finiteLawNodeEmbedding_zero (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    finiteLawNodeEmbedding μ hμ ⟨0, finiteLawNodes_card_pos μ hμ⟩ = overlapZero := by
  let e := (finiteLawNodes μ hμ).orderIsoOfFin rfl
  let j := e.symm ⟨overlapZero, by simp [finiteLawNodes]⟩
  have hj : finiteLawNodeEmbedding μ hμ j = overlapZero := by
    change (e (e.symm _)).val = _
    simp
  apply Subtype.ext
  apply le_antisymm
  · have he := (finiteLawNodeEmbedding μ hμ).monotone
      (show (⟨0, finiteLawNodes_card_pos μ hμ⟩ : Fin _) ≤ j by exact Nat.zero_le _)
    rw [hj] at he
    exact he
  · exact (finiteLawNodeEmbedding μ hμ _).property.1

theorem finiteLawNodeEmbedding_last (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    finiteLawNodeEmbedding μ hμ
      ⟨(finiteLawNodes μ hμ).card - 1, Nat.sub_lt (finiteLawNodes_card_pos μ hμ) (by omega)⟩ =
        overlapOne := by
  let e := (finiteLawNodes μ hμ).orderIsoOfFin rfl
  let j := e.symm ⟨overlapOne, by simp [finiteLawNodes]⟩
  have hj : finiteLawNodeEmbedding μ hμ j = overlapOne := by
    change (e (e.symm _)).val = _
    simp
  apply Subtype.ext
  apply le_antisymm
  · exact (finiteLawNodeEmbedding μ hμ _).property.2
  · have hjle : j.val ≤ (finiteLawNodes μ hμ).card - 1 := by
      have := j.isLt
      omega
    have he := (finiteLawNodeEmbedding μ hμ).monotone
      (show j ≤ (⟨(finiteLawNodes μ hμ).card - 1,
        Nat.sub_lt (finiteLawNodes_card_pos μ hμ) (by omega)⟩ : Fin _) from hjle)
    rw [hj] at he
    exact he

def finiteLawSchemeOverlap (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (p : ℕ) : ℝ :=
  finiteLawNodeEmbedding μ hμ
    ⟨min (p - 1) ((finiteLawNodes μ hμ).card - 1), by
      have := finiteLawNodes_card_pos μ hμ
      exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt this (by omega))⟩

theorem finiteLawSchemeOverlap_monotone (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) : Monotone (finiteLawSchemeOverlap μ hμ) := by
  intro p q hpq
  exact (finiteLawNodeEmbedding μ hμ).monotone
    (min_le_min_right _ (Nat.sub_le_sub_right hpq 1))

@[simp] theorem finiteLawSchemeOverlap_zero (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) : finiteLawSchemeOverlap μ hμ 0 = 0 := by
  unfold finiteLawSchemeOverlap
  simpa [overlapZero] using congrArg (fun q : Overlap => (q : ℝ))
    (finiteLawNodeEmbedding_zero μ hμ)

@[simp] theorem finiteLawSchemeOverlap_top (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) {p : ℕ}
    (hp : (finiteLawNodes μ hμ).card ≤ p) : finiteLawSchemeOverlap μ hμ p = 1 := by
  unfold finiteLawSchemeOverlap
  have hmin : min (p - 1) ((finiteLawNodes μ hμ).card - 1) =
      (finiteLawNodes μ hμ).card - 1 := min_eq_right (by omega)
  simp only [hmin]
  simpa [overlapOne] using congrArg (fun q : Overlap => (q : ℝ))
    (finiteLawNodeEmbedding_last μ hμ)

def finiteLawSchemeMass (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (p : ℕ) : ℝ :=
  if p = 0 then 0 else parisiCDF μ (finiteLawSchemeOverlap μ hμ p)

theorem finiteLawSchemeMass_monotone (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) : Monotone (finiteLawSchemeMass μ hμ) := by
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · simp [finiteLawSchemeMass, hq]
    · simpa [finiteLawSchemeMass, hq] using parisiCDF_nonneg μ (finiteLawSchemeOverlap μ hμ q)
  · have hq : q ≠ 0 := by omega
    simpa [finiteLawSchemeMass, hp, hq] using
      parisiCDF_monotone μ (finiteLawSchemeOverlap_monotone μ hμ hpq)

def finiteLawRSBScheme (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite) :
    RSBScheme (finiteLawNodes μ hμ).card where
  q := finiteLawSchemeOverlap μ hμ
  q_zero := finiteLawSchemeOverlap_zero μ hμ
  q_top := finiteLawSchemeOverlap_top μ hμ (by omega)
  q_mono := fun p _ => finiteLawSchemeOverlap_monotone μ hμ (Nat.le_succ p)
  m := finiteLawSchemeMass μ hμ
  m_zero := by simp [finiteLawSchemeMass]
  m_top := by
    simp only [finiteLawSchemeMass, show (finiteLawNodes μ hμ).card + 1 ≠ 0 by omega, ite_false]
    rw [finiteLawSchemeOverlap_top μ hμ (by omega)]
    exact parisiCDF_eq_one_of_one_le μ le_rfl
  m_mono := fun p _ => finiteLawSchemeMass_monotone μ hμ (Nat.le_succ p)

theorem finiteLawSchemeOverlap_at_index (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (i : Fin (finiteLawNodes μ hμ).card) :
    finiteLawSchemeOverlap μ hμ (i.val + 1) = (finiteLawNodeEmbedding μ hμ i : ℝ) := by
  unfold finiteLawSchemeOverlap
  have hi : i.val ≤ (finiteLawNodes μ hμ).card - 1 := by have := i.isLt; omega
  simp only [Nat.add_sub_cancel, min_eq_left hi]

/-- The actual probability CDF is constant between consecutive sorted nodes. -/
theorem finiteLawCDF_cell (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite)
    (i : Fin (finiteLawNodes μ hμ).card) (hi : i.val + 1 < (finiteLawNodes μ hμ).card)
    {t : ℝ} (ht : t ∈ Ico (finiteLawNodeEmbedding μ hμ i : ℝ)
      (finiteLawNodeEmbedding μ hμ ⟨i.val + 1, hi⟩ : ℝ)) :
    parisiCDF μ t = parisiCDF μ (finiteLawNodeEmbedding μ hμ i : ℝ) := by
  have heq : {q : Overlap | (q : ℝ) ≤ t} =ᵐ[(μ : Measure Overlap)]
      {q : Overlap | q ≤ finiteLawNodeEmbedding μ hμ i} := by
    filter_upwards [(μ : Measure Overlap).support_mem_ae] with q hq
    have hqS : q ∈ finiteLawNodes μ hμ := by simp [finiteLawNodes, hq]
    let e := (finiteLawNodes μ hμ).orderIsoOfFin rfl
    let j := e.symm ⟨q, hqS⟩
    have hj : finiteLawNodeEmbedding μ hμ j = q := by
      change (e (e.symm _)).val = _
      simp
    apply propext
    constructor
    · intro hqt
      by_contra hn
      have hij : i < j := (finiteLawNodeEmbedding μ hμ).lt_iff_lt.mp (by
        rw [hj]
        exact lt_of_not_ge hn)
      have hnext : (⟨i.val + 1, hi⟩ : Fin _) ≤ j := by
        change i.val + 1 ≤ j.val
        exact Nat.succ_le_of_lt hij
      have he := (finiteLawNodeEmbedding μ hμ).monotone hnext
      rw [hj] at he
      have heR : (finiteLawNodeEmbedding μ hμ ⟨i.val + 1, hi⟩ : ℝ) ≤ (q : ℝ) := he
      linarith [ht.2]
    · intro hqi
      exact (show (q : ℝ) ≤ (finiteLawNodeEmbedding μ hμ i : ℝ) from hqi).trans ht.1
  unfold parisiCDF
  rw [measure_congr heq]
  rfl

/-- Exact probability-law representation, including the two endpoint atoms. -/
theorem parisiSchemeMeasure_finiteLawRSBScheme (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    parisiSchemeMeasure (finiteLawRSBScheme μ hμ) = μ := by
  apply eq_of_parisiCDF_ae_eq
  apply Eventually.of_forall
  intro t
  by_cases ht0 : t < 0
  · rw [parisiCDF_eq_zero_of_lt_zero _ ht0, parisiCDF_eq_zero_of_lt_zero _ ht0]
  by_cases ht1 : 1 ≤ t
  · rw [parisiCDF_eq_one_of_one_le _ ht1, parisiCDF_eq_one_of_one_le _ ht1]
  have ht : 0 ≤ t ∧ t < 1 := ⟨not_lt.mp ht0, not_le.mp ht1⟩
  let A : Finset (Fin (finiteLawNodes μ hμ).card) :=
    Finset.univ.filter (fun i => (finiteLawNodeEmbedding μ hμ i : ℝ) ≤ t)
  have hA : A.Nonempty := by
    refine ⟨⟨0, finiteLawNodes_card_pos μ hμ⟩, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [finiteLawNodeEmbedding_zero]
    exact ht.1
  let i := A.max' hA
  have hiA : i ∈ A := A.max'_mem hA
  have hit : (finiteLawNodeEmbedding μ hμ i : ℝ) ≤ t := (Finset.mem_filter.mp hiA).2
  have hinext : i.val + 1 < (finiteLawNodes μ hμ).card := by
    by_contra hn
    have he : i.val = (finiteLawNodes μ hμ).card - 1 := by have := i.isLt; omega
    have hilast : i = ⟨(finiteLawNodes μ hμ).card - 1,
        Nat.sub_lt (finiteLawNodes_card_pos μ hμ) (by omega)⟩ := Fin.ext he
    rw [hilast, finiteLawNodeEmbedding_last] at hit
    exact ht.2.not_ge hit
  have hnxt : t < (finiteLawNodeEmbedding μ hμ ⟨i.val + 1, hinext⟩ : ℝ) := by
    by_contra hn
    have hjA : (⟨i.val + 1, hinext⟩ : Fin _) ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_lt.mp hn
    have hjle := A.le_max' _ hjA
    change i.val + 1 ≤ i.val at hjle
    omega
  have hcell : t ∈ Ico ((finiteLawRSBScheme μ hμ).q (i.val + 1))
      ((finiteLawRSBScheme μ hμ).q (i.val + 1 + 1)) := by
    change t ∈ Ico (finiteLawSchemeOverlap μ hμ (i.val + 1))
      (finiteLawSchemeOverlap μ hμ (i.val + 1 + 1))
    rw [finiteLawSchemeOverlap_at_index]
    have he := finiteLawSchemeOverlap_at_index μ hμ ⟨i.val + 1, hinext⟩
    rw [he]
    exact ⟨hit, hnxt⟩
  rw [parisiCDF_scheme_cell (finiteLawRSBScheme μ hμ) (by have := i.isLt; omega) hcell]
  change finiteLawSchemeMass μ hμ (i.val + 1) = _
  simp only [finiteLawSchemeMass, show i.val + 1 ≠ 0 by omega, ite_false,
    finiteLawSchemeOverlap_at_index]
  exact (finiteLawCDF_cell μ hμ i hinext ⟨hit, hnxt⟩).symm

theorem exists_RSBScheme_of_finite_support (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    ∃ k, ∃ s : RSBScheme k, parisiSchemeMeasure s = μ :=
  ⟨(finiteLawNodes μ hμ).card, finiteLawRSBScheme μ hμ,
    parisiSchemeMeasure_finiteLawRSBScheme μ hμ⟩

def preservingRSBScheme (μ : ParisiMeasure) (S : Finset Overlap) (n : ℕ) :
    RSBScheme (finiteLawNodes (preservingMeasure μ S n) (finite_support_preservingMeasure μ S n)).card :=
  finiteLawRSBScheme (preservingMeasure μ S n) (finite_support_preservingMeasure μ S n)

theorem parisiSchemeMeasure_preservingRSBScheme (μ : ParisiMeasure)
    (S : Finset Overlap) (n : ℕ) :
    parisiSchemeMeasure (preservingRSBScheme μ S n) = preservingMeasure μ S n :=
  parisiSchemeMeasure_finiteLawRSBScheme _ _

theorem parisiGradient_finiteLawRSBScheme (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite) :
    parisiGradient β μ = parisiFiniteGradient (finiteLawRSBScheme μ hμ) β := by
  simpa only [parisiSchemeMeasure_finiteLawRSBScheme] using
    parisiSchemeGradient_eq_actual (finiteLawRSBScheme μ hμ) β hβ

theorem parisiPotential_finiteLawRSBScheme (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiPotential β μ (t, x) = parisiFinitePotential (finiteLawRSBScheme μ hμ) β (t, x) := by
  simpa only [parisiSchemeMeasure_finiteLawRSBScheme] using
    parisiSchemePotential_eq_actual (finiteLawRSBScheme μ hμ) β hβ t x ht

end FRSB
