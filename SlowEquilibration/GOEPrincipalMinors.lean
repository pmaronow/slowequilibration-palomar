-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEBorderedDeterminant
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section

/-! # Actual GOE principal minors and polynomial integrability -/

namespace SlowEquilibration.GOEPrincipalMinors

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open OAI.CriticalSK
open scoped ENNReal NNReal BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal extraction of a principal matrix on a genuine ordered subset. -/
def principalMatrix {m n : ℕ} (e : Fin m ↪o Fin n) (A : GaussianMatrix (Fin n)) :
    GaussianMatrix (Fin m) := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A (e i) (e j)))

lemma principalMatrix_measurable {m n : ℕ} (e : Fin m ↪o Fin n) : Measurable (principalMatrix e) := by
  unfold principalMatrix
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  fun_prop

/-- Every actual ordered principal minor has the same GOE variance parameter.
Its whole matrix law, not just entry variances, is identified. -/
theorem principalMatrix_law {m n : ℕ} (e : Fin m ↪o Fin n) (s : ℝ) :
    (goeLaw (Fin n) s).map (principalMatrix e) = goeLaw (Fin m) s := by
  let pe : UpperEntry (Fin m) → UpperEntry (Fin n) := fun p => ⟨(e p.1.1, e p.1.2), e.monotone p.2⟩
  have hpe : Injective pe := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact e.injective (congrArg (fun p : UpperEntry (Fin n) => p.1.1) h)
    · exact e.injective (congrArg (fun p : UpperEntry (Fin n) => p.1.2) h)
  have hind := (goe_entries_independent (ι := Fin n) s).precomp hpe
  have hupper := hind.map_fun_eq_pi_map (fun _ => by fun_prop)
  have hmarg (p : UpperEntry (Fin m)) :
      (goeLaw (Fin n) s).map (fun A => A (e p.1.1) (e p.1.2)) =
        goeUpperMarginal s p := by
    rw [goe_entry_law]
    simp only [goeUpperMarginal, e.injective.eq_iff]
  dsimp only [pe] at hupper
  simp_rw [hmarg] at hupper
  rw [goeLaw_eq_upper_product (ι := Fin m) s]
  change (goeLaw (Fin n) s).map (principalMatrix e) =
    (Measure.pi (goeUpperMarginal (ι := Fin m) s)).map upperWrite
  rw [← hupper, Measure.map_map upperWrite_measurable (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [goe_symmetric_ae (ι := Fin n) s] with A hA
  have hm : ∀ i j, principalMatrix e A i j = principalMatrix e A j i := fun i j => hA _ _
  exact (upperWrite_upperRead (principalMatrix e A) hm).symm

/-- In particular, deleting any one row and the same column preserves the
actual GOE law at the original variance parameter. -/
theorem delete_principal_law (n : ℕ) (i : Fin (n + 1)) (s : ℝ) :
    (goeLaw (Fin (n + 1)) s).map (principalMatrix i.succAboveOrderEmb) = goeLaw (Fin n) s :=
  principalMatrix_law _ s

lemma entry_memLp (n : ℕ) (s : ℝ) (i j : Fin n) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun A : GaussianMatrix (Fin n) => A i j) p (goeLaw (Fin n) s) := by
  have h : HasLaw (fun A : GaussianMatrix (Fin n) => A i j)
      (gaussianReal 0 (if i = j then (4 * s ^ 2).toNNReal else (2 * s ^ 2).toNNReal))
      (goeLaw (Fin n) s) := ⟨(by fun_prop), goe_entry_law s i j⟩
  exact h.hasGaussianLaw.memLp hp

/-- Finite products of actual all-moment scalar observables are genuinely
integrable; no real-valued integral defaults are used. -/
lemma integrable_product_of_all_moments {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (S : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ S, ∀ p : ℝ≥0∞, p ≠ ⊤ → MemLp (f i) p μ) :
    Integrable (fun x => ∏ i ∈ S, f i x) μ := by
  by_cases hS : S.Nonempty
  · have hc : (S.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    have ht : (S.card : ℝ≥0∞) ≠ ⊤ := by simp
    have h := MemLp.fun_prod (p := fun _ : ι => (S.card : ℝ≥0∞))
      (fun i hi => hf i hi _ ht)
    have hexp : (∑ _i ∈ S, (S.card : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel hc ht, inv_one]
    rw [hexp] at h
    exact h.integrable le_rfl
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, Finset.prod_empty]
    exact integrable_const _

/-- Every literal shifted GOE determinant is integrable in every finite
matrix dimension, even where no spectral rare-event estimate is yet small. -/
theorem shifted_determinant_integrable (n : ℕ) (s k : ℝ) :
    Integrable (fun A : GaussianMatrix (Fin n) =>
      (k • (1 : Matrix (Fin n) (Fin n) ℝ) - (Matrix.of fun i j => A i j)).det) (goeLaw (Fin n) s) := by
  simp_rw [Matrix.det_apply']
  apply integrable_finsetSum
  intro σ hσ
  apply Integrable.const_mul
  apply integrable_product_of_all_moments
  intro i hi p hp
  have hg := entry_memLp n s (σ i) i hp
  exact (memLp_const (k * (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i)).sub hg

end
end SlowEquilibration.GOEPrincipalMinors
