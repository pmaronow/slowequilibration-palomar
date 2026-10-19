module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Actual finite iid uniform sampling, collision probability, and extension
of a distinct sample to a permutation. These are combinatorial foundations;
no infinite directing-measure representation is assumed here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace OverlapPaper

def iidUniformSamplingLaw (n k : ℕ) (hn : 0 < n) : Measure (Fin k → Fin n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Measure.pi (fun _ : Fin k => (PMF.uniformOfFintype (Fin n)).toMeasure)

instance isProbabilityMeasure_iidUniformSamplingLaw (n k : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (iidUniformSamplingLaw n k hn) := by
  dsimp [iidUniformSamplingLaw]
  infer_instance

theorem iidUniformSamplingLaw_pair_collision (n k : ℕ) (hn : 0 < n)
    (i j : Fin k) (hij : i ≠ j) :
    iidUniformSamplingLaw n k hn {a | a i = a j} = (n : ℝ≥0∞)⁻¹ := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := (PMF.uniformOfFintype (Fin n)).toMeasure
  have hsingle (l : Fin k) (v : Fin n) :
      Measure.pi (fun _ : Fin k => μ) ((Function.eval l) ⁻¹' {v}) = (n : ℝ≥0∞)⁻¹ := by
    rw [(measurePreserving_eval (μ := fun _ : Fin k => μ) l).measure_preimage
      (measurableSet_singleton v).nullMeasurableSet]
    simp [μ, PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton v)]
  have hind : iIndepFun (fun l : Fin k => Function.eval l)
      (Measure.pi (fun _ : Fin k => μ)) :=
    iIndepFun_pi (X := fun _ : Fin k => id) (fun _ => aemeasurable_id)
  have hsets : {a : Fin k → Fin n | a i = a j} =
      ⋃ v : Fin n, ((fun a : Fin k → Fin n => a i) ⁻¹' {v} ∩ (fun a : Fin k → Fin n => a j) ⁻¹' {v}) := by
    ext a
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff,
      Function.eval]
    exact ⟨fun h => ⟨a i, rfl, h.symm⟩, fun ⟨v, hi, hj⟩ => hi.trans hj.symm⟩
  have hdisj : Pairwise (fun v w : Fin n => Disjoint
      ((fun a : Fin k → Fin n => a i) ⁻¹' {v} ∩ (fun a : Fin k → Fin n => a j) ⁻¹' {v})
      ((fun a : Fin k → Fin n => a i) ⁻¹' {w} ∩ (fun a : Fin k → Fin n => a j) ⁻¹' {w})) := by
    intro v w hvw
    rw [Set.disjoint_left]
    intro a ha hb
    exact hvw (ha.1.symm.trans hb.1)
  change Measure.pi (fun _ : Fin k => μ) _ = _
  rw [hsets, measure_iUnion hdisj (fun v =>
    ((measurable_pi_apply i) (measurableSet_singleton v)).inter
      ((measurable_pi_apply j) (measurableSet_singleton v)))]
  simp_rw [(hind.indepFun hij).measure_inter_preimage_eq_mul { _ } { _ }
    (measurableSet_singleton _) (measurableSet_singleton _), hsingle]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [←mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (by simp), one_mul]

def uniformSamplingCollisionRate (n k : ℕ) : ℝ := (k.choose 2 : ℝ) / n

theorem uniformSamplingCollisionRate_eq (n k : ℕ) :
    uniformSamplingCollisionRate n k = (k : ℝ) * ((k : ℝ) - 1) / (2 * n) := by
  rw [uniformSamplingCollisionRate, Nat.cast_choose_two ℝ]
  ring

theorem iidUniformSamplingLaw_noninjective_le (n k : ℕ) (hn : 0 < n) :
    iidUniformSamplingLaw n k hn {a | ¬ Injective a} ≤
      ENNReal.ofReal (uniformSamplingCollisionRate n k) := by
  classical
  let pairs : Finset (Fin k × Fin k) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun ij => ij.1 < ij.2)
  have hsets : {a : Fin k → Fin n | ¬Injective a} =
      ⋃ ij ∈ pairs, {a | a ij.1 = a ij.2} := by
    ext a
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro ha
      obtain ⟨i, j, heq, hne⟩ := not_injective_iff.mp ha
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨(i,j), by simp [pairs,hlt], heq⟩
      · exact ⟨(j,i), by simp [pairs,hlt], heq.symm⟩
    · rintro ⟨⟨i,j⟩, hij, heq⟩ hinj
      have hlt : i < j := (Finset.mem_filter.mp hij).2
      exact hlt.ne (hinj heq)
  rw [hsets]
  calc
    _ ≤ ∑ ij ∈ pairs, iidUniformSamplingLaw n k hn {a | a ij.1 = a ij.2} :=
      measure_biUnion_finset_le pairs _
    _ = (k.choose 2 : ℝ≥0∞) / n := by
      have hpair : ∀ij∈pairs,
          iidUniformSamplingLaw n k hn {a | a ij.1 = a ij.2} = (n : ℝ≥0∞)⁻¹ := by
        intro ij hij
        exact iidUniformSamplingLaw_pair_collision n k hn ij.1 ij.2
          ((Finset.mem_filter.mp hij).2.ne)
      rw [Finset.sum_congr rfl hpair, Finset.sum_const]
      simp only [pairs, Finset.card_product_filter_lt, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, div_eq_mul_inv]
    _ = ENNReal.ofReal (uniformSamplingCollisionRate n k) := by
      rw [uniformSamplingCollisionRate, ENNReal.ofReal_div_of_pos (by exact_mod_cast hn)]
      simp

theorem injective_sample_extends_permutation {n k : ℕ} (hkn : k ≤ n)
    (a : Fin k → Fin n) (ha : Injective a) :
    ∃σ : Equiv.Perm (Fin n), ∀i : Fin k, σ (Fin.castLE hkn i) = a i :=
  Equiv.Perm.exists_extending_pair (Fin.castLE hkn) a (Fin.castLE_injective hkn) ha

theorem iidUniformSamplingLaw_bounded_test {n k : ℕ} (hn : 0 < n)
    (F : (Fin k → Fin n) → ℝ) (a C : ℝ) (hC : 0 ≤ C)
    (hF : ∀x, ‖F x‖ ≤ C) (ha : ‖a‖ ≤ C)
    (hconst : ∀x, Injective x → F x = a) :
    ‖(∫x, F x ∂iidUniformSamplingLaw n k hn) - a‖ ≤
      2 * C * uniformSamplingCollisionRate n k := by
  classical
  let μ := iidUniformSamplingLaw n k hn
  have hint : Integrable F μ := Integrable.of_finite
  have heq : (∫x, F x ∂μ) - a =
      ∫x in {x | ¬Injective x}, F x - a ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hh : Injective x := by simpa using hx
      rw [hconst x hh, sub_self]), integral_sub hint (integrable_const a)]
    simp
  rw [heq]
  have hbound := norm_setIntegral_le_of_norm_le_const
    (μ := μ) (f := fun x => F x - a) (s := {x | ¬Injective x}) (measure_lt_top μ _)
    (C := 2*C) (fun x _ => (norm_sub_le _ _).trans (by linarith [hF x]))
  have hprob : μ.real {x | ¬Injective x} ≤ uniformSamplingCollisionRate n k := by
    have hrate : 0 ≤ uniformSamplingCollisionRate n k := by
      dsimp [uniformSamplingCollisionRate]; positivity
    have hh := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      ENNReal.ofReal_ne_top).mpr (iidUniformSamplingLaw_noninjective_le n k hn)
    simpa [Measure.real, ENNReal.toReal_ofReal hrate] using hh
  exact hbound.trans (mul_le_mul_of_nonneg_left hprob (by positivity))

end OverlapPaper
