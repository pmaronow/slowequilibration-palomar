-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianHermiteMixedDerivative
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Fixed Gaussian chaos mass is bounded by the energy of ordered expected
coordinate derivatives. The argument uses a choice of one tuple representing
each Hermite index, so exact multinomial multiplicities are unnecessary. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianHermiteOrderedEnergy

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open GaussianHermiteDerivative
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem finite_sum_sq_le_of_representation {A T : Type*} [DecidableEq A]
    [Fintype T] [DecidableEq T] (s : Finset A) (R : T → A)
    (c W : A → ℝ) (E : T → ℝ)
    (hex : ∀ a ∈ s, ∃ t, R t = a)
    (hW : ∀ a ∈ s, 1 ≤ W a)
    (hE : ∀ t, E t ^ 2 = W (R t) * c (R t) ^ 2) :
    ∑ a ∈ s, c a ^ 2 ≤ ∑ t, E t ^ 2 := by
  classical
  let d : s → T := fun a => Classical.choose (hex a.val a.property)
  have hd (a : s) : R (d a) = a := Classical.choose_spec (hex a.val a.property)
  have hinj : Function.Injective d := by
    intro a b hab
    apply Subtype.ext
    rw [← hd a, ← hd b, hab]
  have hterm (a : s) : c a ^ 2 ≤ E (d a) ^ 2 := by
    rw [hE, hd]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hW a a.property)) (sq_nonneg (c a))]
  have hfin : ∑ a : s, c a ^ 2 ≤ ∑ t, E t ^ 2 :=
    Finset.sum_le_sum_of_injOn d hinj.injOn (Finset.subset_univ _)
      (fun a _ => hterm a) (fun _ _ _ => sq_nonneg _)
  exact (Finset.sum_coe_sort s _).symm.trans_le hfin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degree-n Hermite indices form the finite image of the ordered tuples. -/
def degreeIndices (n : ℕ) : Finset (ι → ℕ) :=
  Finset.univ.image (fun d : Fin n → ι => raisedIndex n d 0)

@[simp] theorem mem_degreeIndices (n : ℕ) (a : ι → ℕ) :
    a ∈ degreeIndices n ↔ degree a = n := by
  classical
  constructor
  · intro ha
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp ha
    simpa [degree] using degree_raisedIndex n d (0 : ι → ℕ)
  · intro ha
    obtain ⟨d, hd⟩ := exists_raisedIndex_zero n a ha
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd⟩

/-- Any finite family of degree-n coefficients is controlled by all ordered
n-fold expected coordinate derivatives, with no dimension factor. -/
theorem finite_fixed_degree_coeff_sum_le_ordered
    (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d))
    (hL2 : ∀ n d, MemLp (mixedCoordinatePartial f n d) 2 (γpi ι))
    (n : ℕ) (s : Finset (ι → ℕ)) (hs : ∀ a ∈ s, degree a = n) :
    ∑ a ∈ s, (coeff f a)^2 ≤
      ∑ d : Fin n → ι, (∫ x, mixedCoordinatePartial f n d x ∂γpi ι)^2 := by
  apply finite_sum_sq_le_of_representation s (fun d => raisedIndex n d 0)
    (coeff f) factorialProduct (fun d => ∫ x, mixedCoordinatePartial f n d x ∂γpi ι)
  · intro a ha
    exact exists_raisedIndex_zero n a (hs a ha)
  · intro a _
    exact factorialProduct_one_le a
  · exact integral_mixedCoordinatePartial_square f hjet hL2 n

/-- A finite collection of chaos levels is bounded by the sum of its
ordered derivative energies. In applications the level set is `Icc 1 K`. -/
theorem finite_coeff_sum_le_ordered_by_degree
    (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d))
    (hL2 : ∀ n d, MemLp (mixedCoordinatePartial f n d) 2 (γpi ι))
    (s : Finset (ι → ℕ)) (t : Finset ℕ) (hs : ∀ a ∈ s, degree a ∈ t) :
    ∑ a ∈ s, (coeff f a)^2 ≤
      ∑ n ∈ t, ∑ d : Fin n → ι, (∫ x, mixedCoordinatePartial f n d x ∂γpi ι)^2 := by
  classical
  calc
    _ = ∑ n ∈ t, ∑ a ∈ s.filter (fun a => degree a = n), (coeff f a)^2 :=
      (Finset.sum_fiberwise_of_maps_to hs _).symm
    _ ≤ _ := Finset.sum_le_sum (fun n _ =>
      finite_fixed_degree_coeff_sum_le_ordered f hjet hL2 n _
        (fun a ha => (Finset.mem_filter.mp ha).2))

/-- The full degree-n coefficient mass satisfies the ordered-energy bound. -/
theorem fixed_degree_coeff_sum_le_ordered
    (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d))
    (hL2 : ∀ n d, MemLp (mixedCoordinatePartial f n d) 2 (γpi ι)) (n : ℕ) :
    ∑ a ∈ degreeIndices n, (coeff f a)^2 ≤
      ∑ d : Fin n → ι, (∫ x, mixedCoordinatePartial f n d x ∂γpi ι)^2 :=
  finite_fixed_degree_coeff_sum_le_ordered f hjet hL2 n _
    (fun a ha => (mem_degreeIndices n a).mp ha)

/-- Writing a fixed chaos mass as a tsum does not change its finite value. -/
theorem fixed_degree_tsum_eq_sum (n : ℕ) (c : (ι → ℕ) → ℝ) :
    (∑' a, if degree a = n then c a else 0) = ∑ a ∈ degreeIndices n, c a := by
  classical
  rw [tsum_eq_sum (s := degreeIndices n) (fun a ha => by
    have hnot : degree a ≠ n := fun h => ha ((mem_degreeIndices n a).mpr h)
    simp only [hnot, ite_false])]
  exact Finset.sum_congr rfl (fun a ha => by
    simp only [(mem_degreeIndices n a).mp ha, ite_true])

/-- Tsum version of the fixed-chaos bound, convenient for Parseval splits. -/
theorem fixed_degree_coeff_tsum_le_ordered
    (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d))
    (hL2 : ∀ n d, MemLp (mixedCoordinatePartial f n d) 2 (γpi ι)) (n : ℕ) :
    (∑' a, if degree a = n then (coeff f a)^2 else 0) ≤
      ∑ d : Fin n → ι, (∫ x, mixedCoordinatePartial f n d x ∂γpi ι)^2 := by
  rw [fixed_degree_tsum_eq_sum]
  exact fixed_degree_coeff_sum_le_ordered f hjet hL2 n

/-- Exponential first-jet bounds already supply all L² hypotheses. -/
theorem fixed_degree_coeff_tsum_le_ordered_of_jet
    (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d)) (n : ℕ) :
    (∑' a, if degree a = n then (coeff f a)^2 else 0) ≤
      ∑ d : Fin n → ι, (∫ x, mixedCoordinatePartial f n d x ∂γpi ι)^2 :=
  fixed_degree_coeff_tsum_le_ordered f hjet (fun k d => (hjet k d).memLp_two) n

end SlowEquilibration.GaussianHermiteOrderedEnergy
