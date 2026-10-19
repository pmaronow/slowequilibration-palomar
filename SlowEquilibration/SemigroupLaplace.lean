-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# The actual Bochner Laplace integral of a contraction semigroup

These generic constructions integrate the operators supplied by a strongly
continuous contraction semigroup. They do not presume a spectral basis or
identify the integral with the spherical variational resolvent.
-/

namespace SlowEquilibration.SemigroupLaplace

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  P : ℝ≥0 → E →L[ℝ] E
  zero : P 0 = ContinuousLinearMap.id ℝ E
  add : ∀ s t, P (s + t) = (P s).comp (P t)
  norm_le : ∀ t x, ‖P t x‖ ≤ ‖x‖
  continuous : ∀ x, Continuous (fun t => P t x)

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Data
variable (S : Data E)
set_option backward.isDefEq.respectTransparency false

def integrand (x : E) (t : ℝ) : E := Real.exp (-t) • S.P t.toNNReal x

omit [CompleteSpace E] in
theorem integrand_continuous (x : E) : Continuous (S.integrand x) :=
  (Real.continuous_exp.comp continuous_neg).smul
    ((S.continuous x).comp (by fun_prop))

omit [CompleteSpace E] in
theorem integrand_norm_le (x : E) (t : ℝ) :
    ‖S.integrand x t‖ ≤ Real.exp (-t) * ‖x‖ := by
  rw [integrand, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (S.norm_le _ _) (Real.exp_pos _).le

omit [CompleteSpace E] in
theorem integrand_integrable (x : E) : IntegrableOn (S.integrand x) (Ioi 0) :=
  ((integrableOn_exp_neg_Ioi 0).mul_const ‖x‖).mono'
    (S.integrand_continuous x).aestronglyMeasurable
    (ae_of_all _ (S.integrand_norm_le x))

def value (x : E) : E := ∫ t : ℝ in Ioi 0, S.integrand x t

omit [CompleteSpace E] in
theorem value_norm_le (x : E) : ‖S.value x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖S.integrand x t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0, Real.exp (-t) * ‖x‖ :=
      integral_mono (S.integrand_integrable x).norm
        ((integrableOn_exp_neg_Ioi 0).mul_const ‖x‖) (S.integrand_norm_le x)
    _ = ‖x‖ := by rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

omit [CompleteSpace E] in
theorem value_add (x y : E) : S.value (x + y) = S.value x + S.value y := by
  unfold value
  have he : S.integrand (x + y) = S.integrand x + S.integrand y := by
    funext t
    simp [integrand, map_add, smul_add]
  rw [he]
  exact integral_add (S.integrand_integrable x) (S.integrand_integrable y)

omit [CompleteSpace E] in
theorem value_smul (a : ℝ) (x : E) : S.value (a • x) = a • S.value x := by
  unfold value
  have he : S.integrand (a • x) = a • S.integrand x := by
    funext t
    simp only [integrand, map_smul, Pi.smul_apply]
    exact smul_comm _ _ _
  rw [he]
  exact integral_smul a (S.integrand x)

def operator : E →L[ℝ] E := LinearMap.mkContinuous
  { toFun := S.value
    map_add' := S.value_add
    map_smul' := S.value_smul }
  1 (fun x => by simpa using S.value_norm_le x)

omit [CompleteSpace E] in
@[simp] theorem operator_apply (x : E) : S.operator x = S.value x := rfl

omit [CompleteSpace E] in
theorem operator_norm_le : ‖S.operator‖ ≤ 1 :=
  S.operator.opNorm_le_bound zero_le_one (fun x => by simpa using S.value_norm_le x)

theorem operator_commutes (s : ℝ≥0) (x : E) : S.operator (S.P s x) = S.P s (S.operator x) := by
  simp only [operator_apply, value]
  rw [← (S.P s).integral_comp_comm (S.integrand_integrable x)]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change Real.exp (-t) • S.P t.toNNReal (S.P s x) =
      S.P s (Real.exp (-t) • S.P t.toNNReal x)
    rw [map_smul]
    congr 1
    have he := congrArg (fun L : E →L[ℝ] E => L x) (S.add t.toNNReal s)
    have he' := congrArg (fun L : E →L[ℝ] E => L x) (S.add s t.toNNReal)
    rw [add_comm s t.toNNReal] at he'
    simpa only [ContinuousLinearMap.comp_apply] using he.symm.trans he')

end Data
end Banach

namespace Data
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (S : Data E)
set_option backward.isDefEq.respectTransparency false

theorem inner_operator_right (x y : E) :
    inner ℝ x (S.operator y) = ∫ t : ℝ in Ioi 0, inner ℝ x (S.integrand y t) := by
  exact ((innerSL ℝ x).integral_comp_comm (S.integrand_integrable y)).symm

theorem inner_operator_left (x y : E) :
    inner ℝ (S.operator x) y = ∫ t : ℝ in Ioi 0, inner ℝ (S.integrand x t) y := by
  rw [real_inner_comm, S.inner_operator_right]
  congr 1
  funext t
  exact real_inner_comm _ _

theorem operator_isSymmetric
    (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric) : S.operator.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (S.operator x) y = inner ℝ x (S.operator y)
  rw [S.inner_operator_left, S.inner_operator_right]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    simp only [integrand, real_inner_smul_left, real_inner_smul_right]
    exact congrArg (fun a : ℝ => Real.exp (-t) * a) (hSym t.toNNReal x y))

theorem operator_isSelfAdjoint
    (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric) : IsSelfAdjoint S.operator :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (S.operator_isSymmetric hSym)

omit [CompleteSpace E] in
theorem semigroup_inner_self (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric)
    (t : ℝ≥0) (x : E) : inner ℝ (S.P t x) x = ‖S.P (t / 2) x‖ ^ 2 := by
  have ht : t / 2 + t / 2 = t := by ring
  calc
    _ = inner ℝ (S.P (t / 2) (S.P (t / 2) x)) x := by
      have he := congrArg (fun L : E →L[ℝ] E => inner ℝ (L x) x) (S.add (t / 2) (t / 2))
      simpa only [ht, ContinuousLinearMap.comp_apply] using he
    _ = inner ℝ (S.P (t / 2) x) (S.P (t / 2) x) := hSym (t / 2) _ _
    _ = _ := real_inner_self_eq_norm_sq _

theorem inner_operator_self_integral (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric)
    (x : E) : inner ℝ (S.operator x) x =
      ∫ t : ℝ in Ioi 0, Real.exp (-t) * ‖S.P (t.toNNReal / 2) x‖ ^ 2 := by
  rw [S.inner_operator_left]
  congr 1
  funext t
  simp only [integrand, real_inner_smul_left, S.semigroup_inner_self hSym]

theorem operator_nonnegative (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric)
    (x : E) : 0 ≤ inner ℝ (S.operator x) x := by
  rw [S.inner_operator_self_integral hSym]
  exact integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

theorem inner_operator_self_eq_zero_iff
    (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric) (x : E) :
    inner ℝ (S.operator x) x = 0 ↔ x = 0 := by
  refine ⟨fun hz => ?_, fun hx => by simp [hx]⟩
  let φ : ℝ → ℝ := fun t => Real.exp (-t) * ‖S.P (t.toNNReal / 2) x‖ ^ 2
  have hφ : Continuous φ := by
    apply (Real.continuous_exp.comp continuous_neg).mul
    exact (((S.continuous x).comp (by fun_prop)).norm).pow 2
  have hi : IntegrableOn φ (Ioi 0) := by
    apply ((innerSL ℝ x).integrable_comp (S.integrand_integrable x)).congr
    exact ae_of_all _ (fun t => by
      change inner ℝ x (Real.exp (-t) • S.P t.toNNReal x) = _
      rw [real_inner_smul_right]
      change Real.exp (-t) * inner ℝ x (S.P t.toNNReal x) =
        Real.exp (-t) * ‖S.P (t.toNNReal / 2) x‖ ^ 2
      rw [← real_inner_comm x (S.P t.toNNReal x), S.semigroup_inner_self hSym])
  have hzero : (∫ t : ℝ in Ioi 0, φ t) = 0 := by
    exact (S.inner_operator_self_integral hSym x).symm.trans hz
  have hae : φ =ᵐ[volume.restrict (Ioi 0)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hi).mp hzero
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hφ.continuousOn continuous_const.continuousOn
  have hclosed : IsClosed {t : ℝ | φ t = 0} := isClosed_eq hφ continuous_const
  have hcl : closure (Ioi (0 : ℝ)) ⊆ {t : ℝ | φ t = 0} := closure_minimal heq hclosed
  have h0 := hcl (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) by rw [closure_Ioi]; exact self_mem_Ici)
  have hn : ‖x‖ ^ 2 = 0 := by simpa [φ, S.zero] using h0
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem operator_injective (hSym : ∀ t, (S.P t).toLinearMap.IsSymmetric) :
    Function.Injective S.operator := by
  intro x y hxy
  have hz : S.operator (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hinner : inner ℝ (S.operator (x - y)) (x - y) = 0 := by rw [hz, inner_zero_left]
  exact sub_eq_zero.mp ((S.inner_operator_self_eq_zero_iff hSym (x - y)).mp hinner)

end Data
end
end SlowEquilibration.SemigroupLaplace
