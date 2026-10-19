module
public import QuantitativeFollowup.DirectionalConvexity
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-! Actual inversion of a uniformly coercive operator family. Smoothness
and quantitative derivative bounds follow from differentiating its
linear equation, not from assuming inverse-energy regularity. -/
noncomputable section
namespace QuantitativeFollowup

theorem hasDerivAt_vector_on_affine_line {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 2 f) (x z : E) (r : ℝ) :
    HasDerivAt (fun s => f (x+s • z)) (fderiv ℝ f (x+r • z) z) r := by
  apply (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
  simpa only [id_eq,one_smul] using
    ((hasDerivAt_id r).smul_const z |>.const_add x)

theorem hasDerivAt_vector_directional_on_affine_line {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 2 f) (x z : E) (r : ℝ) :
    HasDerivAt (fun s => fderiv ℝ f (x+s • z) z)
      (fderiv ℝ (fderiv ℝ f) (x+r • z) z z) r := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hh := (hd.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).smul_const z |>.const_add x)
  simpa only [Function.comp_apply,map_zero,add_zero,id_eq,one_smul] using
    hh.clm_apply (hasDerivAt_const r z)

theorem isUnit_of_coercive {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hA : ∀ z, r*‖z‖^2 ≤ inner ℝ z (A z)) : IsUnit A := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map A
    (c := ⟨r,hr.le⟩) (by exact_mod_cast hr)
  intro z
  change ‖z‖^2*r ≤ ‖inner ℝ (A z) z‖
  rw [Real.norm_eq_abs,real_inner_comm z (A z)]
  have hh : ‖z‖^2*r ≤ inner ℝ z (A z) := by simpa only [mul_comm] using hA z
  exact hh.trans (le_abs_self _)

theorem norm_ringInverse_le_of_coercive {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (r : ℝ) (hr : 0<r)
    (hA : ∀ z, r*‖z‖^2 ≤ inner ℝ z (A z)) : ‖Ring.inverse A‖ ≤ r⁻¹ := by
  have hu := isUnit_of_coercive A r hr hA
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hr.le)
  intro y
  let z := (Ring.inverse A) y
  have haz : A z=y := by
    have hh := congrArg (fun L : E →L[ℝ] E => L y) (Ring.mul_inverse_cancel A hu)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply,z] using hh
  have hl := hA z
  rw [haz] at hl
  have hcs := real_inner_le_norm z y
  have hnorm : r*‖z‖ ≤ ‖y‖ := by
    by_cases hz : z=0
    · simp [hz, norm_nonneg y]
    · have hp : 0<‖z‖ := norm_pos_iff.mpr hz
      nlinarith
  have hh := (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hnorm)
  simpa only [div_eq_mul_inv,mul_comm,z] using hh

def inverseFamily {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (x : D) : E := (Ring.inverse (A x)) (b x)

theorem contDiff_inverseFamily {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (hA : ContDiff ℝ 2 A)
    (hb : ContDiff ℝ 2 b) (hunit : ∀ x, IsUnit (A x)) :
    ContDiff ℝ 2 (inverseFamily A b) := by
  have hi : ContDiff ℝ 2 (fun x => Ring.inverse (A x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hh := contDiffAt_ringInverse ℝ (hunit x).unit (n := 2)
    rw [(hunit x).unit_spec] at hh
    exact hh.comp x hA.contDiffAt
  exact hi.clm_apply hb

theorem inverseFamily_equation {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (hunit : ∀ x, IsUnit (A x)) (x : D) :
    A x (inverseFamily A b x)=b x := by
  have hh := congrArg (fun L : E →L[ℝ] E => L (b x))
    (Ring.mul_inverse_cancel (A x) (hunit x))
  simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply,inverseFamily] using hh

theorem inverseFamily_first_equation {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (hA : ContDiff ℝ 2 A)
    (hb : ContDiff ℝ 2 b) (hunit : ∀ x, IsUnit (A x)) (x z : D) :
    fderiv ℝ A x z (inverseFamily A b x)+
      A x (fderiv ℝ (inverseFamily A b) x z)=fderiv ℝ b x z := by
  have hv := contDiff_inverseFamily A b hA hb hunit
  have hprod := (hasDerivAt_vector_on_affine_line A hA x z 0).clm_apply
    (hasDerivAt_vector_on_affine_line (inverseFamily A b) hv x z 0)
  have heq : (fun s : ℝ => A (x+s • z) (inverseFamily A b (x+s • z))) =
      (fun s => b (x+s • z)) := by
    funext s
    exact inverseFamily_equation A b hunit _
  rw [heq] at hprod
  have hh := hprod.unique (hasDerivAt_vector_on_affine_line b hb x z 0)
  simpa only [zero_smul,add_zero] using hh

theorem inverseFamily_second_equation {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (hA : ContDiff ℝ 2 A)
    (hb : ContDiff ℝ 2 b) (hunit : ∀ x, IsUnit (A x)) (x z : D) :
    fderiv ℝ (fderiv ℝ A) x z z (inverseFamily A b x)+
      (2:ℝ) • (fderiv ℝ A x z (fderiv ℝ (inverseFamily A b) x z))+
      A x (fderiv ℝ (fderiv ℝ (inverseFamily A b)) x z z)=
        fderiv ℝ (fderiv ℝ b) x z z := by
  have hv := contDiff_inverseFamily A b hA hb hunit
  have hprod := ((hasDerivAt_vector_directional_on_affine_line A hA x z 0).clm_apply
    (hasDerivAt_vector_on_affine_line (inverseFamily A b) hv x z 0)).add
    ((hasDerivAt_vector_on_affine_line A hA x z 0).clm_apply
      (hasDerivAt_vector_directional_on_affine_line (inverseFamily A b) hv x z 0))
  have heq : (fun s : ℝ => fderiv ℝ A (x+s • z) z (inverseFamily A b (x+s • z))+
      A (x+s • z) (fderiv ℝ (inverseFamily A b) (x+s • z) z)) =
      (fun s => fderiv ℝ b (x+s • z) z) := by
    funext s
    exact inverseFamily_first_equation A b hA hb hunit _ z
  change HasDerivAt (fun s => fderiv ℝ A (x+s • z) z (inverseFamily A b (x+s • z))+
    A (x+s • z) (fderiv ℝ (inverseFamily A b) (x+s • z) z)) _ 0 at hprod
  rw [heq] at hprod
  have hh := hprod.unique (hasDerivAt_vector_directional_on_affine_line b hb x z 0)
  simp only [zero_smul,add_zero] at hh
  rw [←hh]
  module

end QuantitativeFollowup
