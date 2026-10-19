-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Multiplication by a strictly positive square root of a measure density
is an actual unitary between the two real L² spaces. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PositiveDensityL2
open MeasureTheory Filter
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (w : α → ℝ) (hw : Measurable w) (hwpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2)))

include hw hwpos hν

theorem reverse_absolutelyContinuous : μ ≪ ν := by
  rw [hν]
  apply withDensity_absolutelyContinuous' (hw.pow_const 2).ennreal_ofReal.aemeasurable
  exact .of_forall (fun x => (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hwpos x))).ne')

theorem forward_absolutelyContinuous : ν ≪ μ := by
  rw [hν]
  exact withDensity_absolutelyContinuous _ _

theorem integrable_iff (f : α → ℝ) :
    Integrable f ν ↔ Integrable (fun x => w x ^ 2 * f x) μ := by
  rw [hν, integrable_withDensity_iff_integrable_smul'
    (hw.pow_const 2).ennreal_ofReal (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem integral_eq (f : α → ℝ) :
    (∫ x, f x ∂ν) = ∫ x, w x ^ 2 * f x ∂μ := by
  rw [hν, integral_withDensity_eq_integral_toReal_smul
    (hw.pow_const 2).ennreal_ofReal (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem memLp_weighted (f : Lp ℝ 2 ν) : MemLp (fun x => w x * f x) 2 μ := by
  have hm := (Lp.aestronglyMeasurable f).mono_ac
    (reverse_absolutelyContinuous μ ν w hw hwpos hν)
  apply (memLp_two_iff_integrable_sq (hw.aestronglyMeasurable.mul hm)).mpr
  have hi := (integrable_iff μ ν w hw hwpos hν _).mp (Lp.memLp f).integrable_sq
  simpa only [Pi.mul_apply, mul_pow] using hi

theorem memLp_unweighted (f : Lp ℝ 2 μ) : MemLp (fun x => f x / w x) 2 ν := by
  have hm : AEStronglyMeasurable (fun x => f x / w x) ν := by
    have hi : Measurable (fun x => (w x)⁻¹) := measurable_inv.comp hw
    have ht := ((Lp.aestronglyMeasurable f).mul hi.aestronglyMeasurable).mono_ac
      (forward_absolutelyContinuous μ ν w hw hwpos hν)
    exact ht.congr (.of_forall (fun x => by simp only [Pi.mul_apply, div_eq_mul_inv]))

  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_iff μ ν w hw hwpos hν _).mpr
  convert (Lp.memLp f).integrable_sq using 1
  funext x
  simp only [div_pow]
  field_simp [(hwpos x).ne']

def forward (f : Lp ℝ 2 ν) : Lp ℝ 2 μ :=
  (memLp_weighted μ ν w hw hwpos hν f).toLp _

def backward (f : Lp ℝ 2 μ) : Lp ℝ 2 ν :=
  (memLp_unweighted μ ν w hw hwpos hν f).toLp _

theorem forward_coe (f : Lp ℝ 2 ν) :
    forward μ ν w hw hwpos hν f =ᵐ[μ] (fun x => w x * f x) :=
  MemLp.coeFn_toLp _

theorem backward_coe (f : Lp ℝ 2 μ) :
    backward μ ν w hw hwpos hν f =ᵐ[ν] (fun x => f x / w x) :=
  MemLp.coeFn_toLp _

theorem forward_backward (f : Lp ℝ 2 μ) :
    forward μ ν w hw hwpos hν (backward μ ν w hw hwpos hν f) = f := by
  apply Lp.ext
  filter_upwards [forward_coe μ ν w hw hwpos hν _,
    (backward_coe μ ν w hw hwpos hν f).filter_mono
      (reverse_absolutelyContinuous μ ν w hw hwpos hν).ae_le] with x hx hy
  rw [hx, hy]
  field_simp [(hwpos x).ne']

theorem backward_forward (f : Lp ℝ 2 ν) :
    backward μ ν w hw hwpos hν (forward μ ν w hw hwpos hν f) = f := by
  apply Lp.ext
  filter_upwards [backward_coe μ ν w hw hwpos hν _,
    (forward_coe μ ν w hw hwpos hν f).filter_mono
      (forward_absolutelyContinuous μ ν w hw hwpos hν).ae_le] with x hx hy
  rw [hx, hy]
  field_simp [(hwpos x).ne']

theorem forward_inner (f g : Lp ℝ 2 ν) :
    inner ℝ (forward μ ν w hw hwpos hν f) (forward μ ν w hw hwpos hν g) =
      inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def, integral_eq μ ν w hw hwpos hν]
  apply integral_congr_ae
  filter_upwards [forward_coe μ ν w hw hwpos hν f,
    forward_coe μ ν w hw hwpos hν g] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  ring

def unitary : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun := forward μ ν w hw hwpos hν
  invFun := backward μ ν w hw hwpos hν
  left_inv := backward_forward μ ν w hw hwpos hν
  right_inv := forward_backward μ ν w hw hwpos hν
  map_add' f g := by
    apply Lp.ext
    filter_upwards [forward_coe μ ν w hw hwpos hν (f+g),
      forward_coe μ ν w hw hwpos hν f, forward_coe μ ν w hw hwpos hν g,
      (Lp.coeFn_add f g).filter_mono
        (reverse_absolutelyContinuous μ ν w hw hwpos hν).ae_le,
      Lp.coeFn_add (forward μ ν w hw hwpos hν f) (forward μ ν w hw hwpos hν g)]
      with x hfg hf hg hadd hadd'
    simp only [hfg, hadd, hadd', Pi.add_apply, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [forward_coe μ ν w hw hwpos hν (c • f),
      forward_coe μ ν w hw hwpos hν f,
      (Lp.coeFn_smul c f).filter_mono
        (reverse_absolutelyContinuous μ ν w hw hwpos hν).ae_le,
      Lp.coeFn_smul c (forward μ ν w hw hwpos hν f)] with x hcf hf hsmul hsmul'
    simp only [RingHom.id_apply, hcf, hsmul, hsmul', Pi.smul_apply, smul_eq_mul, hf]
    ring
  norm_map' f := by
    change ‖forward μ ν w hw hwpos hν f‖ = ‖f‖
    have hi := forward_inner μ ν w hw hwpos hν f f
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (forward μ ν w hw hwpos hν f), norm_nonneg f]

theorem unitary_coe (f : Lp ℝ 2 ν) :
    unitary μ ν w hw hwpos hν f =ᵐ[μ] (fun x => w x * f x) :=
  forward_coe μ ν w hw hwpos hν f

theorem unitary_symm_coe (f : Lp ℝ 2 μ) :
    (unitary μ ν w hw hwpos hν).symm f =ᵐ[ν] (fun x => f x / w x) :=
  backward_coe μ ν w hw hwpos hν f

end SlowEquilibration.PositiveDensityL2
