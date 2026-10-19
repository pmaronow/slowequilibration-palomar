-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.RadialGaussianBounds

/-! Exact one-dimensional Laplace normalization, concentration and first
moments from primitive pointwise quadratic bounds on an actual density. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RadialLaplaceBounds
open Set MeasureTheory Filter RadialGaussianBounds
open scoped Topology ENNReal
set_option maxHeartbeats 300000

def lowerConstant (c b : ℝ) : ℝ := 2*c*Real.exp (-b)
def upperConstant (C a : ℝ) : ℝ := C*Real.sqrt (Real.pi/a)

theorem lowerConstant_pos {c b : ℝ} (hc : 0<c) : 0<lowerConstant c b := by
  unfold lowerConstant
  positivity

theorem gaussian_dimensional_scale {a N : ℝ} (ha : 0<a) (_hN : 0<N) :
    Real.sqrt (Real.pi/(a*N))=Real.sqrt (Real.pi/a)/Real.sqrt N := by
  rw [show Real.pi/(a*N)=(Real.pi/a)/N by ring,
    Real.sqrt_div (div_nonneg Real.pi_pos.le ha.le)]

/-- Integrating the pointwise upper bound retains the true N^{-1/2}. -/
theorem laplace_integral_upper {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) {C a N m θ : ℝ} (hC : 0≤C) (ha : 0<a) (hN : 0<N)
    (henv : ∀ k∈U,f k≤C*Real.exp (N*θ)*gaussian (a*N) m k) :
    (∫ k in U,f k)≤upperConstant C a*Real.exp (N*θ)/Real.sqrt N := by
  have hh := density_integral_upper hU hf (mul_nonneg hC (Real.exp_pos _).le)
    (mul_pos ha hN) henv
  rw [gaussian_dimensional_scale ha hN] at hh
  exact hh.trans_eq (by unfold upperConstant;ring)

/-- The local lower Gaussian estimate is integrated over a real interval
of radius N^{-1/2}; its length supplies the sharp normalization. -/
theorem laplace_integral_lower {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) (hf0 : ∀ k∈U,0≤f k)
    {c b N m θ : ℝ} (hc : 0≤c) (hb : 0≤b) (hN : 0<N)
    (hInside : Icc (m-1/Real.sqrt N) (m+1/Real.sqrt N)⊆U)
    (hl : ∀ k∈Icc (m-1/Real.sqrt N) (m+1/Real.sqrt N),
      c*Real.exp (N*θ)*gaussian (b*N) m k≤f k) :
    lowerConstant c b*Real.exp (N*θ)/Real.sqrt N≤∫ k in U,f k := by
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hN
  have hwidth : N*(1/Real.sqrt N)^2=1 := by
    field_simp [hs.ne']
    rw [Real.sq_sqrt hN.le]
  have hh := density_integral_lower hU hf hf0 (by positivity : 0≤1/Real.sqrt N)
    hInside (A := c*Real.exp (N*θ)*Real.exp (-b)) (by
      intro k hk
      apply le_trans _ (hl k hk)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (Real.exp_pos _).le)
      unfold gaussian
      apply Real.exp_le_exp.mpr
      have hd : |k-m|≤1/Real.sqrt N := abs_le.mpr (by constructor <;> linarith [hk.1,hk.2])
      have hsq : (k-m)^2≤(1/Real.sqrt N)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (k-m)) hd 2
      have hh := mul_le_mul_of_nonneg_left hsq hN.le
      rw [hwidth] at hh
      nlinarith)
  exact (by unfold lowerConstant;ring :
    lowerConstant c b*Real.exp (N*θ)/Real.sqrt N=
      2*(1/Real.sqrt N)*(c*Real.exp (N*θ)*Real.exp (-b))).trans_le hh

/-- The tail estimate is an actual restricted density integral. -/
theorem density_tail_upper {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) {A a m t : ℝ} (hA : 0≤A) (ha : 0<a) (ht : 0≤t)
    (henv : ∀ k∈U,f k≤A*gaussian a m k) :
    (∫ k in U∩{k : ℝ | t≤|k-m|},f k)≤
      A*Real.sqrt (Real.pi/(a/2))*Real.exp (-(a/2)*t^2) := by
  have hT : MeasurableSet {k : ℝ | t≤|k-m|} := measurableSet_le measurable_const (by fun_prop)
  have hh := density_integral_upper (hU.inter hT) (hf.mono_set inter_subset_left)
    (A := A*Real.exp (-(a/2)*t^2)) (by positivity) (half_pos ha) (m := m) (by
      intro k hk
      apply (henv k hk.1).trans
      have hp : gaussian a m k≤Real.exp (-(a/2)*t^2)*gaussian (a/2) m k := by
        unfold gaussian
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hsq : t^2≤(k-m)^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ ht hk.2 2
        nlinarith
      exact (mul_le_mul_of_nonneg_left hp hA).trans_eq (by ring))
  exact hh.trans_eq (by ring)

/-- The same pointwise Gaussian estimate controls the actual first moment. -/
theorem density_first_moment_upper {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) (hf0 : ∀ k∈U,0≤f k)
    {A a m : ℝ} (hA : 0≤A) (ha : 0<a)
    (henv : ∀ k∈U,f k≤A*gaussian a m k) :
    (∫ k in U,|k-m| * f k)≤A*(Real.sqrt (Real.pi/(a/2))/Real.sqrt a) := by
  have hg := (gaussian_moment_integrable ha m).const_mul A
  have hi : IntegrableOn (fun k => |k-m| * f k) U := by
    apply (hg.restrict (s := U)).mono'
    · exact ((by fun_prop : Continuous (fun k : ℝ => |k-m|)).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hU] with k hk
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hf0 k hk))]
      exact (mul_le_mul_of_nonneg_left (henv k hk) (abs_nonneg _)).trans_eq (by ring)
  calc
    _≤∫ k in U,A*(|k-m| * gaussian a m k) := setIntegral_mono_on hi
      (hg.restrict (s := U)) hU (fun k hk => (mul_le_mul_of_nonneg_left (henv k hk)
        (abs_nonneg _)).trans_eq (by ring))
    _≤∫ k : ℝ,A*(|k-m| * gaussian a m k) := setIntegral_le_integral hg
      (ae_of_all _ (fun _ => by unfold gaussian;positivity))
    _≤_ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (gaussian_first_moment_le ha m) hA
end SlowEquilibration.RadialLaplaceBounds
