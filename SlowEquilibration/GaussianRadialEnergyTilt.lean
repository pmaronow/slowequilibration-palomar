-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.RadialLaplaceBounds

/-! Exact completion of the radial Gaussian square under the physical
energy tilt. Normalization bounds are obtained by integrating the actual
tilted density; no tilted probability or count limit is assumed. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory RadialGaussianBounds RadialLaplaceBounds
set_option maxHeartbeats 300000

def tiltedDensity (w : ℝ → ℝ) (N A B c₀ m σ k : ℝ) : ℝ :=
  w k*Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))

def shiftedCenter (a N B m σ : ℝ) : ℝ := m-B*σ/(2*a*N)

def heightCorrection (a N A B c₀ σ : ℝ) : ℝ :=
  -c₀*σ-A*σ^2/(2*N)+B^2*σ^2/(4*a*N)

/-- The square is completed exactly, for every scalar energy increment. -/
theorem gaussian_energy_completion {a N : ℝ} (ha : 0<a) (hN : 0<N)
    (A B c₀ m σ k : ℝ) :
    gaussian (a*N) m k*Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))=
      Real.exp (heightCorrection a N A B c₀ σ)*gaussian (a*N) (shiftedCenter a N B m σ) k := by
  unfold gaussian heightCorrection shiftedCenter
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  field_simp [ha.ne',hN.ne']
  ring

theorem tiltedDensity_gaussian_upper {w : ℝ → ℝ} {U : Set ℝ}
    {C a N A B c₀ m σ : ℝ} (ha : 0<a) (hN : 0<N)
    (hw : ∀ k∈U,w k≤C*gaussian (a*N) m k) :
    ∀ k∈U,tiltedDensity w N A B c₀ m σ k≤
      C*Real.exp (heightCorrection a N A B c₀ σ)*gaussian (a*N) (shiftedCenter a N B m σ) k := by
  intro k hk
  have hh := mul_le_mul_of_nonneg_right (hw k hk)
    (Real.exp_pos (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))).le
  unfold tiltedDensity
  apply hh.trans_eq
  rw [mul_assoc,gaussian_energy_completion ha hN]
  ring

theorem tiltedDensity_gaussian_lower {w : ℝ → ℝ} {U : Set ℝ}
    {c b N A B c₀ m σ : ℝ} (hb : 0<b) (hN : 0<N)
    (hw : ∀ k∈U,c*gaussian (b*N) m k≤w k) :
    ∀ k∈U,c*Real.exp (heightCorrection b N A B c₀ σ)*gaussian (b*N) (shiftedCenter b N B m σ) k≤
      tiltedDensity w N A B c₀ m σ k := by
  intro k hk
  have hh := mul_le_mul_of_nonneg_right (hw k hk)
    (Real.exp_pos (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))).le
  unfold tiltedDensity
  apply le_trans _ hh
  exact le_of_eq (by
    calc
      _=c*(Real.exp (heightCorrection b N A B c₀ σ)*
        gaussian (b*N) (shiftedCenter b N B m σ) k) := by ring
      _=c*(gaussian (b*N) m k*Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))) := by
        rw [gaussian_energy_completion hb hN]
      _=_ := by ring)

/-- The actual tilted integral upper bound contains only a quadratic
energy correction divided by N, in addition to the source energy slope. -/
theorem tilted_integral_upper {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    {C a N A B c₀ m σ : ℝ} (hC : 0≤C) (ha : 0<a) (hN : 0<N)
    (hi : IntegrableOn (tiltedDensity w N A B c₀ m σ) U)
    (hw : ∀ k∈U,w k≤C*gaussian (a*N) m k) :
    (∫ k in U,tiltedDensity w N A B c₀ m σ k)≤
      upperConstant C a*Real.exp (heightCorrection a N A B c₀ σ)/Real.sqrt N := by
  have hh := density_integral_upper hU hi
    (A := C*Real.exp (heightCorrection a N A B c₀ σ)) (by positivity) (mul_pos ha hN)
    (tiltedDensity_gaussian_upper ha hN hw)
  rw [gaussian_dimensional_scale ha hN] at hh
  exact hh.trans_eq (by unfold upperConstant;ring)

/-- The lower bound is integrated over a true interval about the actual
shifted Gaussian center; its inclusion is the sole geometric input. -/
theorem tilted_integral_lower {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    {c b N A B c₀ m σ : ℝ} (hc : 0≤c) (hb : 0<b) (hN : 0<N)
    (hi : IntegrableOn (tiltedDensity w N A B c₀ m σ) U)
    (h0 : ∀ k∈U,0≤w k)
    (hw : ∀ k∈U,c*gaussian (b*N) m k≤w k)
    (hInside : Icc (shiftedCenter b N B m σ-1/Real.sqrt N)
      (shiftedCenter b N B m σ+1/Real.sqrt N)⊆U) :
    lowerConstant c b*Real.exp (heightCorrection b N A B c₀ σ)/Real.sqrt N≤
      ∫ k in U,tiltedDensity w N A B c₀ m σ k := by
  have hh := laplace_integral_lower hU hi
    (fun k hk => mul_nonneg (h0 k hk) (Real.exp_pos _).le)
    (c := c*Real.exp (heightCorrection b N A B c₀ σ)) (by positivity)
    hb.le hN hInside (θ := 0) (by
      intro k hk
      simpa only [mul_zero,Real.exp_zero,mul_one] using
        tiltedDensity_gaussian_lower hb hN hw k (hInside hk))
  simpa only [mul_zero,Real.exp_zero,mul_one,one_mul,lowerConstant,mul_assoc,mul_comm,mul_left_comm] using hh
end SlowEquilibration.GaussianRadialEnergyTilt
