-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.StrongFieldLaplace

/-! Genuine Gaussian envelopes obtained from a negative scalar gap and a
quadratic coercivity bound, together with unrestricted determinant tails. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.QuadraticPlaneEnvelopes
open Set MeasureTheory Filter
open StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 400000

theorem gap_and_coercivity_envelope {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    {γ C a : ℝ} (hγ : 0 < γ) (hC : 0 < C) (ha : 0 < a)
    (hgap : ∀ z ∈ S,f z ≤ -γ) (hcoerc : ∀ z,f z ≤ C-a*(z.1^2+z.2^2)) :
    ∃ η κ : ℝ,0 < η ∧ 0 < κ ∧ ∀ z ∈ S,f z ≤ -η-κ*(z.1^2+z.2^2) := by
  let θ := γ/(2*(C+γ))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(C+γ))).mpr
    linarith
  have hθeq : θ*(C+γ)=γ/2 := by dsimp [θ]; field_simp
  refine ⟨γ/2,θ*a,by positivity,mul_pos hθ ha,?_⟩
  intro z hz
  have h1 := mul_le_mul_of_nonneg_left (hgap z hz) (by linarith : 0 ≤ 1-θ)
  have h2 := mul_le_mul_of_nonneg_left (hcoerc z) hθ.le
  nlinarith

def crudeCutoff (C κ : ℝ) : ℝ := Real.sqrt (8*(|C|+1+1/κ)/κ)+1

theorem crudeCutoff_pos (C : ℝ) {κ : ℝ} (hκ : 0 < κ) : 0 < crudeCutoff C κ := by
  unfold crudeCutoff
  positivity

theorem crude_quadratic_tail_loss (C : ℝ) {κ : ℝ} (hκ : 0 < κ) (e k : ℝ)
    (hk : crudeCutoff C κ ≤ |k|) :
    C+|k|-κ/2*(e^2+k^2) ≤ -1-κ/8*(e^2+k^2) := by
  have hroot : Real.sqrt (8*(|C|+1+1/κ)/κ) ≤ |k| := by
    dsimp [crudeCutoff] at hk
    linarith
  have hsq : 8*(|C|+1+1/κ)/κ ≤ k^2 := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg k)).mpr hroot
    rwa [Real.sq_sqrt (by positivity),sq_abs] at hh
  have hbase := (div_le_iff₀ hκ).mp hsq
  have hYoung : |k| ≤ κ/4*k^2+1/κ := by
    have hid : κ*(κ/4*k^2+1/κ-|k|)=(κ*|k|-2)^2/4 := by
      field_simp [hκ.ne']
      nlinarith [sq_abs k]
    have hh : 0 ≤ κ*(κ/4*k^2+1/κ-|k|) := by rw [hid]; positivity
    nlinarith
  have he : 0 ≤ κ*e^2 := by positivity
  nlinarith [le_abs_self C]

theorem combined_intensity_envelope
    (R : ℕ → (ℝ × ℝ) → ℝ≥0∞) (theta : ℝ × ℝ → ℝ) (S : Set (ℝ × ℝ))
    {B1 B2 C κ γ ρ : ℝ} (hB1 : 0 < B1) (_hB2 : 0 < B2) (hκ : 0 < κ)
    (hγ : 0 < γ) (hρ : 0 < ρ)
    (hSharp : ∀ {Z eps : ℝ},0 ≤ Z → 0 < eps →
      ∀ᶠ n : ℕ in atTop,∀ z : ℝ × ℝ,|z.2| ≤ Z →
        R n z ≤ ENNReal.ofReal (B1*(n+2 : ℕ)*Real.exp ((n+2 : ℕ)*(theta z+eps))))
    (hCrude : ∀ n : ℕ,∀ z : ℝ × ℝ,
      R n z ≤ ENNReal.ofReal (B2*(n+2 : ℕ)*Real.exp ((n+2 : ℕ)*
        (C+|z.2|-κ/2*(z.1^2+z.2^2)))))
    (hTheta : ∀ z ∈ S,theta z ≤ -γ-ρ*(z.1^2+z.2^2)) :
    ∃ B η a : ℝ,0 < B ∧ 0 < η ∧ 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ S,R n z ≤ ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp (-η*(n+2 : ℕ)))*
        ENNReal.ofReal (gaussianPlane a z) := by
  let Z := crudeCutoff C κ
  have hZ := crudeCutoff_pos C hκ
  refine ⟨max B1 B2,min (γ/2) 1,min ρ (κ/8),lt_max_of_lt_left hB1,
    lt_min (by positivity) (by norm_num),lt_min hρ (by positivity),?_⟩
  filter_upwards [hSharp hZ.le (show 0 < γ/2 by positivity)] with n hn
  intro z hz
  have hN : 1 ≤ ((n+2 : ℕ) : ℝ) := by norm_cast; omega
  rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ max B1 B2*(n+2 : ℕ)*
    Real.exp (-min (γ/2) 1*(n+2 : ℕ)))]
  by_cases hk : |z.2| ≤ Z
  · apply (hn z hk).trans
    apply ENNReal.ofReal_le_ofReal
    have hgap := hTheta z hz
    have hsq : 0 ≤ z.1^2+z.2^2 := by positivity
    have ht := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ ((n+2 : ℕ) : ℝ))
    have hkeep := mul_le_mul_of_nonneg_right hN (mul_nonneg hρ.le hsq)
    have hη := mul_le_mul_of_nonneg_right (min_le_left (γ/2) 1)
      (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)
    have ha := mul_le_mul_of_nonneg_right (min_le_left ρ (κ/8)) hsq
    have he : (n+2 : ℕ)*(theta z+γ/2) ≤
        -min (γ/2) 1*(n+2 : ℕ)-min ρ (κ/8)*(z.1^2+z.2^2) := by nlinarith
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left B1 B2)
      (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity))
      (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    apply hh.trans_eq
    rw [show -min (γ/2) 1*(n+2 : ℕ)-min ρ (κ/8)*(z.1^2+z.2^2)=
      -min (γ/2) 1*(n+2 : ℕ)+(-min ρ (κ/8)*(z.1^2+z.2^2)) by ring,Real.exp_add]
    unfold gaussianPlane
    ring
  · apply (hCrude n z).trans
    apply ENNReal.ofReal_le_ofReal
    have htail := crude_quadratic_tail_loss C hκ z.1 z.2 (le_of_not_ge hk)
    have hsq : 0 ≤ z.1^2+z.2^2 := by positivity
    have ht := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ ((n+2 : ℕ) : ℝ))
    have hkeep := mul_le_mul_of_nonneg_right hN (mul_nonneg (by positivity : 0 ≤ κ/8) hsq)
    have hη := mul_le_mul_of_nonneg_right (min_le_right (γ/2) 1)
      (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)
    have ha := mul_le_mul_of_nonneg_right (min_le_right ρ (κ/8)) hsq
    have he : (n+2 : ℕ)*(C+|z.2|-κ/2*(z.1^2+z.2^2)) ≤
        -min (γ/2) 1*(n+2 : ℕ)-min ρ (κ/8)*(z.1^2+z.2^2) := by nlinarith
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right B1 B2)
      (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity))
      (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    apply hh.trans_eq
    rw [show -min (γ/2) 1*(n+2 : ℕ)-min ρ (κ/8)*(z.1^2+z.2^2)=
      -min (γ/2) 1*(n+2 : ℕ)+(-min ρ (κ/8)*(z.1^2+z.2^2)) by ring,Real.exp_add]
    unfold gaussianPlane
    ring

/-- A genuine Gaussian pointwise envelope integrates against the literal
two-dimensional Lebesgue measure, retaining every dimensional prefactor. -/
theorem intensity_lintegral_envelope (R : ℝ × ℝ → ℝ≥0∞) (S : Set (ℝ × ℝ))
    {B N η a : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N) (ha : 0 < a)
    (hR : ∀ z ∈ S,R z ≤ ENNReal.ofReal (B*N*Real.exp (-η*N))*ENNReal.ofReal (gaussianPlane a z)) :
    (∫⁻ z in S,R z ∂planeVolume) ≤ ENNReal.ofReal (B*N*(Real.pi/a)*Real.exp (-η*N)) := by
  have hG : (∫⁻ z,ENNReal.ofReal (gaussianPlane a z) ∂planeVolume)=ENNReal.ofReal (Real.pi/a) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (gaussianPlane_integrable ha)
      (ae_of_all _ (fun z => (Real.exp_pos _).le)),integral_gaussianPlane ha]
  calc
    _ ≤ ∫⁻ z in S,ENNReal.ofReal (B*N*Real.exp (-η*N))*ENNReal.ofReal (gaussianPlane a z) ∂planeVolume := by
      apply setLIntegral_mono (by unfold gaussianPlane; fun_prop)
      exact hR
    _ ≤ ∫⁻ z,ENNReal.ofReal (B*N*Real.exp (-η*N))*ENNReal.ofReal (gaussianPlane a z) ∂planeVolume :=
      by simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := planeVolume)
          (f := fun z => ENNReal.ofReal (B*N*Real.exp (-η*N))*ENNReal.ofReal (gaussianPlane a z))
          (subset_univ S))
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hG,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end SlowEquilibration.QuadraticPlaneEnvelopes
