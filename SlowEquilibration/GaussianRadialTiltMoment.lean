-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.RadialGaussianShiftedMoment
public import SlowEquilibration.GaussianRadialTiltLogBounds
public import SlowEquilibration.GaussianRadialTiltAnalysis

/-! Actual normalized radial first moments after Gaussian energy
reweighting. These estimates require no determinant amplitude limit. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory RadialGaussianBounds RadialLaplaceBounds
set_option maxHeartbeats 300000

def radialMoment (w : ℝ → ℝ) (U : Set ℝ) (N A B c₀ m σ : ℝ) : ℝ :=
  ∫ k in U,|k-m| * tiltedDensity w N A B c₀ m σ k

def gaussianMomentConstant (a : ℝ) : ℝ := Real.sqrt (Real.pi/(a/2))/Real.sqrt a
def gaussianShiftMomentConstant (a B : ℝ) : ℝ := |B| * Real.sqrt (Real.pi/a)/(2*a)
def normalizedMomentConstant (c C a b A B : ℝ) : ℝ :=
  (C*Real.exp (correctionBound a A B))*(gaussianMomentConstant a+gaussianShiftMomentConstant a B)/
    (lowerConstant c b*Real.exp (-correctionBound b A B))

theorem gaussian_dimensional_moment_scale {a N : ℝ} (ha : 0 < a) (hN : 0 < N) :
    Real.sqrt (Real.pi/((a*N)/2))/Real.sqrt (a*N)=gaussianMomentConstant a/N := by
  have he : (a*N)/2=(a/2)*N := by ring
  rw [he,gaussian_dimensional_scale (half_pos ha) hN,Real.sqrt_mul ha.le]
  unfold gaussianMomentConstant
  calc
    _=(Real.sqrt (Real.pi/(a/2))/Real.sqrt a)/(Real.sqrt N)^2 := by
      field_simp
    _=_ := by rw [Real.sq_sqrt hN.le]

theorem radialMoment_gaussian_upper {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    {C a N A B c₀ m σ : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hN : 0 < N)
    (hi : IntegrableOn (tiltedDensity w N A B c₀ m σ) U) (h0 : ∀ k∈U,0 ≤ w k)
    (hu : ∀ k∈U,w k ≤ C*gaussian (a*N) m k) :
    radialMoment w U N A B c₀ m σ ≤ C*Real.exp (heightCorrection a N A B c₀ σ)*
      (gaussianMomentConstant a/N+gaussianShiftMomentConstant a B*|σ|/(N*Real.sqrt N)) := by
  have hh := density_shifted_first_moment_upper hU hi
    (fun k hk => mul_nonneg (h0 k hk) (Real.exp_pos _).le)
    (A := C*Real.exp (heightCorrection a N A B c₀ σ)) (by positivity) (mul_pos ha hN)
    (tiltedDensity_gaussian_upper ha hN hu) (m := m)
  rw [gaussian_dimensional_moment_scale ha hN,gaussian_dimensional_scale ha hN] at hh
  have hshift : shiftedCenter a N B m σ-m=-(B*σ/(2*a*N)) := by unfold shiftedCenter;ring
  rw [hshift,abs_neg,abs_div,abs_mul,abs_of_pos (by positivity : 0 < 2*a*N)] at hh
  exact hh.trans_eq (by unfold gaussianShiftMomentConstant;ring)

theorem normalizedMomentConstant_nonneg {c C a b A B : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 0 < a) (_hb : 0 < b) : 0 ≤ normalizedMomentConstant c C a b A B := by
  unfold normalizedMomentConstant gaussianMomentConstant gaussianShiftMomentConstant lowerConstant
  positivity

theorem radialMoment_le_density_scale {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    {c C a b N A B c₀ m σ : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hi : IntegrableOn (tiltedDensity w N A B c₀ m σ) U) (h0 : ∀ k∈U,0 ≤ w k)
    (hl : ∀ k∈U,c*gaussian (b*N) m k ≤ w k)
    (hu : ∀ k∈U,w k ≤ C*gaussian (a*N) m k)
    (hInside : Icc (shiftedCenter b N B m σ-1/Real.sqrt N)
      (shiftedCenter b N B m σ+1/Real.sqrt N)⊆U) (hσ : σ^2/N ≤ 1) :
    radialMoment w U N A B c₀ m σ ≤ normalizedMomentConstant c C a b A B*
      (1/Real.sqrt N+|σ|/N)*energyDensity w U N A B c₀ m σ := by
  let d := lowerConstant c b*Real.exp (-correctionBound b A B)
  let P := C*Real.exp (correctionBound a A B)
  let km := gaussianMomentConstant a
  let ks := gaussianShiftMomentConstant a B
  have hd : 0 < d := mul_pos (lowerConstant_pos hc) (Real.exp_pos _)
  have hP : 0 ≤ P := mul_nonneg hC (Real.exp_pos _).le
  have hkm : 0 ≤ km := by dsimp [km,gaussianMomentConstant];positivity
  have hks : 0 ≤ ks := by dsimp [ks,gaussianShiftMomentConstant];positivity
  have hK : 0 ≤ normalizedMomentConstant c C a b A B := normalizedMomentConstant_nonneg hc hC ha hb
  have hq : 0 ≤ 1/Real.sqrt N+|σ|/N := by positivity
  have hlower := (tilted_integral_log_bounds hU hc.le hC ha hb hN hi h0 hl hu hInside hσ).1
  have hraw := radialMoment_gaussian_upper hU hC ha hN hi h0 hu
  have hheight : Real.exp (heightCorrection a N A B c₀ σ) ≤
      Real.exp (correctionBound a A B)*Real.exp (-c₀*σ) := by
    have hh := Real.exp_le_exp.mpr (heightCorrection_bounds ha hN A B c₀ σ hσ).2
    exact hh.trans_eq (by rw [Real.exp_add];ring)
  have hscale : 0 ≤ km/N+ks*|σ|/(N*Real.sqrt N) := by positivity
  have hcoef : C*Real.exp (heightCorrection a N A B c₀ σ) ≤ P*Real.exp (-c₀*σ) :=
    (mul_le_mul_of_nonneg_left hheight hC).trans_eq (by dsimp [P];ring)
  have hupp : radialMoment w U N A B c₀ m σ ≤ P*Real.exp (-c₀*σ)*
      (km/N+ks*|σ|/(N*Real.sqrt N)) := hraw.trans
    (mul_le_mul_of_nonneg_right hcoef hscale)
  have hsum : km/N+ks*|σ|/(N*Real.sqrt N) ≤
      (km+ks)/N+(km+ks)*|σ|/(N*Real.sqrt N) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_right (by linarith) hN.le
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : ks ≤ km+ks) (abs_nonneg σ)) (by positivity)
  have hmain := hupp.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hP (Real.exp_pos _).le))
  have he : P*Real.exp (-c₀*σ)*((km+ks)/N+(km+ks)*|σ|/(N*Real.sqrt N))=
      normalizedMomentConstant c C a b A B*(1/Real.sqrt N+|σ|/N)*
        (d*Real.exp (-c₀*σ)/Real.sqrt N) := by
    change _=(P*(km+ks)/d)*(1/Real.sqrt N+|σ|/N)*(d*Real.exp (-c₀*σ)/Real.sqrt N)
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    field_simp [hd.ne',hN.ne',hs.ne']
    ring_nf
    rw [Real.sq_sqrt hN.le]
  rw [he] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_left hlower (mul_nonneg hK hq))

end SlowEquilibration.GaussianRadialEnergyTilt
