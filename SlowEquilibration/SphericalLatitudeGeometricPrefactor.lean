-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeDeterminantScaling
public import SlowEquilibration.SphericalGeometricPrefactorBounds

@[expose] public section

/-! A dimension-independent multiplicative bound for the actual affine
latitude geometric prefactor, with the exact ambient normalization. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalMarkedWindows SlowEquilibration.SphereChartVolume
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeGeometricFactor (n : ℕ) (a : ℝ) : ℝ :=
  (manuscriptRoundVolume (n+1) univ).toReal *
    (2*Real.pi*(((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)*a))^(-((n+1 : ℕ) : ℝ)/2) *
      (((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))^(n+1)

theorem latitudeGeometricFactor_pos (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < latitudeGeometricFactor n a := by
  have hv := ENNReal.toReal_pos (manuscriptRoundVolume_mass_ne_zero (n+1))
    (manuscriptRoundVolume_mass_ne_top (n+1))
  unfold latitudeGeometricFactor
  positivity

theorem latitudeGeometricFactor_upper {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, latitudeGeometricFactor n a ≤
      C*Real.exp (((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)) := by
  obtain ⟨B, hB, harea⟩ := manuscriptRoundVolume_log_error_bound
  let K := B+|Real.log a|+|Real.log (2*Real.pi)|+1
  refine ⟨Real.exp K, Real.exp_pos _, ?_⟩
  intro n
  let r : ℝ := ((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hp : 0 < 2*Real.pi := by positivity
  have hbase : 0 < 2*Real.pi*(r*a) := mul_pos hp (mul_pos hr ha)
  have hv := ENNReal.toReal_pos (manuscriptRoundVolume_mass_ne_zero (n+1))
    (manuscriptRoundVolume_mass_ne_top (n+1))
  have hlogr : ((n+1 : ℕ) : ℝ)*Real.log r ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr)
      (show 0 ≤ ((n+1 : ℕ) : ℝ) by positivity)
    apply h.trans
    calc
      _ = ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by
        dsimp only [r]
        push_cast
        field_simp
        ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.le_succ (n+1))
  have hl : Real.log (latitudeGeometricFactor n a) =
      Real.log (manuscriptRoundVolume (n+1) univ).toReal -
        ((n+1 : ℕ) : ℝ)/2*(Real.log (2*Real.pi)+Real.log r+Real.log a)+
          ((n+1 : ℕ) : ℝ)*Real.log r := by
    unfold latitudeGeometricFactor
    rw [Real.log_mul (mul_pos hv (Real.rpow_pos_of_pos hbase _)).ne' (pow_pos hr _).ne',
      Real.log_mul hv.ne' (Real.rpow_pos_of_pos hbase _).ne', Real.log_rpow hbase,
      Real.log_pow, Real.log_mul hp.ne' (mul_pos hr ha).ne', Real.log_mul hr.ne' ha.ne']
    ring
  have hle : Real.log (latitudeGeometricFactor n a) ≤
      ((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)+K := by
    rw [hl]
    have hA := (abs_le.mp (harea n)).2
    dsimp only [K]
    push_cast at hA hlogr ⊢
    nlinarith [le_abs_self (Real.log a), le_abs_self (Real.log (2*Real.pi)), abs_nonneg (Real.log (2*Real.pi))]
  calc
    _ = Real.exp (Real.log (latitudeGeometricFactor n a)) := (Real.exp_log (latitudeGeometricFactor_pos n ha)).symm
    _ ≤ Real.exp (((n+3 : ℕ) : ℝ)*((1-Real.log a)/2)+K) := Real.exp_le_exp.mpr hle
    _ = _ := by rw [Real.exp_add]; ring

theorem latitudeGradientDensity_physical {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (q : ℝ)
    (ha : 0 ≤ (latitudeScale n q)^2*firstCovariance c 1) :
    latitudeGradientDensity n c q =
      ENNReal.ofReal ((2*Real.pi*((latitudeScale n q)^2*firstCovariance c 1))^(-(n : ℝ)/2)) := by
  have hp : 0 ≤ 2*Real.pi := by positivity
  have hs : Real.sqrt (((latitudeScale n q)^2*firstCovariance c 1)^n) =
      ((latitudeScale n q)^2*firstCovariance c 1)^((n : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul ha]
    congr 1
    ring
  unfold latitudeGradientDensity GaussianDensity.normalizer
  rw [hs]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  rw [show -(n : ℝ)/2 = -((n : ℝ)/2) by ring,
    Real.rpow_neg (mul_nonneg hp ha), Real.mul_rpow hp ha, mul_inv]
  rfl

theorem latitude_combined_geometric_factor {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {q : ℝ} (hq : |q| ≤ 1) (ha : 0 < (1-q^2)*firstCovariance c 1) :
    latitudeGradientDensity (n+1) c q * manuscriptRoundVolume (n+1) univ *
      ENNReal.ofReal ((((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))^(n+1)) =
        ENNReal.ofReal (latitudeGeometricFactor n ((1-q^2)*firstCovariance c 1)) := by
  have hs : (latitudeScale (n+1) q)^2*firstCovariance c 1 =
      (((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))*((1-q^2)*firstCovariance c 1) := by
    rw [latitudeScale_sq hq]
    ring
  have hpos : 0 < (latitudeScale (n+1) q)^2*firstCovariance c 1 := by rw [hs]; positivity
  rw [latitudeGradientDensity_physical (n+1) c q hpos.le, hs,
    ← ENNReal.ofReal_toReal (manuscriptRoundVolume_mass_ne_top (n+1)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by positivity) _) ENNReal.toReal_nonneg)]
  congr 1
  unfold latitudeGeometricFactor
  ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
