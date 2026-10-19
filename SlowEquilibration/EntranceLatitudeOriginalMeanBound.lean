-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeOriginalMeanPolynomial
public import SlowEquilibration.SphericalLatitudeCorrectionEnvelopeTail

/-! Genuine original mixed latitude tangent mean bound. The minimum
supported degree is read from the actual mixture; higher corrections
retain the literal original Gaussian-bank envelope. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalLatitudeTensorMoments
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Model-only leading constant, fixed before choosing dimension. -/
def originalLatitudeLeadingConstant (μ : FiniteMixture) : ℝ :=
  ∑ p : Degree μ.maxDegree,Real.sqrt (mixtureCoefficients μ p)*(p.val.val : ℝ)*blockThreshold p

/-- Literal original higher-correction envelope of the actual mixture. -/
def originalLatitudeCorrectionEnvelope (n : ℕ) (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  ∑ p : Degree μ.maxDegree,Real.sqrt (mixtureCoefficients μ p)*latitudeCorrectionEnvelope n p.val.val (J p)

/-- Each actual supported degree preserves the true minimum-degree
vanishing order in the normalized leading radial derivative. -/
theorem original_latitude_leading_degree_abs_le {n : ℕ} (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (p : Degree μ.maxDegree)
    {r : ℝ} (hr : |r|≤1) :
    Real.sqrt (mixtureCoefficients μ p)*
      |(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u)|≤
      (Real.sqrt (mixtureCoefficients μ p)*(p.val.val : ℝ)*blockThreshold p)*
        Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1) := by
  by_cases hp : p.val.val∈μ.coeff.support
  · have hmin := (μ.degree_bounds hp).1
    have hN : (0 : ℝ)<((n+1 : ℕ) : ℝ) := by positivity
    have hs : 0<Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hN
    have hgeo : |(1-r^2)*r^(p.val.val-1)|≤|r|^(μ.minDegree-1) := by
      rw [abs_mul,abs_of_nonneg (show 0≤1-r^2 by nlinarith [abs_le.mp hr]),abs_pow]
      apply (mul_le_mul_of_nonneg_right (show 1-r^2≤1 by nlinarith) (pow_nonneg (abs_nonneg r) _)).trans
      simpa only [one_mul] using pow_le_pow_of_le_one (abs_nonneg r) hr (show μ.minDegree-1≤p.val.val-1 by omega)
    have hv := (SphericalAging.LandscapeDerivatives.Hamiltonian_sphere_bound
      (show 0<n+1 by omega) (show 1≤p.val.val by omega) (J p) u hu).trans (hJ p)
    have hb : |blockField p J u|/Real.sqrt ((n+1 : ℕ) : ℝ)≤blockThreshold p*Real.sqrt ((n+1 : ℕ) : ℝ) := by
      apply (div_le_iff₀ hs).mpr
      apply ((div_le_iff₀ hN).mp hv).trans_eq
      rw [mul_assoc,Real.mul_self_sqrt hN.le]
    have he : |(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
        ((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u)|=
        (p.val.val : ℝ)*|(1-r^2)*r^(p.val.val-1)| *
          (|blockField p J u|/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
      rw [show (1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
        ((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u)=
        (p.val.val : ℝ)*((1-r^2)*r^(p.val.val-1))*(blockField p J u/Real.sqrt ((n+1 : ℕ) : ℝ)) by ring]
      rw [abs_mul,abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos hs]
    rw [he]
    apply (mul_le_mul_of_nonneg_left
      (mul_le_mul (mul_le_mul_of_nonneg_left hgeo (Nat.cast_nonneg _)) hb (by positivity) (by positivity))
      (Real.sqrt_nonneg _)).trans_eq
    ring
  · have hc : mixtureCoefficients μ p=0 := by
      simpa only [mixtureCoefficients,Finsupp.mem_support_iff,not_not] using hp
    simp only [hc,Real.sqrt_zero,zero_mul,le_refl]

/-- Actual original-field latitude tangent mean has its genuine source
scale sqrt(N)|r|^(d-1) plus a literal higher original-bank correction. -/
theorem actual_original_latitudeObservableMean_abs_le {n : ℕ} (hn : 1≤n) (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (mixtureCoefficients μ) J u (latitudeFrameAt u) r|≤
      originalLatitudeLeadingConstant μ*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        originalLatitudeCorrectionEnvelope n μ J := by
  rw [actual_latitudeObservableMean_eq_originalPolynomial_derivative hn _ J u hu hr,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _≤∑ p : Degree μ.maxDegree,
        ((Real.sqrt (mixtureCoefficients μ p)*(p.val.val : ℝ)*blockThreshold p)*
          Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        Real.sqrt (mixtureCoefficients μ p)*latitudeCorrectionEnvelope n p.val.val (J p)) := by
      apply Finset.sum_le_sum
      intro p hp
      have he : (1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*(Real.sqrt (mixtureCoefficients μ p)*
          ((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u+
            deriv (pairedLatitudeCorrection n p.val.val (J p) u) r))=
          Real.sqrt (mixtureCoefficients μ p)*
            ((1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*((p.val.val : ℝ)*r^(p.val.val-1)*blockField p J u))+
          Real.sqrt (mixtureCoefficients μ p)*
            ((1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*deriv (pairedLatitudeCorrection n p.val.val (J p) u) r) := by ring
      rw [he]
      apply (abs_add_le _ _).trans
      have ha (t : ℝ) : |Real.sqrt (mixtureCoefficients μ p)*t|=Real.sqrt (mixtureCoefficients μ p)*|t| := by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [ha,ha]
      exact add_le_add (original_latitude_leading_degree_abs_le μ J hJ u hu p (abs_lt.mpr hr).le)
        (mul_le_mul_of_nonneg_left
          (normalized_weighted_pairedLatitudeCorrection_derivative_abs_le hn (J p) u hu (abs_lt.mpr hr).le)
          (Real.sqrt_nonneg _))
    _=_ := by
      unfold originalLatitudeLeadingConstant originalLatitudeCorrectionEnvelope
      rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
