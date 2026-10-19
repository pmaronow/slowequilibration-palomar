-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPLatitudeEntropyCurvature

@[expose] public section

/-! Smoothness and deterministic curvature of the original Hamiltonian
along source-radius transverse latitude slices. The second-derivative
regularity bound remains a physical event supplied by manuscript 12.3. -/

namespace SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
noncomputable section
open Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalTAPLatitudeEntropyCurvature
open SlowEquilibration.SphericalTAPSymmetricLatitudeIntegral
set_option autoImplicit false

def physicalLatitudeSlice (n : ℕ) (μ : FiniteMixture)
    (u ω : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) (a : ℝ) : ℝ :=
  field (mixtureCoefficients μ) J (a • u+Real.sqrt (1-a^2) • ω)

theorem physicalLatitudeSlice_contDiffOn (n : ℕ) (μ : FiniteMixture)
    (u ω : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) :
    ContDiffOn ℝ 2 (physicalLatitudeSlice n μ u ω J) (Ioo (-1:ℝ) 1) := by
  have hbase : ContDiffOn ℝ 2 (fun a : ℝ => 1-a^2) (Ioo (-1:ℝ) 1) := by
    fun_prop
  have hsqrt : ContDiffOn ℝ 2 (fun a : ℝ => Real.sqrt (1-a^2))
      (Ioo (-1:ℝ) 1) := by
    apply hbase.sqrt
    intro a ha
    have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
    exact hp.ne'
  have hpoint : ContDiffOn ℝ 2
      (fun a : ℝ => a • u+Real.sqrt (1-a^2) • ω) (Ioo (-1:ℝ) 1) := by
    fun_prop
  unfold physicalLatitudeSlice
  exact ((field_contDiff (mixtureCoefficients μ) J).of_le (by norm_num)).contDiffOn.comp
    hpoint (fun _ _ => Set.mem_univ _)

/-- The exponent appearing in the literal spherical coarea density,
with ambient dimension `N = n+1` and entropy coefficient `(N-3)/2`. -/
def physicalLatitudeExponent (n : ℕ) (μ : FiniteMixture)
    (u ω : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (β : ℝ) (a : ℝ) : ℝ :=
  latitudeExponent (physicalLatitudeSlice n μ u ω J) β ((n-2:ℕ):ℝ) a

theorem physicalLatitudeExponent_contDiffOn (n : ℕ) (μ : FiniteMixture)
    (u ω : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) (β : ℝ) :
    ContDiffOn ℝ 2 (physicalLatitudeExponent n μ u ω J β)
      (Ioo (-1:ℝ) 1) := by
  unfold physicalLatitudeExponent
  exact latitudeExponent_contDiffOn _ _ _ (physicalLatitudeSlice_contDiffOn n μ u ω J)

/-- On an interior latitude interval the physical coarea exponent has the
uniform curvature required for symmetric averaging. The only stochastic
input is the displayed Hamiltonian second-derivative event. -/
theorem physicalLatitudeExponent_second_deriv_lower
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u ω : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    {r a β C₀ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : |a| ≤ r)
    (hβ : 0 ≤ β)
    (hfield : |iteratedDeriv 2 (physicalLatitudeSlice n μ u ω J) a| ≤
      C₀*((n+1:ℕ):ℝ)) :
    -((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2) ≤
      iteratedDeriv 2 (physicalLatitudeExponent n μ u ω J β) a := by
  have hmN : ((n-2:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ) := by
    exact_mod_cast (show n-2 ≤ n+1 by omega)
  unfold physicalLatitudeExponent
  exact latitudeExponent_second_deriv_lower
    (physicalLatitudeSlice_contDiffOn n μ u ω J)
    hr0 hr1 ha hβ (Nat.cast_nonneg _) hmN hfield

/-- Deterministic source Lemma 12.19 on a fixed transverse point. It uses
the true spherical entropy and the original polynomial field; a bound on
the field's second latitude derivative is precisely the regularity event. -/
theorem physicalLatitudeExponent_symmetric_integral_lower
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u ω : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    {r center width β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hwidth : 0 < width)
    (hβ : 0 ≤ β)
    (hinside : ∀ a ∈ Icc (center-width) (center+width), |a| ≤ r)
    (hfield : ∀ a ∈ Icc (center-width) (center+width),
      |iteratedDeriv 2 (physicalLatitudeSlice n μ u ω J) a| ≤
        C₀*((n+1:ℕ):ℝ)) :
    2*width*Real.exp (physicalLatitudeExponent n μ u ω J β center-
      ((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2)*width^2/2) ≤
      ∫ a in (center-width)..(center+width),
        Real.exp (physicalLatitudeExponent n μ u ω J β a) := by
  have hinterval : Icc (center-width) (center+width) ⊆ Ioo (-1:ℝ) 1 := by
    intro a ha
    have habs := hinside a ha
    rw [abs_le] at habs
    constructor <;> linarith [habs.1,habs.2,hr1]
  have hcurv : 0 ≤ ((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2) := by
    have hcenter : center ∈ Icc (center-width) (center+width) := by
      constructor <;> linarith [hwidth]
    have hf := hfield center hcenter
    have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hC : 0 ≤ C₀ := by
      nlinarith [abs_nonneg (iteratedDeriv 2 (physicalLatitudeSlice n μ u ω J) center)]
    have hden : 0 < (1-r^2)^2 := by
      apply sq_pos_of_pos
      nlinarith [hr0,hr1]
    positivity
  exact exponential_symmetric_integral_lower_of_local_second_derivative
    (physicalLatitudeExponent n μ u ω J β) (-1) 1 center width
    (((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2))
    (physicalLatitudeExponent_contDiffOn n μ u ω J β)
    hwidth hcurv hinterval
    (fun a ha => by
      simpa only [neg_mul] using
        physicalLatitudeExponent_second_deriv_lower n hn μ u ω J
          hr0 hr1 (hinside a ha) hβ (hfield a ha))

end
end SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
