-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeGeometry

@[expose] public section

/-! # Exact physical first and second targets of source Gaussian IBP

At the concentrated source latitude the two nonzero selected polynomials
measure the first and second moments of physical overlap minus q². The
source Dirac derivatives give precisely the targets q−q² and (q−q²)².
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set SphericalModel
open scoped Topology
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def amplitudeProbeMomentCoefficient (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (q : ℝ) : ℝ :=
  mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1) : ℝ)*
    q^(2*(p₀.val.val-(k.val+1)))

theorem amplitudeProbeMomentCoefficient_pos (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (hp₀ : 0 < mixtureCoefficients μ p₀) (k : Fin 2) {q : ℝ} (hq : 0<q) :
    0 < amplitudeProbeMomentCoefficient μ p₀ k q := by
  have hk : k.val+1≤p₀.val.val := by have hh:=k.isLt;have hp:=p₀.property;omega
  have hchoose : 0 < (Nat.choose p₀.val.val (k.val+1) : ℝ) := by exact_mod_cast Nat.choose_pos hk
  unfold amplitudeProbeMomentCoefficient
  exact mul_pos (mul_pos hp₀ hchoose) (pow_pos hq _)

theorem amplitudePhysicalProbePolynomial_center_eq_moment (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (q R : ℝ) :
    amplitudePhysicalProbePolynomial μ p₀ k q q R=
      amplitudeProbeMomentCoefficient μ p₀ k q*(R-q^2)^(k.val+1) :=
  amplitudePhysicalProbePolynomial_center μ p₀ k q R

theorem amplitudeSelectedCoefficient_eq_momentCoefficient (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (q : ℝ) :
    amplitudeSelectedCoefficient μ p₀ k q=
      amplitudeProbeMomentCoefficient μ p₀ k q*(1-q^2)^(k.val+1) := rfl

theorem amplitudeDiracAtom_physical_target {q : ℝ} (hq : 0≤q) :
    (1-q^2)*amplitudeDiracAtom q=q-q^2 := by
  unfold amplitudeDiracAtom
  rw [abs_of_nonneg hq]
  have hd : 1+q≠0 := by positivity
  field_simp
  ring

/-- The literal source envelope derivative targets the ordinary physical
probe moments, with no normalized transverse coordinate or pole condition. -/
theorem amplitudeProbe_source_target_identity (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {q : ℝ} (hq : 0≤q) :
    β^2*amplitudeSelectedCoefficient μ p₀ k q-
      2*amplitudeDiracShiftCoefficient μ β p₀ k q=
        β^2*amplitudeProbeMomentCoefficient μ p₀ k q*(q-q^2)^(k.val+1) := by
  unfold amplitudeDiracShiftCoefficient
  rw [amplitudeSelectedCoefficient_eq_momentCoefficient]
  calc
    _=β^2*amplitudeProbeMomentCoefficient μ p₀ k q*
      ((1-q^2)*amplitudeDiracAtom q)^(k.val+1) := by rw [mul_pow];ring
    _=_ := by rw [amplitudeDiracAtom_physical_target hq]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
