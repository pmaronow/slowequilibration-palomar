-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalTAPPhysicalHessianSource
public import SlowEquilibration.SphericalWindowGeometry
public import SlowEquilibration.SphericalPureMarkedWindows
public import SlowEquilibration.SphericalMarkedMaximumEvents

/-! The printed proper-pure radial mark restriction is automatic on each
value window, pathwise for the original homogeneous Gaussian tensor field. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set SphericalModel SphericalGaussianJet SphericalTAPCertificate
open WholeFieldRegression SphericalKacRiceGluing
open scoped ENNReal Topology
set_option autoImplicit false

theorem pure_actualScore_radial_eq_value
    (N p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp a ha).maxDegree) (y : Vector N) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    actualScore c J y 1 = (p : ℝ)*actualValue c J y := by
  dsimp only
  rw [actualScore_pure p hp a ha Q J y]
  rfl

/-- For a pure field, a score window obtained by restricting the radial
mark to the Euler image of a value box counts exactly the value-window
critical points for every disorder sample. -/
theorem pure_actualScoreWindowCount_eq_valueWindowCount
    (N p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q E δ : ℝ)
    (I : Set ℝ) (hI : I ⊆ Icc (E-δ) (E+δ))
    (J : Disorder (N+1) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    actualScoreWindowCount N c
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ I ∧ b 1 ∈ Icc ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
      (fun _ _ => 1) J =
    actualValueWindowCount N c I (fun _ _ => 1) J := by
  classical
  dsimp only
  let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
  rw [actualScoreWindowCount_eq_indicator,actualValueWindowCount_eq_indicator]
  apply congrArg (fun psi => actualSphereCount N c psi J)
  funext J' y
  have hv : actualScore c J' y 0 = actualValue c J' y := by
    rw [actualScore_value_eq]
    rfl
  have hr := pure_actualScore_radial_eq_value (N+1) p hp a ha Q J' y
  have hp0 : (0 : ℝ) ≤ p := by exact_mod_cast (show 0 ≤ p by omega)
  have hmem : actualScore c J' y ∈
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ I ∧ b 1 ∈ Icc ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} ↔
      actualValue c J' y ∈ I := by
    constructor
    · intro hh
      exact hv ▸ hh.1
    · intro hh
      have hbox := hI hh
      constructor
      · simpa only [hv] using hh
      · rw [hr]
        exact
          (show (p : ℝ)*actualValue c J' y ∈
            Icc ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ)) from
            ⟨mul_le_mul_of_nonneg_left hbox.1 hp0,
              mul_le_mul_of_nonneg_left hbox.2 hp0⟩)
  split_ifs with hscore hvalue
  · rfl
  · exact False.elim (hvalue (hmem.mp hscore))
  · rename_i hvalue
    exact False.elim (hscore (hmem.mpr hvalue))
  · rfl

end SlowEquilibration.SphericalMarkedWindows
