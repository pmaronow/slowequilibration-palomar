-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianQuadraticHighMoments
public import SlowEquilibration.GaussianQuadraticVariance

/-! Every fixed real moment of the actual centered symmetric quadratic
form under the standard Gaussian law. Spectral choices are made for a fixed
operator, so no measurable eigenbasis is required. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A genuine dimension-sharp ordinary moment bound for the centered
quadratic form; the bound is uniform over all symmetric operators with the
stated deterministic operator norm bound. -/
theorem standard_gaussian_quadratic_high_moment (S : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) {L : ℝ} (hL : 0 < L) (hSL : ‖S‖ ≤ L)
    (hm : 0 < Module.finrank ℝ E) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x=>|centeredQuadratic S hS x|^q) (stdGaussian E) ∧
      (∫ x,|centeredQuadratic S hS x|^q ∂stdGaussian E) ≤
        quadraticMomentConstant q*(quadraticFluctuationScale (Module.finrank ℝ E) L)^q := by
  let B:=hS.eigenvectorBasis (show Module.finrank ℝ E=Module.finrank ℝ E from rfl)
  let R : (Fin (Module.finrank ℝ E) → ℝ) → E:=fun z=>B.repr.symm (WithLp.toLp 2 z)
  have hRM : Measurable R:=B.repr.symm.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
  have hLaw : (γpi (Fin (Module.finrank ℝ E))).map R=stdGaussian E := by
    rw [← stdGaussian_map B.repr.symm,← map_pi_eq_stdGaussian,
      Measure.map_map B.repr.symm.continuous.measurable (WithLp.measurable_toLp 2 _)]
    rfl
  have hw (i : Fin (Module.finrank ℝ E)) : |hS.eigenvalues rfl i| ≤ L := by
    have hnorm:=S.le_opNorm (B i)
    have hSv : S (B i)=hS.eigenvalues rfl i • B i := hS.apply_eigenvectorBasis rfl i
    rw [hSv,norm_smul,Real.norm_eq_abs,B.norm_eq_one i,mul_one,mul_one] at hnorm
    exact hnorm.trans hSL
  have hMoment:=diagonalQuadratic_high_moment (hS.eigenvalues rfl) hL
    (by simpa only [Fintype.card_fin] using hm) hw q hq
  have hMeas : Measurable (fun x=>|centeredQuadratic S hS x|^q) :=
    (centeredQuadratic_measurable S hS).abs.pow_const q
  have hCoords (z) : |centeredQuadratic S hS (R z)|^q=
      |diagonalQuadratic (hS.eigenvalues rfl) z|^q := by
    rw [show centeredQuadratic S hS (R z)=diagonalQuadratic (hS.eigenvalues rfl) z from
      centeredQuadratic_eigen_coordinates S hS z]
  refine ⟨?_,?_⟩
  · rw [←hLaw]
    exact (integrable_map_measure hMeas.aestronglyMeasurable hRM.aemeasurable).mpr
      (by simpa only [Function.comp_def,hCoords] using hMoment.1)
  · rw [←hLaw,integral_map hRM.aemeasurable hMeas.aestronglyMeasurable]
    simp only [hCoords]
    simpa only [Fintype.card_fin] using hMoment.2

end
end SlowEquilibration.GaussianQuadraticVariance
