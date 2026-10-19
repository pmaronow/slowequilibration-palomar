-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeScaledMixturePressure

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeScaledCSValue

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreeMomentLimit
open FiniteMixtureActiveDegreeScaling
open CSFiniteMixtureDirectionalDerivative
open CSCovarianceDirectionalDerivative CSGeneralCovarianceStability
open CSParisiMeasure
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Near amplitude one, the locally selected CS directional value is the
ordinary variational minimum of the genuine rescaled finite mixture. -/
theorem activeDegreeCSValue_eq_scaledMixture_variationalValue
    (μ : FiniteMixture) (β : ℝ) (p : Degree μ.maxDegree)
    (s : ℝ) (hs : 0 < s) (hcp : 0 < mixtureCoefficients μ p)
    (ht : (mixtureCoefficients μ p)*(s^2-1) ∈ Ioo (-1 : ℝ) 1) :
    activeDegreeCSValue μ β p s =
      CSParisiMeasure.variationalValue
        (scaleActiveDegree μ p s hs hcp) β := by
  let t := (mixtureCoefficients μ p)*(s^2-1)
  let ν := scaleActiveDegree μ p s hs hcp
  let L := perturbationLipschitzConstant μ p.val.val
  have hxi : ν.xi = fun r => μ.xi r+t*r^p.val.val := by
    funext r
    exact scaleActiveDegree_xi μ p s hs hcp r
  have hL : LipschitzOnWith L (fun r => μ.xi r+t*r^p.val.val)
      (Icc (0 : ℝ) 1) :=
    monomial_perturbation_lipschitzOn μ p.val.val
      (abs_le.mpr ⟨by linarith [ht.1],ht.2.le⟩)
  let ζ := locallyPerturbedMinimizer β μ.xi p.val.val L
    (base_lipschitzOn μ p.val.val)
    (fun z hz => monomial_perturbation_lipschitzOn μ p.val.val
      (abs_le.mpr ⟨by linarith [hz.1],hz.2.le⟩)) t
  have hζ : ζ.IsMinimizer β ν.xi := by
    rw [hxi]
    dsimp only [ζ, locallyPerturbedMinimizer]
    rw [dite_eq_left ht]
    exact lipschitzMinimizer_isMinimizer β (fun r => μ.xi r+t*r^p.val.val) L hL
  have hcanon := eq_canonicalMinimizer_of_isMinimizer ν β ζ hζ
  change ζ.value β (fun r => μ.xi r+t*r^p.val.val) =
    (canonicalMinimizer ν β).value β ν.xi
  rw [← hxi, hcanon]

end SlowEquilibration.SphericalActiveDegreeScaledCSValue
