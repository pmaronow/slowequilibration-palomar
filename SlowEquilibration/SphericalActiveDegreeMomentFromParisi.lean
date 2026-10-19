-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeScaledCSValue

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeMomentFromParisi

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure
open SphericalActiveDegreeMomentLimit
open SphericalActiveDegreeScaledMixturePressure
open SphericalActiveDegreeScaledCSValue
open FiniteMixtureActiveDegreeScaling
open SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The ordinary full Parisi pressure formula for all finite mixtures at
the fixed temperature determines the physical overlap-power moment for
every degree already present with a positive coefficient. -/
theorem physical_pairPower_tendsto_of_full_finiteMixture_parisi
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (hβ : 0 < β) (p : Degree μ.maxDegree)
    (hcp : 0 < mixtureCoefficients μ p)
    (hparisi : ∀ ν : FiniteMixture,
      Tendsto (fun n : ℕ => quenchedPressure (n+2) ν β)
        atTop (𝓝 (CSParisiMeasure.variationalValue ν β))) :
    Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1)^p.val.val ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1-x)*Q^p.val.val)) := by
  let c := mixtureCoefficients μ p
  have htcont : ContinuousAt (fun s : ℝ => c*(s^2-1)) 1 :=
    continuousAt_const.mul ((continuousAt_id.pow 2).sub continuousAt_const)
  have hpos : ∀ᶠ s : ℝ in 𝓝 1, 0 < s :=
    continuousAt_id.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1:ℝ) ∈ Ioi 0))
  have hbound : ∀ᶠ s : ℝ in 𝓝 1,
      c*(s^2-1) ∈ Ioo (-1 : ℝ) 1 :=
    htcont.eventually (isOpen_Ioo.mem_nhds (by norm_num : c*((1:ℝ)^2-1) ∈ Ioo (-1:ℝ) 1))
  obtain ⟨l,u,⟨hl,hu⟩,hlu⟩ := (hpos.and hbound).exists_Ioo_subset
  let δ : ℝ := min (1-l) (u-1)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hlocal (s : ℝ) (hs : s ∈ Ioo (1-δ) (1+δ)) :
      0 < s ∧ c*(s^2-1) ∈ Ioo (-1 : ℝ) 1 := by
    apply hlu
    constructor
    · dsimp [δ] at hs
      have hmin := min_le_left (1-l) (u-1)
      linarith [hs.1]
    · dsimp [δ] at hs
      have hmin := min_le_right (1-l) (u-1)
      linarith [hs.2]
  apply physical_pairPower_tendsto_of_active_degree_parisi h hβ p hcp δ hδ
  intro s hs
  obtain ⟨hspos,ht⟩ := hlocal s hs
  let ν := scaleActiveDegree μ p s hspos hcp
  have hfinite (n : ℕ) : activeDegreePressure (n+2) μ β p s =
      quenchedPressure (n+2) ν β :=
    activeDegreePressure_eq_scaledMixture_quenchedPressure (by omega)
      μ β p s hspos hcp
  have hCS : activeDegreeCSValue μ β p s =
      CSParisiMeasure.variationalValue ν β :=
    activeDegreeCSValue_eq_scaledMixture_variationalValue μ β p s hspos hcp ht
  have hfun : (fun n : ℕ => activeDegreePressure (n+2) μ β p s) =
      fun n : ℕ => quenchedPressure (n+2) ν β := funext hfinite
  rw [hfun,hCS]
  exact hparisi ν

end SlowEquilibration.SphericalActiveDegreeMomentFromParisi
