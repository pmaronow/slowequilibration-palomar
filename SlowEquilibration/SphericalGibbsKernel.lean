-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PlantedLaw
public import Mathlib.Probability.Kernel.WithDensity

/-! The actual normalized mixed spherical Gibbs laws form a genuine
Markov kernel in the disorder. Joint measurability comes from the actual
tensor polynomial and the literal partition integral. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N P : ℕ}

/-- Literal disorder-indexed Gibbs laws, normalized by the actual sphere
partition integral, as a measurable kernel. -/
def disorderGibbsKernel (_hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ) :
    Kernel (Disorder N P) (Vector N) :=
  let _ := sphereLaw_probability N
  (Kernel.const (Disorder N P) (sphereLaw N)).withDensity
    (fun J x => ENNReal.ofReal (gibbsDensity N β (field c J) x))

@[simp] theorem disorderGibbsKernel_apply (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder N P) : disorderGibbsKernel hN c β J = gibbsLaw N β (field c J) := by
  let _ := sphereLaw_probability N
  unfold disorderGibbsKernel
  rw [Kernel.withDensity_apply _ (gibbsReferenceDensity_measurable (N := N) c β).ennreal_ofReal]
  rfl

instance disorderGibbsKernel_isMarkov (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ) :
    IsMarkovKernel (disorderGibbsKernel hN c β) where
  isProbabilityMeasure J := by
    rw [disorderGibbsKernel_apply]
    exact gibbsLaw_probability hN β (field_contDiff c J).continuous

theorem disorder_gibbsLaw_measurable (hN : 1 ≤ N) (c : Degree P → ℝ) (β : ℝ) :
    Measurable (fun J : Disorder N P => gibbsLaw N β (field c J)) := by
  have he : (fun J : Disorder N P => gibbsLaw N β (field c J)) =
      (fun J => disorderGibbsKernel hN c β J) := by
    funext J
    exact (disorderGibbsKernel_apply hN c β J).symm
  rw [he]
  exact (disorderGibbsKernel hN c β).measurable

theorem mixtureGibbsLaw_measurable (hN : 1 ≤ N) (μ : SlowEquilibration.FiniteMixture) (β : ℝ) :
    Measurable (fun J : Disorder N μ.maxDegree => mixtureGibbsLaw μ β J) :=
  disorder_gibbsLaw_measurable hN (mixtureCoefficients μ) β

end SlowEquilibration.SphericalModel
