-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacPhysical
public import SphericalAging.BrownianFutureConditionalIntegral

/-! Temporal restart of the true killing occupation.  The future
occupation is derived from the original SDE restart and Fubini, rather
than supplied as a Markov or Feynman--Kac identity. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalDynamics
open SphericalDynamics.FixedCoefficients BrownianFuturePath
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {σ : Fin N → Fin N → State N → ℝ}
  (hb : ∀ i, LipschitzWith Kb (b i)) (hσ : ∀ i j, LipschitzWith Ks (σ i j))

/-- The jointly Borel representative of the actual original Picard flow. -/
def flow (x : State N) : ℝ≥0 → VectorBrownian.Space N → State N :=
  jointProcess (canonicalDriver N) hb hσ x

theorem flow_measurable : Measurable
    (fun q : State N × (ℝ≥0 × VectorBrownian.Space N) => flow hb hσ q.1 q.2.1 q.2.2) :=
  (jointProcess_measurable (canonicalDriver N) hb hσ).measurable

theorem flow_terminal_measurable (s : ℝ≥0) :
    Measurable (fun q : State N × VectorBrownian.Space N => flow hb hσ q.1 s q.2) :=
  terminal_measurable (canonicalDriver N) hb hσ s

theorem flow_future_restart (B : CoefficientBounds b σ) (x : State N) (s t : ℝ≥0) :
    flow hb hσ x (s+t) =ᵐ[VectorBrownian.law N]
      fun ω => flow hb hσ (flow hb hσ x s ω) t (future s ω) := by
  filter_upwards [jointProcess_ae (canonicalDriver N) hb hσ x,
    future_restart hb hσ B x s t] with ω hj hr
  change ∀ t, flow hb hσ x t ω = _ at hj
  rw [hj (s+t),hj s]
  exact hr

/-- Restart also identifies the whole cumulative future hazard.  Only
fixed-time SDE restart is needed: jointly Borel representatives and
Fubini turn those identities into an almost-everywhere time identity. -/
theorem flow_occupation_restart (B : CoefficientBounds b σ) (x : State N)
    (κ : State N → ℝ) (hκ : Measurable κ) (s t : ℝ≥0) :
    (fun ω => occupation κ (fun r => flow hb hσ x (s+r)) t ω)
      =ᵐ[VectorBrownian.law N]
    fun ω => occupation κ (flow hb hσ (flow hb hσ x s ω)) t (future s ω) := by
  let f : ℝ × VectorBrownian.Space N → ℝ :=
    fun q => κ (flow hb hσ x (s+q.1.toNNReal) q.2)
  let g : ℝ × VectorBrownian.Space N → ℝ :=
    fun q => κ (flow hb hσ (flow hb hσ x s q.2) q.1.toNNReal (future s q.2))
  have hxs : Measurable (fun ω => flow hb hσ x s ω) :=
    (flow_terminal_measurable hb hσ s).comp (measurable_const.prodMk measurable_id)
  have hf : Measurable f := hκ.comp ((flow_measurable hb hσ).comp
    (measurable_const.prodMk ((measurable_const.add measurable_fst.real_toNNReal).prodMk measurable_snd)))
  have hg : Measurable g := hκ.comp ((flow_measurable hb hσ).comp
    ((hxs.comp measurable_snd).prodMk
      (measurable_fst.real_toNNReal.prodMk ((future_measurable s).comp measurable_snd))))
  have ht : ∀ᵐ ω ∂VectorBrownian.law N, ∀ᵐ r : ℝ ∂volume, f (r,ω)=g (r,ω) := by
    apply (Measure.ae_ae_comm
      (hf.stronglyMeasurable.measurableSet_eq_fun hg.stronglyMeasurable)).mp
    apply Filter.Eventually.of_forall
    intro r
    exact (flow_future_restart hb hσ B x s r.toNNReal).mono (fun _ h => congrArg κ h)
  filter_upwards [ht] with ω hω
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hω] with r hr
  exact fun _ => hr

/-- The same actual temporal restart holds for the survival multiplier. -/
theorem flow_survival_restart (B : CoefficientBounds b σ) (x : State N)
    (κ : State N → ℝ) (hκ : Measurable κ) (s t : ℝ≥0) :
    (fun ω => survival κ (fun r => flow hb hσ x (s+r)) t ω)
      =ᵐ[VectorBrownian.law N]
    fun ω => survival κ (flow hb hσ (flow hb hσ x s ω)) t (future s ω) :=
  (flow_occupation_restart hb hσ B x κ hκ s t).mono (fun _ h => by
    simp only [survival,h])

end SlowEquilibration.ConditionedEntrance.FeynmanKac
