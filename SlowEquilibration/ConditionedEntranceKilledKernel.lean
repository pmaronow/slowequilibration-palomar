-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacSemigroup
public import Mathlib.Probability.Kernel.WithDensity

/-! The true finite subprobability transition kernel is the original
Wiener path law weighted by its literal killing survival and pushed
forward by the actual physical Picard terminal state. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalDynamics
open SphericalDynamics.FixedCoefficients
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {σ : Fin N → Fin N → State N → ℝ}
  (hb : ∀ i, LipschitzWith Kb (b i)) (hσ : ∀ i j, LipschitzWith Ks (σ i j))

theorem flow_survival_joint_measurable (κ : State N → ℝ) (hκ : Continuous κ) (t : ℝ≥0) :
    Measurable (fun q : State N × VectorBrownian.Space N => survival κ (flow hb hσ q.1) t q.2) := by
  have h := (killedIntegrand_stronglyMeasurable hb hσ κ hκ t (fun _ => 1)
    stronglyMeasurable_const).measurable
  simpa only [mul_one] using h

/-- Actual killed law, including the original physical noise probability. -/
def killedLaw (κ : State N → ℝ) (t : ℝ≥0) (x : State N) : Measure (State N) :=
  ((VectorBrownian.law N).withDensity (fun ω => ENNReal.ofReal (survival κ (flow hb hσ x) t ω))).map
    (fun ω => flow hb hσ x t ω)

def killedKernel (κ : State N → ℝ) (hκ : Continuous κ) (t : ℝ≥0) : Kernel (State N) (State N) where
  toFun := killedLaw hb hσ κ t
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hterm := flow_terminal_measurable hb hσ t
    have hw := (flow_survival_joint_measurable hb hσ κ hκ t).ennreal_ofReal
    have hi : Measurable (fun q : State N × VectorBrownian.Space N =>
        ((fun q => flow hb hσ q.1 t q.2) ⁻¹' A).indicator
          (fun q => ENNReal.ofReal (survival κ (flow hb hσ q.1) t q.2)) q) :=
      hw.indicator (hterm hA)
    convert hi.lintegral_prod_right' (ν := VectorBrownian.law N) using 1
    funext x
    have htx : Measurable (fun ω => flow hb hσ x t ω) := hterm.comp (measurable_const.prodMk measurable_id)
    rw [killedLaw,Measure.map_apply htx hA,withDensity_apply _ (htx hA),
      ← lintegral_indicator (htx hA)]
    rfl

theorem killedKernel_apply (κ : State N → ℝ) (hκ : Continuous κ) (t : ℝ≥0) (x : State N) :
    killedKernel hb hσ κ hκ t x = killedLaw hb hσ κ t x := rfl

theorem killedLaw_le_original (κ : State N → ℝ) (_hκ : Continuous κ)
    (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0) (x : State N) :
    killedLaw hb hσ κ t x ≤ transitionKernel (canonicalDriver N) hb hσ t x := by
  have hw : (VectorBrownian.law N).withDensity
      (fun ω => ENNReal.ofReal (survival κ (flow hb hσ x) t ω)) ≤ VectorBrownian.law N := by
    calc
      _ ≤ (VectorBrownian.law N).withDensity (fun _ => 1) :=
        withDensity_mono (.of_forall (fun ω => by
          simpa only [ENNReal.ofReal_one] using
            ENNReal.ofReal_le_ofReal (survival_le_one κ hκ0 (flow hb hσ x) t ω)))
      _ = _ := by simp
  have htm : Measurable (fun ω => flow hb hσ x t ω) :=
    (flow_terminal_measurable hb hσ t).comp (measurable_const.prodMk measurable_id)
  have ho : transitionKernel (canonicalDriver N) hb hσ t x =
      (VectorBrownian.law N).map (fun ω => flow hb hσ x t ω) := by
    rw [transitionKernel,Kernel.map_apply _ (terminal_measurable (canonicalDriver N) hb hσ t),
      Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
      Measure.map_map (terminal_measurable (canonicalDriver N) hb hσ t) measurable_prodMk_left]
    rfl
  rw [ho]
  change (((VectorBrownian.law N).withDensity
    (fun ω => ENNReal.ofReal (survival κ (flow hb hσ x) t ω))).map
      (fun ω => flow hb hσ x t ω)) ≤ _
  exact Measure.map_mono hw htm

theorem killedKernel_finite (κ : State N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0) : IsFiniteKernel (killedKernel hb hσ κ hκ t) :=
  ⟨⟨1,by simp,fun x => (killedLaw_le_original hb hσ κ hκ hκ0 t x univ).trans_eq (by simp)⟩⟩

theorem killedKernel_integral (κ : State N → ℝ) (hκ : Continuous κ)
    (t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f) (x : State N) :
    (∫ y, f y ∂killedKernel hb hσ κ hκ t x) = killedTransition hb hσ κ t f x := by
  have htm : Measurable (fun ω => flow hb hσ x t ω) :=
    (flow_terminal_measurable hb hσ t).comp (measurable_const.prodMk measurable_id)
  have hwm : Measurable (fun ω => ENNReal.ofReal (survival κ (flow hb hσ x) t ω)) :=
    ((flow_survival_joint_measurable hb hσ κ hκ t).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [killedKernel_apply,killedLaw,integral_map
    htm.aemeasurable
    hf.aestronglyMeasurable,integral_withDensity_eq_integral_toReal_smul
      hwm
      (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (survival_nonneg κ _ _ _),smul_eq_mul,
    killedTransition,killedExpectation]

end SlowEquilibration.ConditionedEntrance.FeynmanKac
