-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralPhysical
public import SlowEquilibration.ConditionedEntranceFeynmanKacContinuous

/-! Actual path representatives and the L² semigroup law for the
nonpolynomial source cutoff killed diffusion. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalDynamics.FixedCoefficients SphericalReversibility
open SphericalSmoothTensorStationarity FeynmanKac
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def process (D : FieldData N) (β : ℝ) (x : Vector N) :
    ℝ≥0 → VectorBrownian.Space N → Vector N :=
  FeynmanKac.flow
    (SphericalC1Dynamics.cutoffDrift_lipschitz β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff)
      (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x

theorem process_measurable (D : FieldData N) (β : ℝ) (x : Vector N) :
    Measurable (Function.uncurry (process D β x)) :=
  (FeynmanKac.flow_measurable _ _).comp
    (measurable_const.prodMk measurable_id)

theorem process_ae_actual (D : FieldData N) (β : ℝ) (x : Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, process D β x t ω =
      SphericalC1Dynamics.process β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
        (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x t ω :=
  jointProcess_ae (canonicalDriver N) _ _ x

theorem process_ae_continuous (D : FieldData N) (β : ℝ) (x : Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N, Continuous (fun t => process D β x t ω) :=
  FeynmanKac.flow_ae_continuous _ _ x

theorem process_zero (D : FieldData N) (β : ℝ) (x : Vector N) :
    process D β x 0 =ᵐ[VectorBrownian.law N] fun _ => x := by
  filter_upwards [process_ae_actual D β x,
    SphericalC1Dynamics.process_zero β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x] with ω he h0
  exact (he 0).trans h0

theorem process_onSphere (D : FieldData N) (β : ℝ) (x : Vector N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, OnSphere (process D β x t ω) := by
  filter_upwards [process_ae_actual D β x,
    SphericalC1Dynamics.process_onSphere (by have := D.dimension_ge_one; omega) β
      (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x hx] with ω he hs
  intro t
  rw [he t]
  exact hs t

def expectation (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ) (t : ℝ≥0)
    (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  killedExpectation (VectorBrownian.law N) κ (process D β x) t f

theorem expectation_eq_actual (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ) (t : ℝ≥0)
    (f : Vector N → ℝ) (x : Vector N) :
    expectation D β κ t f x =
      ∫ ω, survival κ (SphericalC1Dynamics.process β
        (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
        (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x) t ω *
        f (SphericalC1Dynamics.process β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
          (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x t ω)
        ∂VectorBrownian.law N := by
  apply integral_congr_ae
  filter_upwards [process_ae_actual D β x] with ω he
  have ho : occupation κ (process D β x) t ω = occupation κ
      (SphericalC1Dynamics.process β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
        (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x) t ω := by
    apply intervalIntegral.integral_congr
    intro r _
    exact congrArg κ (he r.toNNReal)
  simp only [survival,ho,he t]

theorem kernel_integral_actual (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (t : ℝ≥0) (f : Vector N → ℝ) (hf : StronglyMeasurable f) (x : Vector N) :
    (∫ y,f y ∂kernel D β κ hκ t x)=expectation D β κ t f x :=
  FeynmanKac.killedKernel_integral _ _ κ hκ t f hf x

theorem operator_ae_expectation (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) (f : Vector N → ℝ) (hf : StronglyMeasurable f)
    (hUf : U =ᵐ[gibbsLaw N β D.hamiltonian] f) :
    operator D β κ hκ hκ0 t U =ᵐ[gibbsLaw N β D.hamiltonian] fun x => expectation D β κ t f x := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let := kernel_finite D β κ hκ hκ0 t
  have ha := KilledL2.ae_average_congr (gibbsLaw N β D.hamiltonian) (kernel D β κ hκ t)
    (kernel_gibbs_subinvariant D β κ hκ hκ0 t) hUf
  filter_upwards [operator_ae D β κ hκ hκ0 t U,ha] with x hx ha
  exact hx.trans (ha.trans (kernel_integral_actual D β κ hκ t f hf x))

theorem operator_add (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (s t : ℝ≥0) :
    operator D β κ hκ hκ0 (s+t) =
      (operator D β κ hκ hκ0 s).comp
        (operator D β κ hκ hκ0 t) := by
  let π := gibbsLaw N β D.hamiltonian
  let K := kernel D β κ hκ
  let Q := operator D β κ hκ hκ0
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let := kernel_finite D β κ hκ hκ0 s
  let := kernel_finite D β κ hκ hκ0 t
  let := kernel_finite D β κ hκ hκ0 (s+t)
  apply ContinuousLinearMap.ext
  intro U
  have hrep := Measure.ae_ae_of_ae_comp
    ((ae_mono (kernel_gibbs_subinvariant D β κ hκ hκ0 s))
      (operator_ae D β κ hκ hκ0 t U))
  have hi : Integrable (U : Vector N → ℝ) (K (s+t) ∘ₘ π) :=
    ((Lp.memLp U).integrable (by norm_num)).mono_measure
      (kernel_gibbs_subinvariant D β κ hκ hκ0 (s+t))
  have hslice := (Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi
  apply Lp.ext
  filter_upwards [operator_ae D β κ hκ hκ0 (s+t) U,
    operator_ae D β κ hκ hκ0 s (Q t U),hrep,hslice.1]
    with x hst hs hr hi
  change Q (s+t) U x = Q s (Q t U) x
  rw [hst,hs]
  calc
    _ = ∫ z, ∫ y, U y ∂K t z ∂K s x := by
      have hc := kernel_add D β κ hκ hκ0 s t x
      rw [hc] at hi ⊢
      exact Kernel.integral_comp hi
    _ = _ := by
      have hrf : (Q t U : Vector N → ℝ) =ᵐ[K s x] fun z => ∫ y, U y ∂K t z := hr
      exact integral_congr_ae (EventuallyEq.symm hrf)

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
