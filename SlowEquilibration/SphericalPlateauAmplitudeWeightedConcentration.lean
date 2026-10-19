-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeConcentration
public import SlowEquilibration.SphericalPlateauAmplitudeDerivative

@[expose] public section

/-! # Genuine concentration of the global weighted amplitude partition

The deterministic planted drift and source penalty define the actual sphere
Gibbs base law. Its support and the physical bank feature bound prove the
Gaussian Lipschitz constant independently of the reference and penalty.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm GaussianSpinInterpolation
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Exact Gaussian partition representation at every amplitude, retaining
its actual deterministic drift and source smooth penalty. -/
theorem amplitudeWeightedGaussianLog_eq (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (w : EuclideanBank n μ) :
    logPartition (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
      (amplitudeBankLinear μ β x e p₀ s) w=
      Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ s (unpackBankCLM n μ w))-
        Real.log (partition (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x)) := by
  rw [logPartition_gibbs_eq_ratio (by omega) (amplitudeBasePotential_continuous μ β J δ q₁ q₂ x)
    _ (fun w => (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (amplitudeBankLinear_continuous μ β x e p₀ s))]
  congr 2
  unfold partition amplitudePartition
  apply integral_congr_ae
  exact .of_forall fun u => by
    dsimp only
    rw [amplitudeBankLinear_apply,one_mul]
    congr 1
    unfold amplitudeBasePotential amplitudePlantedField
    ring

theorem amplitudeWeightedLogPartition_gaussian_lipschitz (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) :
    LipschitzWith (2*|β| * Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)).toNNReal
      (fun w : EuclideanBank n μ => Real.log
        (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s (unpackBankCLM n μ w))) := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x
  let ν := gibbsLaw (n+1) 1 A
  let L := amplitudeBankLinear μ β x (latitudeFrameAt x) p₀ s
  have hA : Continuous A := amplitudeBasePotential_continuous μ β J δ q₁ q₂ x
  let _ := gibbsLaw_probability (by omega : 1≤n+1) 1 hA
  have hb : ∀ᵐ u ∂ν,‖L u‖≤2*|β| * Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1) := by
    filter_upwards [gibbsLaw_support (by omega : 1≤n+1) 1 A] with u hu
    dsimp [L]
    rw [amplitudeBankLinear,norm_smul,Real.norm_eq_abs,innerSL_apply_norm]
    have hf := amplitudeBankFeature_norm_le μ x hx p₀ s hs u
      (by simpa only [Nat.cast_add,Nat.cast_one] using hu)
    exact (mul_le_mul_of_nonneg_left hf (abs_nonneg β)).trans_eq (by ring)
  have hLip := GaussianPerturbationFluctuation.logPartition_lipschitz ν L
    (amplitudeBankLinear_continuous μ β x (latitudeFrameAt x) p₀ s).measurable
    (by positivity : 0≤2*|β| * Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)) hb
  apply LipschitzWith.of_dist_le_mul
  intro w v
  have hh := hLip.dist_le_mul w v
  have hw := amplitudeWeightedGaussianLog_eq μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s w
  have hv := amplitudeWeightedGaussianLog_eq μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s v
  change dist (logPartition ν L w) (logPartition ν L v)≤_ at hh
  rw [hw,hv,Real.dist_eq,sub_sub_sub_cancel_right] at hh
  simpa only [Real.dist_eq] using hh

/-- Closed true tN Gaussian tail about the literal bank-law expected logarithm.
All deterministic source parameters and every amplitude in the source box
share the physical Gaussian constant. -/
theorem amplitudeWeightedLogPartition_pressure_concentration
    (μ : FiniteMixture) {β t : ℝ} (hβ : 0<β) (ht : 0<t) (J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) :
    bankLaw n μ {D | t*((n+1 : ℕ) : ℝ)≤
      |Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)-
        ∫ E,Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s E) ∂bankLaw n μ|}≤
      ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1))) := by
  let F : EuclideanBank n μ → ℝ := fun w => Real.log
    (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s (unpackBankCLM n μ w))
  let L : ℝ := 2*|β| * Real.sqrt (((n+1 : ℕ) : ℝ)*μ.xi 1)
  have hL : 0<L := by
    dsimp [L]
    exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hβ.ne'))
      (Real.sqrt_pos.mpr (mul_pos (by positivity) (μ.xi_pos (by norm_num))))
  have hLip := amplitudeWeightedLogPartition_gaussian_lipschitz μ β J δ q₁ q₂ x hx p₀ s hs
  have hlaw := actual_bank_flattened_gaussian n μ
  have hmean : (∫ D,Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D) ∂bankLaw n μ)=
      ∫ w,F w ∂stdGaussian (EuclideanBank n μ) := by
    simpa only [F,Function.comp_apply,unpackBank_euclideanBank] using
      hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have h := euclidean_lipschitz_gaussian_closed_tail F L (t*((n+1 : ℕ) : ℝ)) hL (by positivity) hLip
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at h
  have hset : MeasurableSet {w : EuclideanBank n μ | t*((n+1 : ℕ) : ℝ)≤
      |F w-(∫ y,F y ∂stdGaussian (EuclideanBank n μ))|} :=
    measurableSet_le measurable_const ((hLip.continuous.sub continuous_const).abs.measurable)
  nth_rw 1 [← hlaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at h
  have hpow : L^2=4*β^2*((n+1 : ℕ) : ℝ)*μ.xi 1 := by
    dsimp [L]
    rw [mul_pow,mul_pow,sq_abs,Real.sq_sqrt (mul_nonneg (by positivity) (μ.xi_pos (by norm_num)).le)]
    ring
  have he : -(t*((n+1 : ℕ) : ℝ))^2/(2*L^2)=-(t^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1) := by
    rw [hpow]
    field_simp
    ring
  rw [he] at h
  simpa only [Set.preimage_ofPred_eq,F,unpackBank_euclideanBank,hmean] using h

/-- Genuine normalized weighted-pressure concentration at every dimension. -/
theorem amplitudeWeightedPressure_concentration
    (μ : FiniteMixture) {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) (J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2) :
    bankLaw n μ {D | ε≤
      |Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s|}≤
      ENNReal.ofReal (2*Real.exp (-(ε^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1))) := by
  have h := amplitudeWeightedLogPartition_pressure_concentration μ hβ hε J δ q₁ q₂ x hx p₀ s hs
  have hN : 0<((n+1 : ℕ) : ℝ) := by positivity
  have hset : {D : BankDisorder n μ | ε≤
      |Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
        amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s|}=
      {D : BankDisorder n μ | ε*((n+1 : ℕ) : ℝ)≤
        |Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)-
          ∫ E,Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s E) ∂bankLaw n μ|} := by
    ext D
    simp only [Set.mem_ofPred_eq,amplitudeExpectedPressure,Nat.cast_add,Nat.cast_one,
      ← sub_div,abs_div,abs_of_pos (by simpa only [Nat.cast_add,Nat.cast_one] using hN)]
    exact le_div_iff₀ (by simpa only [Nat.cast_add,Nat.cast_one] using hN)
  rw [hset]
  exact h

/-- Uniform exponential weighted-pressure tail about the true expected
pressure, before every reference axis and every source amplitude. -/
theorem amplitudeWeightedPressure_concentration_eventually
    (μ : FiniteMixture) {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) (p₀ : Degree μ.maxDegree) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (J δ q₁ q₂ : ℝ)
      (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
        bankLaw n μ {D | ε≤
          |Real.log (amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D)/((n+1 : ℕ) : ℝ)-
            amplitudeExpectedPressure μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s|}≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  let α : ℝ := ε^2/(8*β^2*μ.xi 1)
  have hα : 0<α := by
    have hcov := μ.xi_pos (by norm_num : (0 : ℝ)<1)
    dsimp [α]
    positivity
  obtain ⟨γ,hγ,htail⟩ := latitude_polynomial_tail_eventually_le 0 hα
  refine ⟨γ,hγ,?_⟩
  filter_upwards [htail] with n htail
  intro J δ q₁ q₂ s hs x hx
  apply (amplitudeWeightedPressure_concentration μ hβ hε J δ q₁ q₂ x hx p₀ s hs).trans
  have he : -(ε^2*((n+1 : ℕ) : ℝ))/(8*β^2*μ.xi 1)=-α*((n+1 : ℕ) : ℝ) := by
    dsimp [α]
    ring
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  simp only [pow_zero] at htail
  nlinarith [Real.exp_pos (-((n+1 : ℕ) : ℝ)/2),Real.exp_pos (-α*((n+1 : ℕ) : ℝ))]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
