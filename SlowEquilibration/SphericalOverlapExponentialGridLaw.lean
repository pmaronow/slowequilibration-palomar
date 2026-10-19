-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOverlapExponentialMaximal
public import SphericalAging.BrownianFutureFiltered

/-! Genuine deterministic waiting-time law of overlap excursions. Countable
dyadic events are jointly Borel, and actual future-Wiener restart plus the
literal independent future product law prove each grid-cell probability. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalOverlapExponential
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalC1Dynamics
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def jointPhysicalProcess (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (t : ℝ≥0) (eta : VectorBrownian.Space N) : State N :=
  FixedCoefficients.jointProcess (FixedCoefficients.canonicalDriver N)
    (cutoffDrift_lipschitz β g hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x t eta

lemma jointPhysicalProcess_measurable (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) :
    Measurable (fun q : State N × VectorBrownian.Space N => jointPhysicalProcess β g hg q.1 t q.2) :=
  FixedCoefficients.terminal_measurable _ _ _ t

lemma jointPhysicalProcess_ae_actual (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) :
    ∀ᵐ eta ∂VectorBrownian.law N,∀ t,jointPhysicalProcess β g hg x t eta = process β g hg x t eta :=
  FixedCoefficients.jointProcess_ae _ _ _ x

lemma process_future_restart (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (s t : ℝ≥0) :
    process β g hg x (s + t) =ᵐ[VectorBrownian.law N]
      fun omega => jointPhysicalProcess β g hg (process β g hg x s omega) t (BrownianFuturePath.future s omega) :=
  FixedCoefficients.future_restart _ _ (coefficientBounds β g hg) x s t

def dyadicCell {Ω : Type*} (u : State N) (X : ℝ≥0 → Ω → State N)
    (s T : ℝ≥0) (δ : ℝ) : Set Ω :=
  {omega | ∃ n k : ℕ,k ≤ 2 ^ n ∧ δ <
    |overlapValue u (X (s + uniformPartitionTime T (2 ^ n) k) omega) - overlapValue u (X s omega)|}

def dyadicRow (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (u : State N) (T : ℝ≥0) (δ : ℝ) : Set (State N × VectorBrownian.Space N) :=
  {q | ∃ n k : ℕ,k ≤ 2 ^ n ∧ δ <
    |overlapValue u (jointPhysicalProcess β g hg q.1 (uniformPartitionTime T (2 ^ n) k) q.2) - overlapValue u q.1|}

lemma dyadicRow_measurable (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (u : State N) (T : ℝ≥0) (δ : ℝ) : MeasurableSet (dyadicRow β g hg u T δ) := by
  unfold dyadicRow
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : k ≤ 2 ^ n
  · simp only [hk,true_and]
    have hm := ((overlapLinear u).continuous.measurable.comp
      (jointPhysicalProcess_measurable β g hg (uniformPartitionTime T (2 ^ n) k))).sub
        ((overlapLinear u).continuous.measurable.comp measurable_fst)
    simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.sub_apply,overlapValue] using measurableSet_lt measurable_const (measurable_norm.comp hm)
  · simp only [hk,false_and,ofPred_false]
    exact MeasurableSet.empty

lemma dyadicCell_measurable (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (u x : State N) (s T : ℝ≥0) (δ : ℝ) : MeasurableSet (dyadicCell u (process β g hg x) s T δ) := by
  unfold dyadicCell
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : k ≤ 2 ^ n
  · simp only [hk,true_and]
    have hm := ((overlapLinear u).continuous.measurable.comp
      (process_measurable β g hg x (s + uniformPartitionTime T (2 ^ n) k))).sub
        ((overlapLinear u).continuous.measurable.comp (process_measurable β g hg x s))
    simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.sub_apply,overlapValue] using measurableSet_lt measurable_const (measurable_norm.comp hm)
  · simp only [hk,false_and,ofPred_false]
    exact MeasurableSet.empty

lemma dyadicCell_future_event (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (u x : State N) (s T : ℝ≥0) (δ : ℝ) :
    ∀ᵐ omega ∂VectorBrownian.law N,
      omega ∈ dyadicCell u (process β g hg x) s T δ ↔
        (process β g hg x s omega,BrownianFuturePath.future s omega) ∈ dyadicRow β g hg u T δ := by
  have hr : ∀ᵐ omega ∂VectorBrownian.law N,∀ n k : ℕ,
      process β g hg x (s + uniformPartitionTime T (2 ^ n) k) omega =
        jointPhysicalProcess β g hg (process β g hg x s omega) (uniformPartitionTime T (2 ^ n) k)
          (BrownianFuturePath.future s omega) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => process_future_restart β g hg x s _))
  filter_upwards [hr] with omega homega
  simp only [dyadicCell,dyadicRow,mem_ofPred_eq]
  simp_rw [homega]

lemma dyadicRow_section_bound (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u y : State N) (hu : OnSphere u) (hy : OnSphere y) {δ : ℝ} (hδ : 0 < δ)
    (T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real {eta | (y,eta) ∈ dyadicRow β g hg u T δ} ≤
      2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  have he : {eta | (y,eta) ∈ dyadicRow β g hg u T δ} =ᵐ[VectorBrownian.law N]
      {eta | ∃ n k : ℕ,k ≤ 2 ^ n ∧ δ <
        |overlapValue u (process β g hg y (uniformPartitionTime T (2 ^ n) k) eta) - overlapValue u y|} := by
    filter_upwards [jointPhysicalProcess_ae_actual β g hg y] with eta heta
    simp only [dyadicRow,mem_ofPred_eq]
    simp_rw [heta]
  have hsub : {eta | ∃ n k : ℕ,k ≤ 2 ^ n ∧ δ <
      |overlapValue u (process β g hg y (uniformPartitionTime T (2 ^ n) k) eta) - overlapValue u y|} ⊆
      {eta | ∃ t : ℝ≥0,t ≤ T ∧ δ < |overlapValue u (process β g hg y t eta) - overlapValue u y|} := by
    intro eta heta
    obtain ⟨n,k,hk,hd⟩ := heta
    exact ⟨uniformPartitionTime T (2 ^ n) k,
      (uniformPartitionTime_mem_Icc_of_le T (by positivity : 0 < 2 ^ n) hk).2,hd⟩
  rw [measureReal_def,measure_congr he]
  exact (measureReal_mono hsub).trans
    (overlap_absolute_short_window_tail hN hβ hC g hg hgrad u y hu hy hδ T hT hshort)

lemma continuous_excursion_mem_dyadicCell {Ω : Type*} (u : State N) (X : ℝ≥0 → Ω → State N)
    (s T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (omega : Ω)
    (hc : Continuous (fun t => X t omega))
    (hexc : ∃ t : ℝ≥0,t ≤ T ∧ δ < |overlapValue u (X (s+t) omega) - overlapValue u (X s omega)|) :
    omega ∈ dyadicCell u X s T δ := by
  obtain ⟨t,ht,hex⟩ := hexc
  let R : ℝ≥0 → Ω → ℝ := fun r w => overlapValue u (X (s+r) w) - overlapValue u (X s w)
  have hRc : Continuous (fun r => R r omega) :=
    (((overlapLinear u).continuous.comp hc).comp (continuous_const.add continuous_id)).sub continuous_const
  have hsq : δ ^ 2 < (R t omega) ^ 2 := by
    have hh := (sq_lt_sq₀ hδ.le (abs_nonneg (R t omega))).mpr hex
    simpa only [sq_abs] using hh
  obtain ⟨n,hn⟩ := exists_lt_dyadicPartitionSqMax_of_continuous R T omega hRc ht hsq
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun k => (R (uniformPartitionTime T (2 ^ n) k) omega) ^ 2)
  change δ ^ 2 < (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => (R (uniformPartitionTime T (2 ^ n) k) omega) ^ 2) at hn
  rw [he] at hn
  refine ⟨n,k,Nat.le_of_lt_succ (Finset.mem_range.mp hk),?_⟩
  have hsqabs : δ ^ 2 < |R (uniformPartitionTime T (2 ^ n) k) omega| ^ 2 := by
    simpa only [sq_abs] using hn
  exact (sq_lt_sq₀ hδ.le (abs_nonneg _)).mp hsqabs

/-- Actual future-product integration yields a uniform cell bound at every
fixed deterministic waiting time of the original physical process. -/
theorem dyadicCell_probability (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {δ : ℝ} (hδ : 0 < δ)
    (s T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real (dyadicCell u (process β g hg x) s T δ) ≤
      2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  let P := VectorBrownian.law N
  let Z := process β g hg x s
  let ρ := P.map Z
  let A := dyadicRow β g hg u T δ
  let φ := fun omega => (Z omega,BrownianFuturePath.future s omega)
  have hZ : Measurable[physicalFiltration N s] Z :=
    (GlobalSDE.process_stronglyAdapted (FixedCoefficients.canonicalDriver N)
      (cutoffDrift_lipschitz β g hg _ (cutoffRadius_pos N)).choose_spec
      (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x s).measurable
  have hmZ : Measurable Z := hZ.mono ((physicalFiltration N).le s) le_rfl
  let : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hφ : MeasurePreserving φ P (ρ.prod P) :=
    BrownianFutureFiltered.waiting_future_measurePreserving s Z hZ
  have hA : MeasurableSet A := dyadicRow_measurable β g hg u T δ
  have he : P (dyadicCell u (process β g hg x) s T δ) = (ρ.prod P) A := by
    calc
      _ = P (φ ⁻¹' A) := measure_congr ((dyadicCell_future_event β g hg u x s T δ).mono (fun _ h => propext h))
      _ = P.map φ A := (Measure.map_apply hφ.measurable hA).symm
      _ = _ := by rw [hφ.map_eq]
  have hSphereρ : ∀ᵐ y ∂ρ,OnSphere y :=
    (ae_map_iff hmZ.aemeasurable (sphere_measurableSet N)).mpr
      ((process_onSphere hN β g hg x hx).mono (fun _ h => h s))
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) (ρ.prod P) :=
    (integrable_const 1).indicator hA
  have hrow : ∀ᵐ y ∂ρ,(∫ eta,A.indicator (fun _ => (1 : ℝ)) (y,eta) ∂P) ≤
      2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
    filter_upwards [hSphereρ] with y hy
    let S : Set (VectorBrownian.Space N) := {eta | (y,eta) ∈ A}
    have hS : MeasurableSet S := hA.preimage (measurable_const.prodMk measurable_id)
    have hfun : (fun eta => A.indicator (fun _ => (1 : ℝ)) (y,eta)) = S.indicator (fun _ => (1 : ℝ)) := by
      funext eta
      by_cases heta : (y,eta) ∈ A <;> simp [S,heta]
    rw [hfun,integral_indicator_const 1 hS]
    simpa only [smul_eq_mul,mul_one] using dyadicRow_section_bound hN hβ hC g hg hgrad u y hu hy hδ T hT hshort
  rw [measureReal_def,he]
  have hprob : (ρ.prod P).real A = ∫ q,A.indicator (fun _ => (1 : ℝ)) q ∂ρ.prod P := by
    rw [integral_indicator_const 1 hA]
    simp
  change (ρ.prod P).real A ≤ _
  rw [hprob,integral_prod _ hi]
  have hb := integral_mono_ae hi.integral_prod_left (integrable_const
    (2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))))) hrow
  simpa only [integral_const,probReal_univ,one_smul] using hb

/-- A genuine shifted continuous-cell tail on the original path. The law is
proved through the measurable actual Wiener-future product event. -/
theorem shifted_overlap_absolute_short_window_tail (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {δ : ℝ} (hδ : 0 < δ)
    (s T : ℝ≥0) (hT : 0 < T) (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ δ) :
    (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ T ∧
      δ < |overlapValue u (process β g hg x (s + t) omega) - overlapValue u (process β g hg x s omega)|} ≤
      2 * Real.exp (-(N : ℝ) * δ ^ 2 / (16 * (T : ℝ))) := by
  have hc : {omega | ∃ t : ℝ≥0,t ≤ T ∧ δ <
      |overlapValue u (process β g hg x (s + t) omega) - overlapValue u (process β g hg x s omega)|}
      ≤ᵐ[VectorBrownian.law N] dyadicCell u (process β g hg x) s T δ := by
    filter_upwards [process_continuous β g hg x] with omega homega hex
    exact continuous_excursion_mem_dyadicCell u (process β g hg x) s T hδ omega homega hex
  have hm := ENNReal.toReal_mono (by finiteness) (measure_mono_ae hc)
  exact hm.trans (dyadicCell_probability hN hβ hC g hg hgrad u x hu hx hδ s T hT hshort)

end SlowEquilibration.SphericalOverlapExponential
