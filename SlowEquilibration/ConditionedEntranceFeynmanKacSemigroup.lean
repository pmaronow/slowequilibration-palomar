-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacWaiting

/-! The actual path-weighted physical expectations satisfy the killed
semigroup identity.  The temporal law is derived using the genuine SDE
restart and the true independent future Wiener path. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalDynamics
open SphericalDynamics.FixedCoefficients BrownianFuturePath BrownianFutureFiltered
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem occupation_add {E Ω : Type*} [TopologicalSpace E]
    (κ : E → ℝ) (hκ : Continuous κ) (X : ℝ≥0 → Ω → E) (ω : Ω)
    (hc : Continuous (fun r => X r ω)) (s t : ℝ≥0) :
    occupation κ X (s+t) ω = occupation κ X s ω +
      occupation κ (fun r => X (s+r)) t ω := by
  let g : ℝ → ℝ := fun r => κ (X r.toNNReal ω)
  have hg : Continuous g := hκ.comp (hc.comp continuous_real_toNNReal)
  have hs : occupation κ (fun r => X (s+r)) t ω = ∫ r in (s : ℝ)..(s : ℝ)+t, g r := by
    calc
      _ = ∫ r in (0 : ℝ)..(t : ℝ), g ((s : ℝ)+r) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr0 : 0 ≤ r := (show r ∈ Icc (0 : ℝ) t from by
          simpa only [uIcc_of_le t.coe_nonneg] using hr).1
        have he : s+r.toNNReal = ((s : ℝ)+r).toNNReal := by
          apply NNReal.eq
          simp only [NNReal.coe_add,Real.coe_toNNReal r hr0,
            Real.coe_toNNReal ((s : ℝ)+r) (add_nonneg s.coe_nonneg hr0)]
        exact congrArg (fun u => κ (X u ω)) he
      _ = _ := by rw [intervalIntegral.integral_comp_add_left,add_zero]
  rw [hs]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (0 : ℝ) s) (hg.intervalIntegrable s ((s : ℝ)+t))).symm

theorem survival_add {E Ω : Type*} [TopologicalSpace E]
    (κ : E → ℝ) (hκ : Continuous κ) (X : ℝ≥0 → Ω → E) (ω : Ω)
    (hc : Continuous (fun r => X r ω)) (s t : ℝ≥0) :
    survival κ X (s+t) ω = survival κ X s ω *
      survival κ (fun r => X (s+r)) t ω := by
  simp only [survival,occupation_add κ hκ X ω hc s t,neg_add,Real.exp_add]

variable {N : ℕ} {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {σ : Fin N → Fin N → State N → ℝ}
  (hb : ∀ i, LipschitzWith Kb (b i)) (hσ : ∀ i j, LipschitzWith Ks (σ i j))

theorem flow_stronglyAdapted (x : State N) : StronglyAdapted
    (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))
    (flow hb hσ x) := by
  intro s
  exact (jointProcess_adapted (canonicalDriver N) hb hσ s).comp_measurable
    (measurable_const.prodMk measurable_id)

theorem flow_ae_continuous (x : State N) :
    ∀ᵐ ω ∂VectorBrownian.law N, Continuous (fun r => flow hb hσ x r ω) := by
  filter_upwards [jointProcess_ae (canonicalDriver N) hb hσ x,
    GlobalSDE.process_continuous (canonicalDriver N) hb hσ x] with ω he hc
  exact hc.congr (fun r => (he r).symm)

/-- Literal physical bounded-killing transition, with no abstract
generator or semigroup premise. -/
def killedTransition (κ : State N → ℝ) (t : ℝ≥0) (f : State N → ℝ) (x : State N) : ℝ :=
  killedExpectation (VectorBrownian.law N) κ (flow hb hσ x) t f

theorem killedIntegrand_stronglyMeasurable (κ : State N → ℝ) (hκ : Continuous κ)
    (t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f) : StronglyMeasurable
    (fun q : State N × VectorBrownian.Space N =>
      survival κ (flow hb hσ q.1) t q.2 * f (flow hb hσ q.1 t q.2)) := by
  let X : ℝ≥0 → State N × VectorBrownian.Space N → State N :=
    fun r q => flow hb hσ q.1 r q.2
  have hX : Measurable (Function.uncurry X) := (flow_measurable hb hσ).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  exact (survival_stronglyMeasurable κ hκ.measurable X hX t).mul
    (hf.comp_measurable (flow_terminal_measurable hb hσ t))

theorem killedTransition_stronglyMeasurable (κ : State N → ℝ) (hκ : Continuous κ)
    (t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (killedTransition hb hσ κ t f) :=
  (killedIntegrand_stronglyMeasurable hb hσ κ hκ t f hf).integral_prod_right'

/-- The true killed semigroup law is obtained by splitting occupation,
restarting the genuine SDE, and integrating the independent Wiener future. -/
theorem killedTransition_add (B : CoefficientBounds b σ)
    (κ : State N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (s t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f)
    (C : ℝ) (_hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) (x : State N) :
    killedTransition hb hσ κ (s+t) f x =
      killedTransition hb hσ κ s (killedTransition hb hσ κ t f) x := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let X := flow hb hσ x
  obtain ⟨H,hHm,hHb,hHW⟩ := survival_waiting_representative F κ hκ hκ0 X
    (flow_stronglyAdapted hb hσ x) (flow_ae_continuous hb hσ x) s
  let Z : VectorBrownian.Space N → State N × ℝ := fun ω => (X s ω,H ω)
  have hZa : Measurable[F s] Z := ((flow_stronglyAdapted hb hσ x) s).measurable.prodMk hHm.measurable
  have hZm : Measurable Z := hZa.mono (F.le s) le_rfl
  let ρ := P.map Z
  let : IsProbabilityMeasure ρ := (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let G : (State N × ℝ) × VectorBrownian.Space N → ℝ :=
    fun q => q.1.2 * (survival κ (flow hb hσ q.1.1) t q.2 * f (flow hb hσ q.1.1 t q.2))
  have hG : StronglyMeasurable G := (measurable_snd.comp measurable_fst).stronglyMeasurable.mul
    ((killedIntegrand_stronglyMeasurable hb hσ κ hκ t f hf).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hHρ : ∀ᵐ z ∂ρ, ‖z.2‖ ≤ 1 :=
    (ae_map_iff hZm.aemeasurable (measurableSet_le measurable_snd.norm measurable_const)).mpr
      (.of_forall (fun ω => by rw [Real.norm_of_nonneg (hHb ω).1]; exact (hHb ω).2))
  have hGi : Integrable G (ρ.prod P) := by
    apply Integrable.of_bound hG.aestronglyMeasurable C
    filter_upwards [(measurePreserving_fst (μ := ρ) (ν := P)).quasiMeasurePreserving.ae hHρ] with q hq
    change ‖q.1.2 * (survival κ (flow hb hσ q.1.1) t q.2 * f (flow hb hσ q.1.1 t q.2))‖ ≤ C
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (survival_nonneg κ _ _ _)]
    exact (mul_le_of_le_one_left (mul_nonneg (survival_nonneg κ _ _ _) (norm_nonneg _))
      hq).trans ((mul_le_of_le_one_left (norm_nonneg _)
        (survival_le_one κ hκ0 _ _ _)).trans (hC _))
  let φ : VectorBrownian.Space N → (State N × ℝ) × VectorBrownian.Space N :=
    fun ω => (Z ω,future s ω)
  have hφ : MeasurePreserving φ P (ρ.prod P) := waiting_future_measurePreserving s Z hZa
  have hpull : (∫ ω, G (φ ω) ∂P) = ∫ q, G q ∂ρ.prod P := by
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hG.aestronglyMeasurable).symm
  have hfuture : (∫ ω, survival κ X (s+t) ω * f (X (s+t) ω) ∂P) =
      ∫ ω, G (φ ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [flow_ae_continuous hb hσ x,hHW,
      flow_survival_restart hb hσ B x κ hκ.measurable s t,
      flow_future_restart hb hσ B x s t] with ω hc hH hw hx
    change survival κ X (s+t) ω * f (X (s+t) ω) =
      H ω * (survival κ (flow hb hσ (X s ω)) t (future s ω) *
        f (flow hb hσ (X s ω) t (future s ω)))
    change X (s+t) ω = flow hb hσ (X s ω) t (future s ω) at hx
    change survival κ (fun r => X (s+r)) t ω =
      survival κ (flow hb hσ (X s ω)) t (future s ω) at hw
    rw [survival_add κ hκ X ω hc s t,hx,hw,← hH]
    ring
  have hinner : (∫ q, G q ∂ρ.prod P) =
      ∫ z : State N × ℝ, z.2 * killedTransition hb hσ κ t f z.1 ∂ρ := by
    rw [integral_prod G hGi]
    apply integral_congr_ae
    exact .of_forall (fun z => by
      change (∫ η, z.2 * (survival κ (flow hb hσ z.1) t η * f (flow hb hσ z.1 t η)) ∂P) =
        z.2 * (∫ η, survival κ (flow hb hσ z.1) t η * f (flow hb hσ z.1 t η) ∂P)
      exact integral_const_mul _ _)
  have hback : (∫ z : State N × ℝ, z.2 * killedTransition hb hσ κ t f z.1 ∂ρ) =
      ∫ ω, H ω * killedTransition hb hσ κ t f (X s ω) ∂P := by
    apply integral_map hZm.aemeasurable
      (measurable_snd.stronglyMeasurable.mul
        ((killedTransition_stronglyMeasurable hb hσ κ hκ t f hf).comp_measurable measurable_fst)).aestronglyMeasurable
  calc
    _ = ∫ ω, survival κ X (s+t) ω * f (X (s+t) ω) ∂P := rfl
    _ = ∫ ω, G (φ ω) ∂P := hfuture
    _ = ∫ q, G q ∂ρ.prod P := hpull
    _ = ∫ z : State N × ℝ, z.2 * killedTransition hb hσ κ t f z.1 ∂ρ := hinner
    _ = ∫ ω, H ω * killedTransition hb hσ κ t f (X s ω) ∂P := hback
    _ = _ := integral_congr_ae (hHW.mono (fun ω h => by
      change H ω * killedTransition hb hσ κ t f (X s ω) =
        survival κ X s ω * killedTransition hb hσ κ t f (X s ω)
      rw [h]))

end SlowEquilibration.ConditionedEntrance.FeynmanKac
