-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingHazard

/-! Actual finite-horizon cap hitting is controlled by genuine bounded-hazard
firing mass and the proved deterministic-grid failure probability. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory ProbabilityTheory Set Filter
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalC1Dynamics
open SphericalOverlapExponential FeynmanKac
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def exposureFactor (θ : ℝ) (H T : ℝ≥0) : ℝ :=
  Real.exp (-θ * ((H + T : ℝ≥0) : ℝ)) * (1 - Real.exp (-(T : ℝ)))

lemma exposureFactor_nonneg (θ : ℝ) (H T : ℝ≥0) : 0 ≤ exposureFactor θ H T :=
  mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr T.coe_nonneg)))

/-- Deterministic cap hitting on a good grid gives a whole literal hazard
exposure interval, hence a quantitative discounted firing mass. -/
theorem grid_hit_has_firing_mass {Ω : Type*} [MeasurableSpace Ω]
    (κ : State N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ y,0 ≤ κ y)
    (X : ℝ≥0 → Ω → State N) (u : State N) {α : ℝ} (hα : 0 < α)
    (hκcap : ∀ y,α / 3 ≤ |overlapValue u y| → 1 ≤ κ y)
    {θ : ℝ} (hθ : 0 ≤ θ) (H T : ℝ≥0) (hT : 0 < T) (omega : Ω)
    (hc : Continuous (fun t => X t omega))
    (hgood : omega ∉ badGrid (fun t eta => overlapValue u (X t eta)) H T (α / 12))
    (hhit : ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤ |overlapValue u (X t omega)|) :
    exposureFactor θ H T ≤ finiteDiscountedMass κ X θ (H + T) omega := by
  have hg : ∀ j : Fin (gridSize H T),∀ v : ℝ≥0,v ≤ T →
      |overlapValue u (X (gridStart T j.val + v) omega) - overlapValue u (X (gridStart T j.val) omega)| ≤ α / 12 :=
    fun j v hv => good_grid_cell_bound (fun t eta => overlapValue u (X t eta)) H T (α / 12) omega hgood j v hv
  obtain ⟨j,hj,hres⟩ := grid_hit_has_residence (fun t => overlapValue u (X t omega)) H T hT hα hg hhit
  let τ := gridStart T j.val
  let q : ℝ → ℝ := fun r => κ (X r.toNNReal omega)
  have hqc : Continuous q := hκ.comp (hc.comp continuous_real_toNNReal)
  have hq0 : ∀ r,0 ≤ q r := fun r => hκ0 _
  have hex : ∀ r ∈ Icc (τ : ℝ) ((τ : ℝ) + (T : ℝ)),1 ≤ q r := by
    intro r hr
    have hr0 : 0 ≤ r := τ.coe_nonneg.trans hr.1
    have hτ : τ ≤ r.toNNReal := by
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal r hr0] using hr.1
    let v := r.toNNReal - τ
    have hv : v ≤ T := by
      apply NNReal.coe_le_coe.mp
      dsimp [v]
      rw [NNReal.coe_sub hτ,Real.coe_toNNReal r hr0]
      linarith [hr.2]
    have he : τ + v = r.toNNReal := add_tsub_cancel_of_le hτ
    have hb := hres v hv
    change α / 3 ≤ |overlapValue u (X (τ + v) omega)| at hb
    rw [he] at hb
    exact hκcap _ hb
  have hEnd : (τ : ℝ) + (T : ℝ) ≤ ((H + T : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add]
    have hjR : (τ : ℝ) ≤ H := hj
    linarith
  rw [finiteDiscountedMass_eq_hazard]
  exact discounted_hazard_ge_exposure hqc hq0 hθ τ.coe_nonneg T.coe_nonneg hEnd hex

lemma jointPhysicalProcess_uncurry_measurable (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (x : State N) :
    Measurable (Function.uncurry (jointPhysicalProcess β g hg x)) :=
  (FixedCoefficients.jointProcess_measurable (FixedCoefficients.canonicalDriver N)
    (cutoffDrift_lipschitz β g hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec).measurable.comp
      (measurable_const.prodMk measurable_id)

lemma jointPhysicalProcess_continuous_ae (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (x : State N) :
    ∀ᵐ omega ∂VectorBrownian.law N,Continuous (fun t => jointPhysicalProcess β g hg x t omega) := by
  filter_upwards [jointPhysicalProcess_ae_actual β g hg x,process_continuous β g hg x] with omega he hc
  exact hc.congr (fun t => (he t).symm)

/-- Actual cap hitting probability is bounded by actual discounted firing
mass plus the genuine grid failure probability. No moment, entropy, or
conditional maximal-tail conclusion is supplied as a premise. -/
theorem joint_physical_hitting_discounted_mass (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {α : ℝ} (hα : 0 < α)
    (κ : State N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1)
    (hκcap : ∀ y,α / 3 ≤ |overlapValue u y| → 1 ≤ κ y)
    {θ : ℝ} (hθ : 0 ≤ θ) (H T : ℝ≥0) (hT : 0 < T)
    (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ α / 12) :
    exposureFactor θ H T *
      ((VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤
        |overlapValue u (jointPhysicalProcess β g hg x t omega)|} -
        (gridSize H T : ℝ) * 2 * Real.exp (-(N : ℝ) * (α / 12) ^ 2 / (16 * (T : ℝ)))) ≤
      ∫ omega,finiteDiscountedMass κ (jointPhysicalProcess β g hg x) θ (H + T) omega ∂VectorBrownian.law N := by
  let P := VectorBrownian.law N
  let X := jointPhysicalProcess β g hg x
  let c := exposureFactor θ H T
  let B := badGrid (fun t omega => overlapValue u (X t omega)) H T (α / 12)
  let A : Set (VectorBrownian.Space N) := {omega | ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤ |overlapValue u (X t omega)|}
  let F := finiteDiscountedMass κ X θ (H + T)
  have hc0 : 0 ≤ c := exposureFactor_nonneg θ H T
  have hi : Integrable F P := Integrable.of_bound
    (finiteDiscountedMass_stronglyMeasurable κ hκ.measurable X
      (jointPhysicalProcess_uncurry_measurable β g hg x) θ (H + T)).aestronglyMeasurable
    ((H + T : ℝ≥0) : ℝ) (.of_forall fun omega => finiteDiscountedMass_norm_le κ hκ0 hκ1 X hθ (H + T) omega)
  have hcover : A ≤ᵐ[P] B ∪ {omega | c ≤ F omega} := by
    filter_upwards [jointPhysicalProcess_continuous_ae β g hg x] with omega homega hhit
    by_cases hb : omega ∈ B
    · exact Or.inl hb
    · exact Or.inr (grid_hit_has_firing_mass κ hκ hκ0 X u hα hκcap hθ H T hT omega homega hb hhit)
  have hmeasure := ENNReal.toReal_mono (by finiteness) (measure_mono_ae hcover)
  have hprob : P.real A ≤ P.real B + P.real {omega | c ≤ F omega} :=
    hmeasure.trans (measureReal_union_le (μ := P) B {omega | c ≤ F omega})
  have hb := joint_badGrid_probability hN hβ hC g hg hgrad u x hu hx (by positivity) H T hT hshort
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (.of_forall fun omega => finiteDiscountedMass_nonneg κ hκ0 X θ (H + T) omega) hi c
  have hp := mul_le_mul_of_nonneg_left hprob hc0
  have hbp := mul_le_mul_of_nonneg_left hb hc0
  change c * (P.real A - _) ≤ ∫ omega,F omega ∂P
  change c * P.real B ≤ _ at hbp
  nlinarith only [hp,hbp,hm]

theorem physical_hitting_discounted_mass (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) {α : ℝ} (hα : 0 < α)
    (κ : State N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1)
    (hκcap : ∀ y,α / 3 ≤ |overlapValue u y| → 1 ≤ κ y)
    {θ : ℝ} (hθ : 0 ≤ θ) (H T : ℝ≥0) (hT : 0 < T)
    (hshort : 4 * (1 + β * C) * (T : ℝ) ≤ α / 12) :
    exposureFactor θ H T *
      ((VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤ |overlapValue u (process β g hg x t omega)|} -
        (gridSize H T : ℝ) * 2 * Real.exp (-(N : ℝ) * (α / 12) ^ 2 / (16 * (T : ℝ)))) ≤
      ∫ omega,finiteDiscountedMass κ (jointPhysicalProcess β g hg x) θ (H + T) omega ∂VectorBrownian.law N := by
  have he : {omega | ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤ |overlapValue u (process β g hg x t omega)|} =ᵐ[VectorBrownian.law N]
      {omega | ∃ t : ℝ≥0,t ≤ H ∧ α / 2 ≤ |overlapValue u (jointPhysicalProcess β g hg x t omega)|} := by
    filter_upwards [jointPhysicalProcess_ae_actual β g hg x] with omega homega
    simp_rw [homega]
  rw [measureReal_congr he]
  exact joint_physical_hitting_discounted_mass hN hβ hC g hg hgrad u x hu hx hα κ hκ hκ0 hκ1 hκcap hθ H T hT hshort

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
