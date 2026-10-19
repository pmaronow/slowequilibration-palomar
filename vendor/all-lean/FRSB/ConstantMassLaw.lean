module
public import FRSB.ConstantMassItoEndpoint
public import FRSB.ConstantMassBackwardKernel
public import FRSB.ConditionalKernelLaw

@[expose] public section

/-! The actual conditional h-transform transition law on every constant-CDF interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace FRSB

def parisiConstantMassKernel (β : ℝ) (μ : ParisiMeasure) (a T : ℝ≥0) (m : ℝ) :
    Kernel ℝ ℝ :=
  constantMassKernel m (β^2*(T:ℝ)).toNNReal
    (fun y => parisiPotential β μ ((a:ℝ)+T,y))

theorem isMarkovKernel_parisiConstantMassKernel (β : ℝ) (μ : ParisiMeasure)
    (a T : ℝ≥0) (haT : (a:ℝ)+T ≤ 1) (m : ℝ) :
    IsMarkovKernel (parisiConstantMassKernel β μ a T m) :=
  isMarkovKernel_constantMassKernel m _ _
    ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id))
    (parisiPotential_hasLinearGrowth β μ _ ⟨by positivity,haT⟩)

theorem stronglyAdapted_selectedParisiState (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    StronglyAdapted canonicalBrownianFiltration (selectedParisiItoState β h hβ μ) :=
  stronglyAdapted_canonicalParisiItoState β h μ (fun t x => parisiGradient β μ (t,x))
    (continuous_parisiGradient β μ) (fun t x => norm_parisiGradient_le_one β μ (t,x))
    (lipschitzWith_parisiGradient β hβ μ)

theorem measurable_selectedParisiState_time (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ≥0) : Measurable (selectedParisiItoState β h hβ μ t) :=
  ((stronglyAdapted_selectedParisiState β h hβ μ t).mono
    (canonicalBrownianFiltration.le t)).measurable

theorem selectedParisiState_constantMass_restricted_transitionLaw
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a:ℝ)+T ≤ 1) (m : ℝ)
    (hcdf : ∀ s ∈ Ico (a:ℝ) ((a:ℝ)+T), parisiCDF μ s = m)
    (E : Set BrownianSample) (hE : MeasurableSet[canonicalBrownianFiltration a] E) :
    (canonicalBrownianMeasure.restrict E).map (selectedParisiItoState β h hβ μ (a+T)) =
      parisiConstantMassKernel β μ a T m ∘ₘ
        (canonicalBrownianMeasure.restrict E).map (selectedParisiItoState β h hβ μ a) := by
  letI := isMarkovKernel_parisiConstantMassKernel β μ a T haT m
  apply restricted_transitionLaw_of_weighted_fourier (canonicalBrownianFiltration a)
    canonicalBrownianMeasure (canonicalBrownianFiltration.le a)
    (selectedParisiItoState β h hβ μ a) (selectedParisiItoState β h hβ μ (a+T))
    (measurable_selectedParisiState_time β h hβ μ a)
    (measurable_selectedParisiState_time β h hβ μ (a+T))
    (parisiConstantMassKernel β μ a T m) ?_ ?_ E hE
  · intro ξ Z hZ hZb
    have he := selectedParisiItoState_constantMass_weighted_cos β h hβ μ a T hT haT m ξ
      hcdf Z hZ 1 (by simpa using hZb)
    rw [he]
    apply integral_congr_ae
    exact .of_forall fun sample => by
      dsimp only
      apply congrArg (fun v : ℝ => Z sample * v)
      exact parisiBackwardQuotient_eq_kernel_integral β μ _ m _ _
        ⟨by positivity,haT⟩ (mul_nonneg (sq_nonneg β) T.coe_nonneg)
        (fun y => Real.cos (ξ*y)) (by fun_prop)
  · intro ξ Z hZ hZb
    have he := selectedParisiItoState_constantMass_weighted_sin β h hβ μ a T hT haT m ξ
      hcdf Z hZ 1 (by simpa using hZb)
    rw [he]
    apply integral_congr_ae
    exact .of_forall fun sample => by
      dsimp only
      apply congrArg (fun v : ℝ => Z sample * v)
      exact parisiBackwardQuotient_eq_kernel_integral β μ _ m _ _
        ⟨by positivity,haT⟩ (mul_nonneg (sq_nonneg β) T.coe_nonneg)
        (fun y => Real.sin (ξ*y)) (by fun_prop)

theorem condExp_selectedParisiState_constantMass
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a:ℝ)+T ≤ 1) (m : ℝ)
    (hcdf : ∀ s ∈ Ico (a:ℝ) ((a:ℝ)+T), parisiCDF μ s = m)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    canonicalBrownianMeasure[(fun sample => ψ (selectedParisiItoState β h hβ μ (a+T) sample)) |
      canonicalBrownianFiltration a] =ᵐ[canonicalBrownianMeasure]
      fun sample => ∫ y, ψ y ∂parisiConstantMassKernel β μ a T m
        (selectedParisiItoState β h hβ μ a sample) := by
  letI := isMarkovKernel_parisiConstantMassKernel β μ a T haT m
  exact condExp_kernel_of_restricted_transitionLaw (canonicalBrownianFiltration a)
    canonicalBrownianMeasure (canonicalBrownianFiltration.le a)
    (selectedParisiItoState β h hβ μ a) (selectedParisiItoState β h hβ μ (a+T))
    (stronglyAdapted_selectedParisiState β h hβ μ a)
    (measurable_selectedParisiState_time β h hβ μ (a+T))
    (parisiConstantMassKernel β μ a T m)
    (selectedParisiState_constantMass_restricted_transitionLaw β h hβ μ a T hT haT m hcdf)
    ψ hψ C hC

theorem selectedParisiState_constantMass_weighted_borel
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a:ℝ)+T ≤ 1) (m : ℝ)
    (hcdf : ∀ s ∈ Ico (a:ℝ) ((a:ℝ)+T), parisiCDF μ s = m)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (Cψ : ℝ) (hψb : ∀ x, ‖ψ x‖ ≤ Cψ)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (CZ : ℝ) (hZb : ∀ sample, ‖Z sample‖ ≤ CZ) :
    (∫ sample, Z sample * ψ (selectedParisiItoState β h hβ μ (a+T) sample)
      ∂canonicalBrownianMeasure) =
      ∫ sample, Z sample * (∫ y, ψ y ∂parisiConstantMassKernel β μ a T m
        (selectedParisiItoState β h hβ μ a sample)) ∂canonicalBrownianMeasure := by
  have hi : Integrable (fun sample => ψ (selectedParisiItoState β h hβ μ (a+T) sample))
      canonicalBrownianMeasure :=
    (integrable_const Cψ).mono'
      (hψ.comp (measurable_selectedParisiState_time β h hβ μ (a+T))).aestronglyMeasurable
      (.of_forall fun sample => hψb _)
  exact weighted_kernelObservable_of_condExp (canonicalBrownianFiltration a)
    canonicalBrownianMeasure (canonicalBrownianFiltration.le a) _ _ hi
    (condExp_selectedParisiState_constantMass β h hβ μ a T hT haT m hcdf ψ hψ Cψ hψb)
    Z hZ CZ hZb

/-- The kernel's density uses the actual potentials at both physical endpoints. -/
theorem parisiConstantMassKernel_apply_actual
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a:ℝ)+T ≤ 1) (m : ℝ)
    (hcdf : ∀ s ∈ Ico (a:ℝ) ((a:ℝ)+T), parisiCDF μ s = m) (x : ℝ) :
    parisiConstantMassKernel β μ a T m x =
      (gaussianReal x (β^2*(T:ℝ)).toNNReal).withDensity
        (fun y => ENNReal.ofReal (Real.exp (m *
          (parisiPotential β μ ((a:ℝ)+T,y) - parisiPotential β μ (a,x))))) := by
  unfold parisiConstantMassKernel
  have hAc : Continuous (fun y : ℝ => parisiPotential β μ ((a:ℝ)+T,y)) := by
    convert! (continuous_parisiPotential β μ).comp
      (continuous_const.prodMk continuous_id) using 1
  rw [constantMassKernel_apply m _ (fun y => parisiPotential β μ ((a:ℝ)+T,y)) hAc
    (parisiPotential_hasLinearGrowth β μ _ ⟨by positivity,haT⟩)]
  have he := parisiPotential_coleHopf_on_constantCDF β hβ μ a.coe_nonneg
    (lt_add_of_pos_right (a:ℝ) (NNReal.coe_pos.mpr hT)) haT hcdf x
  rw [show (a:ℝ)+T-a = (T:ℝ) by ring] at he
  simp only [constantMassTransition, constantMassWeight, ← he]

end FRSB
