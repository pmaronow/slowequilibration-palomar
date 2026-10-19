module

public import SphericalAging.SphereEntropyDissipation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-! Actual finite-time Fisher budget obtained by integration of the proved
spherical forward-PDE entropy dissipation, together with genuine entropy positivity. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereEntropyBudget

open MeasureTheory Set Filter
open scoped Topology BigOperators
open FiniteModel SphereInitialLaw SphereGibbsEntropy SphericalIntegrationByParts SphereEntropyDissipation

/-- Genuine compact-sphere continuity of a parameter integral. -/
theorem continuous_sphere_parameter_integral {N : ℕ} (hN : 0<N) {F : ℝ → Vector N → ℝ}
    (hF : Continuous (Function.uncurry F)) :
    Continuous (fun t => ∫ x : Vector N,F t x ∂sphereLaw N) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (t₀-1) (t₀+1))).prod
      (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).bddAbove_image hF.norm.continuousOn
  have hs : Icc (t₀-1) (t₀+1) ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => K)
  · exact Eventually.of_forall fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hs] with t ht
    filter_upwards [sphereLaw_norm_ae hN] with x hx
    exact hK ⟨(t,x),⟨ht,by simp only [Metric.mem_closedBall,dist_zero_right,hx,le_refl]⟩,rfl⟩
  · exact integrable_const K
  · exact ae_of_all _ fun x =>
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- Genuine differentiation of a sphere parameter integral from actual pointwise derivatives. -/
theorem hasDerivAt_sphere_parameter_integral {N : ℕ} (hN : 0<N)
    {F F' : ℝ → Vector N → ℝ} (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ t x,HasDerivAt (fun s => F s x) (F' t x) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ x : Vector N,F t x ∂sphereLaw N)
      (∫ x : Vector N,F' t₀ x ∂sphereLaw N) t₀ := by
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (t₀-1) (t₀+1))).prod
      (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).bddAbove_image hF'.norm.continuousOn
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereLaw N) (F := F) (F' := F') (bound := fun _ => K)
    (x₀ := t₀) (s := Icc (t₀-1) (t₀+1))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    (continuous_sphere_integrable hN (hF.comp (continuous_const.prodMk continuous_id)))
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (by
      filter_upwards [sphereLaw_norm_ae hN] with x hx t ht
      exact hK ⟨(t,x),⟨ht,by simp only [Metric.mem_closedBall,dist_zero_right,hx,le_refl]⟩,rfl⟩)
    (integrable_const K) (ae_of_all _ fun x t _ => hderiv t x)).2

/-- Probability mass one is derived from the actual forward PDE and the uniform initial density. -/
theorem density_mass_one {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (hinit : ∀ x,ρ 0 x=1) {T : ℝ} (hT : 0≤T)
    (hPDE : ∀ t ∈ Icc 0 T,∀ x,ρdot t x=forwardDensitySlope κ β J A (ρ t) x) :
    (∫ x : Vector N,ρ T x ∂sphereLaw N)=1 := by
  have hd t (ht : t ∈ Icc 0 T) : HasDerivWithinAt
      (fun s => ∫ x : Vector N,ρ s x ∂sphereLaw N) 0 (Icc 0 T) t := by
    have hh := hasDerivAt_sphere_parameter_integral hN hρ.continuous hdot hderiv t
    have hPf : ρdot t=forwardDensitySlope κ β J A (ρ t) := funext (hPDE t ht)
    have hsp : ContDiff ℝ 2 (ρ t) := by
      simpa only [Function.comp_def,Function.uncurry,id_eq] using
        hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (t,x)))
    rw [hPf,forwardDensitySlope_integral_zero hN κ β J A hA hsp] at hh
    exact hh.hasDerivWithinAt
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (fun t ht => by simp) (convex_Icc 0 T) (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)
    (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩)
  simp only [zero_mul] at he
  have heq := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))
  rw [heq,show ρ 0=(fun _ : Vector N => 1) from funext hinit]
  simp

/-- Actual joint spatial derivative regularity follows from joint C2 density regularity. -/
theorem joint_lieDerivative_continuous {N : ℕ} (A : Operator N)
    {ρ : ℝ → Vector N → ℝ} (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) :
    Continuous (fun z : ℝ × Vector N => lieDerivative A (ρ z.1) z.2) := by
  have hf : ContDiff ℝ 2 (Function.uncurry (fun z : ℝ × Vector N => fun x : Vector N => ρ z.1 x)) :=
    hρ.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ 1 (fun z : ℝ × Vector N => fderiv ℝ (ρ z.1) z.2) :=
    hf.fderiv contDiff_snd (by norm_num)
  exact (hd.clm_apply (A.contDiff.comp contDiff_snd)).continuous

/-- True continuity of the constructed Fisher information, including integration over the sphere. -/
theorem rotationFisher_continuous {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {ρ : ℝ → Vector N → ℝ} (hρ : ContDiff ℝ 2 (Function.uncurry ρ))
    (hpos : ∀ t x,0<ρ t x) :
    Continuous (fun t => rotationFisher κ β J A (ρ t)) := by
  classical
  unfold rotationFisher
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply continuous_sphere_parameter_integral hN
  have hflux : Continuous (fun z : ℝ × Vector N => rotationFlux β J (A i) (ρ z.1) z.2) :=
    (joint_lieDerivative_continuous (A i) hρ).sub
      ((continuous_const.mul hρ.continuous).mul
        ((lieDerivative_continuous (A i) ((Hamiltonian_contDiff J).of_le (by simp))).comp continuous_snd))
  exact (hflux.pow 2).div hρ.continuous (fun z => (hpos z.1 z.2).ne')

/-- Full finite-time entropy/Fisher equality from the actual forward density PDE. -/
theorem integrated_entropy_dissipation {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x)
    (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {T : ℝ} (hT : 0≤T)
    (hPDE : ∀ t ∈ Icc 0 T,∀ x,ρdot t x=forwardDensitySlope κ β J A (ρ t) x) :
    (∫ t in 0..T,rotationFisher κ β J A (ρ t))=
      relativeEntropy β J (ρ 0)-relativeEntropy β J (ρ T) := by
  have hF := rotationFisher_continuous hN κ β J A hρ hpos
  have hd t (ht : t ∈ uIcc 0 T) : HasDerivAt (fun s => relativeEntropy β J (ρ s))
      (-rotationFisher κ β J A (ρ t)) t := by
    have htt : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    exact entropy_dissipation_hasDerivAt hN κ β J A hA hρ.continuous hdot hpos hderiv t
      (hρ.comp (contDiff_const.prodMk contDiff_id)) (hPDE t htt)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hF.neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at hh
  linarith

/-- The actual initial entropy bounds the time-integrated Fisher information. -/
theorem finite_fisher_budget {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (hp : 1≤p) (κ : ℝ) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) (A : ι → Operator N) (hA : ∀ i,star (A i)=-A i)
    {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x) (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (hinit : ∀ x,ρ 0 x=1) {T : ℝ} (hT : 0≤T)
    (hPDE : ∀ t ∈ Icc 0 T,∀ x,ρdot t x=forwardDensitySlope κ β J A (ρ t) x)
    :
    (∫ t in 0..T,rotationFisher κ β J A (ρ t)) ≤ initialEntropy N p β J := by
  rw [integrated_entropy_dissipation hN κ β J A hA hρ hdot hpos hderiv hT hPDE,
    show ρ 0=(fun _ : Vector N => 1) from funext hinit,relativeEntropy_uniform hN hp hβ J]
  have hmass := density_mass_one hN κ β J A hA hρ hdot hderiv hinit hT hPDE
  have he := relativeEntropy_nonnegative hN hp hβ J
    (hρ.continuous.comp (continuous_const.prodMk continuous_id)) (hpos T) hmass
  change 0 ≤ relativeEntropy β J (ρ T) at he
  linarith

/-- The genuine Fisher information is integrable on the entire positive time ray,
and its total mass is bounded by the actual initial relative Gibbs entropy. -/
theorem infinite_fisher_budget {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (hp : 1≤p) {κ β : ℝ} (hκ : 0≤κ) (hβ : 0≤β)
    (J : Disorder N p) (A : ι → Operator N) (hA : ∀ i,star (A i)=-A i)
    {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x) (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,ρdot t x=forwardDensitySlope κ β J A (ρ t) x) :
    IntegrableOn (fun t => rotationFisher κ β J A (ρ t)) (Ioi 0) ∧
      (∫ t in Ioi 0,rotationFisher κ β J A (ρ t)) ≤ initialEntropy N p β J := by
  let F (t : ℝ) := rotationFisher κ β J A (ρ t)
  have hc : Continuous F := rotationFisher_continuous hN κ β J A hρ hpos
  have hpF : ∀ t,0≤F t := fun t => rotationFisher_nonnegative hκ β J A (hpos t)
  have hb : ∀ T,0≤T → (∫ t in 0..T,F t) ≤ initialEntropy N p β J := by
    intro T hT
    exact finite_fisher_budget hN hp κ hβ J A hA hρ hdot hpos hderiv hinit hT
      (fun t ht => hPDE t ht.1)
  have hi : IntegrableOn F (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (initialEntropy N p β J) (0 : ℝ)
      (b := fun T : ℝ => T) (l := atTop)
      (fun T => (hc.intervalIntegrable 0 T).1) tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpF _)] using hb T hT
  refine ⟨hi,?_⟩
  have hh := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  apply le_of_tendsto hh
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact hb T hT

end SphericalAging.SphereEntropyBudget
