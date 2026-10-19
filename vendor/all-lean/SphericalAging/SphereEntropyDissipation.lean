module

public import SphericalAging.SphericalIntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

/-! Genuine spherical entropy dissipation from the forward density equation.
Rotation integration by parts is proved in the imported module.  The forward
operator is an actual sum of spherical rotation divergences, not an assumed
entropy or Fisher identity. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereEntropyDissipation

open MeasureTheory Set Filter
open scoped Topology BigOperators
open FiniteModel SphereInitialLaw SphereGibbsEntropy SphericalIntegrationByParts

/-- The actual logarithmic density ratio against the constructed Gibbs density. -/
@[expose] def relativeLog {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) (x : Vector N) : ℝ :=
  Real.log (ρ x)-β*Hamiltonian N p J x+Real.log (partitionFunction N p β J)

@[expose] def relativeEntropy {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) : ℝ :=
  ∫ x : Vector N,ρ x*relativeLog β J ρ x ∂sphereLaw N

/-- The genuine forward probability flux in a rotation direction. -/
@[expose] def rotationFlux {N p : ℕ} (β : ℝ) (J : Disorder N p) (A : Operator N)
    (ρ : Vector N → ℝ) (x : Vector N) : ℝ :=
  lieDerivative A ρ x-β*ρ x*lieDerivative A (Hamiltonian N p J) x

/-- A finite-family spherical forward operator, later instantiated by the actual
coordinate rotations with coefficient `1 / (2 * N)`. -/
@[expose] def forwardDensitySlope {N p : ℕ} {ι : Type*} [Fintype ι] (κ β : ℝ) (J : Disorder N p)
    (A : ι → Operator N) (ρ : Vector N → ℝ) (x : Vector N) : ℝ :=
  κ*∑ i,lieDerivative (A i) (rotationFlux β J (A i) ρ) x

/-- Its exact rotation form of the relative Fisher information. -/
@[expose] def rotationFisher {N p : ℕ} {ι : Type*} [Fintype ι] (κ β : ℝ) (J : Disorder N p)
    (A : ι → Operator N) (ρ : Vector N → ℝ) : ℝ :=
  κ*∑ i,∫ x : Vector N,(rotationFlux β J (A i) ρ x)^2/ρ x ∂sphereLaw N

theorem lieDerivative_contDiff {N : ℕ} (A : Operator N) {ρ : Vector N → ℝ}
    (hρ : ContDiff ℝ 2 ρ) : ContDiff ℝ 1 (lieDerivative A ρ) := by
  unfold lieDerivative
  exact (hρ.fderiv_right (by norm_num)).clm_apply A.contDiff

theorem rotationFlux_contDiff {N p : ℕ} (β : ℝ) (J : Disorder N p) (A : Operator N)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 1 (rotationFlux β J A ρ) := by
  exact (lieDerivative_contDiff A hρ).sub
    (((contDiff_const.mul (hρ.of_le (by norm_num))).mul
      (lieDerivative_contDiff A ((Hamiltonian_contDiff J).of_le (by simp)))))

theorem relativeLog_contDiff {N p : ℕ} (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x,0<ρ x) :
    ContDiff ℝ 1 (relativeLog β J ρ) :=
  ((hρ.log (fun x => (hpos x).ne')).sub
    (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const

/-- The logarithmic score is the genuine flux divided by the density. -/
theorem relativeLog_lieDerivative {N p : ℕ} (β : ℝ) (J : Disorder N p) (A : Operator N)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x,0<ρ x) (x : Vector N) :
    lieDerivative A (relativeLog β J ρ) x=rotationFlux β J A ρ x/ρ x := by
  have hr := flow_function_hasDerivAt A hρ (0 : ℝ) x
  simp only [operatorFlow_zero] at hr
  have hH := flow_function_hasDerivAt A ((Hamiltonian_contDiff J).of_le (by simp)) (0 : ℝ) x
  simp only [operatorFlow_zero] at hH
  have hh := (((hr.log (by simpa only [operatorFlow_zero] using (hpos x).ne')).sub (hH.const_mul β)).add_const
    (Real.log (partitionFunction N p β J)))
  have hh' := flow_function_hasDerivAt A (relativeLog_contDiff β J hρ hpos) (0 : ℝ) x
  simp only [operatorFlow_zero] at hh'
  have he := hh'.unique hh
  simp only [operatorFlow_zero] at he
  rw [he]
  unfold rotationFlux
  field_simp [(hpos x).ne']

/-- The actual forward operator conserves mass by rotation invariance. -/
theorem forwardDensitySlope_integral_zero {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) :
    (∫ x : Vector N,forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=0 := by
  unfold forwardDensitySlope
  rw [integral_const_mul,integral_finsetSum]
  · simp_rw [integral_lieDerivative_eq_zero hN _ (hA _) (rotationFlux_contDiff β J _ hρ)]
    simp
  · intro i _
    exact continuous_sphere_integrable hN
      (lieDerivative_continuous _ (rotationFlux_contDiff β J _ hρ))

/-- Actual entropy production against the forward density slope equals minus the
constructed Fisher information; this is derived from spherical integration by parts. -/
theorem forward_entropy_production {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ : Vector N → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) :
    (∫ x : Vector N,relativeLog β J ρ x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=
      -rotationFisher κ β J A ρ := by
  classical
  have hlog := relativeLog_contDiff β J (hρ.of_le (by norm_num)) hpos
  have hint i : Integrable (fun x : Vector N => relativeLog β J ρ x*
      lieDerivative (A i) (rotationFlux β J (A i) ρ) x) (sphereLaw N) :=
    continuous_sphere_integrable hN (hlog.continuous.mul
      (lieDerivative_continuous _ (rotationFlux_contDiff β J _ hρ)))
  have heq i : (∫ x : Vector N,relativeLog β J ρ x*
      lieDerivative (A i) (rotationFlux β J (A i) ρ) x ∂sphereLaw N)=
      -(∫ x : Vector N,(rotationFlux β J (A i) ρ x)^2/ρ x ∂sphereLaw N) := by
    rw [sphere_lie_integration_by_parts hN _ (hA i) hlog (rotationFlux_contDiff β J _ hρ)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [relativeLog_lieDerivative β J _ (hρ.of_le (by norm_num)) hpos x]
      ring
  have hfun : (fun x : Vector N => relativeLog β J ρ x*forwardDensitySlope κ β J A ρ x)=
      (fun x => κ*∑ i,relativeLog β J ρ x*
        lieDerivative (A i) (rotationFlux β J (A i) ρ) x) := by
    funext x
    unfold forwardDensitySlope
    rw [← Finset.mul_sum]
    ring
  rw [hfun,integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hint i)]
  simp_rw [heq]
  rw [Finset.sum_neg_distrib]
  unfold rotationFisher
  ring

theorem rotationFisher_nonnegative {N p : ℕ} {ι : Type*} [Fintype ι]
    {κ : ℝ} (hκ : 0≤κ) (β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {ρ : Vector N → ℝ} (hpos : ∀ x,0<ρ x) : 0≤rotationFisher κ β J A ρ := by
  unfold rotationFisher
  apply mul_nonneg hκ
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => div_nonneg (sq_nonneg _) (hpos x).le

/-- The defined entropy is exactly the actual density ratio against Gibbs. -/
theorem relativeLog_eq_log_ratio {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) {ρ : Vector N → ℝ}
    (hpos : ∀ x,0<ρ x) (x : Vector N) :
    relativeLog β J ρ x=Real.log (ρ x/gibbsDensity N p β J x) := by
  rw [Real.log_div (hpos x).ne' (gibbsDensity_positive hN hp hβ J x).ne']
  have hh := negative_log_gibbsDensity hN hp hβ J x
  unfold relativeLog
  linarith

/-- Positivity of the actual relative entropy follows from both genuine density masses. -/
theorem relativeEntropy_nonnegative {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) {ρ : Vector N → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ x,0<ρ x)
    (hmass : (∫ x : Vector N,ρ x ∂sphereLaw N)=1) : 0 ≤ relativeEntropy β J ρ := by
  have hlog : Continuous (relativeLog β J ρ) :=
    ((hρ.log (fun x => (hpos x).ne')).sub
      (continuous_const.mul ((Hamiltonian_contDiff J).continuous))).add continuous_const
  have hlo (x : Vector N) : ρ x-gibbsDensity N p β J x ≤ ρ x*relativeLog β J ρ x := by
    have hgp := gibbsDensity_positive hN hp hβ J x
    have hh := Real.log_le_sub_one_of_pos (div_pos hgp (hpos x))
    rw [Real.log_div hgp.ne' (hpos x).ne'] at hh
    have he := negative_log_gibbsDensity hN hp hβ J x
    have hmul := mul_le_mul_of_nonneg_left hh (hpos x).le
    have hcancel : ρ x*(gibbsDensity N p β J x/ρ x-1)=gibbsDensity N p β J x-ρ x := by
      field_simp [(hpos x).ne']
    rw [hcancel] at hmul
    have hRel : relativeLog β J ρ x=Real.log (ρ x)-Real.log (gibbsDensity N p β J x) := by
      unfold relativeLog
      linarith
    rw [hRel]
    linarith only [hmul]
  have hh := integral_mono
    ((continuous_sphere_integrable hN hρ).sub (gibbsDensity_integrable hN hp β J))
    (continuous_sphere_integrable hN (hρ.mul hlog)) hlo
  change (∫ x : Vector N,ρ x-gibbsDensity N p β J x ∂sphereLaw N) ≤ relativeEntropy β J ρ at hh
  rw [integral_sub (continuous_sphere_integrable hN hρ) (gibbsDensity_integrable hN hp β J),
    hmass,gibbsDensity_normalized hN hp hβ J,sub_self] at hh
  exact hh

/-- The uniform initial density has exactly the previously calculated Gibbs entropy. -/
theorem relativeEntropy_uniform {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) :
    relativeEntropy β J (fun _ : Vector N => 1)=initialEntropy N p β J := by
  unfold relativeEntropy initialEntropy
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [relativeLog,Real.log_one,one_mul,zero_sub]
    rw [negative_log_gibbsDensity hN hp hβ J]
    ring

/-- Differentiation of the actual entropy integral, justified by compact domination.
The time derivative of the density is the supplied genuine pointwise derivative. -/
theorem relativeEntropy_hasDerivAt {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x)
    (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t) (t₀ : ℝ) :
    HasDerivAt (fun t => relativeEntropy β J (ρ t))
      (∫ x : Vector N,ρdot t₀ x*(1+relativeLog β J (ρ t₀) x) ∂sphereLaw N) t₀ := by
  let F (t : ℝ) (x : Vector N) := ρ t x*relativeLog β J (ρ t) x
  let F' (t : ℝ) (x : Vector N) := ρdot t x*(1+relativeLog β J (ρ t) x)
  have hlog : Continuous (fun z : ℝ × Vector N => relativeLog β J (ρ z.1) z.2) := by
    unfold relativeLog
    exact ((hρ.log (fun z => (hpos z.1 z.2).ne')).sub
      (continuous_const.mul ((Hamiltonian_contDiff J).continuous.comp continuous_snd))).add continuous_const
  have hFc : Continuous (Function.uncurry F) := hρ.mul hlog
  have hF'c : Continuous (Function.uncurry F') := hdot.mul (continuous_const.add hlog)
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (t₀-1) (t₀+1))).prod
      (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).bddAbove_image hF'c.norm.continuousOn
  have hD (t : ℝ) (x : Vector N) : HasDerivAt (fun s => F s x) (F' t x) t := by
    have hh := (hderiv t x).mul ((((hderiv t x).log (hpos t x).ne').sub_const
      (β*Hamiltonian N p J x)).add_const (Real.log (partitionFunction N p β J)))
    convert hh using 1
    · rfl
    · dsimp only [F',relativeLog]
      field_simp [(hpos t x).ne']
      ring
  have hpointc (t : ℝ) : Continuous (F t) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hpointD (t : ℝ) : Continuous (F' t) :=
    hF'c.comp (continuous_const.prodMk continuous_id)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereLaw N) (F := F) (F' := F') (bound := fun _ => K)
    (x₀ := t₀) (s := Icc (t₀-1) (t₀+1))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun t => (hpointc t).aestronglyMeasurable))
    (continuous_sphere_integrable hN (hpointc t₀))
    (hpointD t₀).aestronglyMeasurable
    (by
      filter_upwards [sphereLaw_norm_ae hN] with x hx t ht
      exact hK ⟨(t,x),⟨ht,by simp only [Metric.mem_closedBall,dist_zero_right,hx,le_refl]⟩,rfl⟩)
    (integrable_const K)
    (ae_of_all _ fun x t _ => hD t x)
  exact hh.2

/-- Actual entropy dissipation is derived from the forward PDE at the given time;
no entropy derivative or Fisher identity is among the hypotheses. -/
theorem entropy_dissipation_hasDerivAt {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x)
    (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (t₀ : ℝ) (hspace : ContDiff ℝ 2 (ρ t₀))
    (hPDE : ∀ x,ρdot t₀ x=forwardDensitySlope κ β J A (ρ t₀) x) :
    HasDerivAt (fun t => relativeEntropy β J (ρ t)) (-rotationFisher κ β J A (ρ t₀)) t₀ := by
  have hh := relativeEntropy_hasDerivAt hN β J hρ hdot hpos hderiv t₀
  have hpc : Continuous (ρdot t₀) := hdot.comp (continuous_const.prodMk continuous_id)
  have hlog := (relativeLog_contDiff β J (hspace.of_le (by norm_num)) (hpos t₀)).continuous
  have heq : (∫ x : Vector N,ρdot t₀ x*(1+relativeLog β J (ρ t₀) x) ∂sphereLaw N)=
      -rotationFisher κ β J A (ρ t₀) := by
    have hfun : (fun x : Vector N => ρdot t₀ x*(1+relativeLog β J (ρ t₀) x))=
        (fun x => ρdot t₀ x+relativeLog β J (ρ t₀) x*ρdot t₀ x) := by funext x;ring
    rw [hfun,integral_add (f := ρdot t₀) (g := fun x => relativeLog β J (ρ t₀) x*ρdot t₀ x)
      (continuous_sphere_integrable hN hpc)
      (continuous_sphere_integrable hN (hlog.mul hpc))]
    have hPDEfun : ρdot t₀=forwardDensitySlope κ β J A (ρ t₀) := funext hPDE
    rw [hPDEfun,forwardDensitySlope_integral_zero hN κ β J A hA hspace,
      forward_entropy_production hN κ β J A hA hspace (hpos t₀),zero_add]
  rwa [heq] at hh

end SphericalAging.SphereEntropyDissipation
