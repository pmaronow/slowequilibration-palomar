module

public import SphericalAging.SphereGeneratorRegularity

public section

/-! The actual nonequilibrium FDT derivative, from the true forward density PDE
and the genuine backward generator equation for a conditional-mean observable. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFiniteFDT

open MeasureTheory Set Filter
open scoped Topology BigOperators
open FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation SphereEntropyBudget
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereForwardAdjoint SphereFDTAlgebra
open SphereGeneratorRegularity

@[expose] def correlationPairing {N : ℕ} (ρ : ℝ → Vector N → ℝ) (φ : Vector N → ℝ)
    (m : ℝ → Vector N → ℝ) (t s : ℝ) : ℝ :=
  ∫ x : Vector N,ρ s x*φ x*m (t-s) x ∂sphereLaw N

/-- The source FDT derivative for one observable. The only equations assumed are
actual forward/backward PDEs; the FDT identity is obtained by genuine calculus. -/
theorem single_component_fdt_hasDerivAt {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ ρdot m : ℝ → Vector N → ℝ} {φ : Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hm : ContDiff ℝ 2 (Function.uncurry m)) (hφ : ContDiff ℝ 2 φ)
    (hback : ∀ v,0<v → ∀ x,HasDerivAt (fun w => m w x) (rotationGenerator κ β J A (m v) x) v)
    {t s : ℝ} (hst : s<t) (hpos : ∀ x,0<ρ s x)
    (hPDE : ∀ x,ρdot s x=forwardDensitySlope κ β J A (ρ s) x) :
    HasDerivAt (fun v => correlationPairing ρ φ m t v)
      ((∫ x : Vector N,ρ s x*rotationGamma κ A φ (m (t-s)) x ∂sphereLaw N)-
        (∫ x : Vector N,ρ s x*m (t-s) x*rotationGamma κ A (relativeLog β J (ρ s)) φ x
          ∂sphereLaw N)) s := by
  let δ := (t-s)/2
  have hδ : 0<δ := by dsimp only [δ];linarith
  let F (v : ℝ) (x : Vector N) := ρ v x*φ x*m (t-v) x
  let F' (v : ℝ) (x : Vector N) :=
    ρdot v x*φ x*m (t-v) x-ρ v x*φ x*rotationGenerator κ β J A (m (t-v)) x
  have hcomp : Continuous (fun z : ℝ × Vector N => (t-z.1,z.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hmc := hm.continuous.comp hcomp
  have hLc := (joint_rotationGenerator_continuous κ β J A hm).comp hcomp
  have hφc := hφ.continuous.comp (continuous_snd : Continuous (fun z : ℝ × Vector N => z.2))
  have hFc : Continuous (Function.uncurry F) := (hρ.continuous.mul hφc).mul hmc
  have hF'c : Continuous (Function.uncurry F') :=
    ((hdot.mul hφc).mul hmc).sub ((hρ.continuous.mul hφc).mul hLc)
  have hD v (hv : v ∈ Icc (s-δ) (s+δ)) (x : Vector N) :
      HasDerivAt (fun w => F w x) (F' v x) v := by
    have hlag : 0<t-v := by dsimp only [δ] at hv;linarith [hv.2]
    have hd := (hback (t-v) hlag x).comp v ((hasDerivAt_const v t).sub (hasDerivAt_id v))
    have hh := ((hderiv v x).mul_const (φ x)).mul hd
    convert hh using 1
    · rfl
    · dsimp only [F',Function.comp_def]
      ring
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (s-δ) (s+δ))).prod
      (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).bddAbove_image hF'c.norm.continuousOn
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereLaw N) (F := F) (F' := F') (bound := fun _ => K)
    (x₀ := s) (s := Icc (s-δ) (s+δ))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun v => (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    (continuous_sphere_integrable hN (hFc.comp (continuous_const.prodMk continuous_id)))
    (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (by
      filter_upwards [sphereLaw_norm_ae hN] with x hx v hv
      exact hK ⟨(v,x),⟨hv,by simp only [Metric.mem_closedBall,dist_zero_right,hx,le_refl]⟩,rfl⟩)
    (integrable_const K) (ae_of_all _ fun x v hv => hD v hv x)
  have hρs : ContDiff ℝ 2 (ρ s) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (s,x)))
  have hms : ContDiff ℝ 2 (m (t-s)) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hm.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (t-s,x)))
  have hφm := hφ.mul hms
  have hfirst : (∫ x : Vector N,ρdot s x*φ x*m (t-s) x ∂sphereLaw N)=
      (∫ x : Vector N,ρ s x*rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x ∂sphereLaw N) := by
    rw [← forward_density_adjoint hN κ β J A hA hρs hpos hφm]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp only;rw [hPDE x];ring
  have hi₀ := continuous_sphere_integrable hN
    (((hdot.comp (continuous_const.prodMk continuous_id : Continuous (fun x : Vector N => (s,x)))).mul
      hφ.continuous).mul hms.continuous)
  have hi₁ := continuous_sphere_integrable hN
    ((hρs.continuous.mul hφ.continuous).mul (rotationGenerator_continuous κ β J A hms))
  have hi₂ := continuous_sphere_integrable hN
    (hρs.continuous.mul (rotationGenerator_continuous κ β J A hφm))
  have he : (∫ x : Vector N,F' s x ∂sphereLaw N)=
      ((∫ x : Vector N,ρ s x*rotationGamma κ A φ (m (t-s)) x ∂sphereLaw N)-
        (∫ x : Vector N,ρ s x*m (t-s) x*rotationGamma κ A (relativeLog β J (ρ s)) φ x
          ∂sphereLaw N)) := by
    dsimp only [F']
    rw [integral_sub (f := fun x : Vector N => ρdot s x*φ x*m (t-s) x)
      (g := fun x => ρ s x*φ x*rotationGenerator κ β J A (m (t-s)) x) hi₀ hi₁,hfirst]
    rw [← integral_sub (f := fun x : Vector N => ρ s x*
      rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x)
      (g := fun x => ρ s x*φ x*rotationGenerator κ β J A (m (t-s)) x) hi₂ hi₁]
    have hfun : (fun x : Vector N => ρ s x*rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x-
        ρ s x*φ x*rotationGenerator κ β J A (m (t-s)) x)=
        (fun x => ρ s x*(rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x-
          φ x*rotationGenerator κ β J A (m (t-s)) x)) := by funext x;ring
    rw [hfun]
    exact generator_fdt_bracket hN κ β J A hA (hρs.of_le (by norm_num)) hpos hφ hms
  rw [he] at hh
  exact hh.2

end SphericalAging.SphereFiniteFDT
