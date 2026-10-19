module

public import SphericalAging.SphereFiniteFDT
public import SphericalAging.SphereCoordinateScore

public section

/-! Exact finite-dimensional nonequilibrium FDT for the true canonical sphere
forward/backward PDEs and the physical tangent score. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereQuenchedFDT

open MeasureTheory Set Filter
open scoped Topology BigOperators InnerProductSpace
open FiniteModel SphereInitialLaw HardSphereDynamics SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereForwardAdjoint SphereFDTAlgebra
open SphereFiniteFDT SphereCoordinateScore SphereFisherCurrent SphereRotationGeometry SphereCanonicalEntropy

@[expose] abbrev canonicalRotations (N : ℕ) (ij : Fin N × Fin N) := coordinateRotation ij.1 ij.2

@[expose] def quenchedCorrelation {N : ℕ} (ρ : ℝ → Vector N → ℝ) (m : ℝ → Vector N → Vector N)
    (t s : ℝ) : ℝ :=
  (∑ i : Fin N,correlationPairing ρ (coordinateObservable i) (fun τ x => m τ x i) t s)/(N : ℝ)

@[expose] def quenchedResponse {N : ℕ} (ρ : ℝ → Vector N → ℝ) (m : ℝ → Vector N → Vector N)
    (t s : ℝ) : ℝ :=
  (∑ i : Fin N,∫ x : Vector N,ρ s x*rotationGamma (1/(2*(N : ℝ))) (canonicalRotations N)
    (coordinateObservable i) (fun y => m (t-s) y i) x ∂sphereLaw N)/(N : ℝ)

/-- The defined finite coordinate correlation is the actual physical overlap pairing. -/
theorem quenchedCorrelation_eq_inner {N : ℕ} (hN : 0<N) {ρ : ℝ → Vector N → ℝ}
    (hρ : Continuous (Function.uncurry ρ)) {m : ℝ → Vector N → Vector N}
    (hm : Continuous (Function.uncurry m)) (t s : ℝ) :
    quenchedCorrelation ρ m t s=(∫ x : Vector N,ρ s x*⟪x,m (t-s) x⟫_ℝ ∂sphereLaw N)/(N : ℝ) := by
  classical
  unfold quenchedCorrelation correlationPairing
  congr 1
  have hr : Continuous (ρ s) := hρ.comp (continuous_const.prodMk continuous_id)
  have hmrow : Continuous (m (t-s)) := hm.comp (continuous_const.prodMk continuous_id)
  have hint (i : Fin N) : Integrable (fun x : Vector N => ρ s x*coordinateObservable i x*m (t-s) x i)
      (sphereLaw N) := continuous_sphere_integrable hN
    ((hr.mul (coordinateObservable_contDiff i).continuous).mul
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp hmrow))
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [real_inner_coordinates]
    simp only [coordinateObservable]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Actual coordinate-current summation gives the exact source vector current. -/
theorem coordinate_integrated_current {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x)
    {m : Vector N → Vector N} (hm : Continuous m) :
    (∑ i : Fin N,∫ x : Vector N,ρ x*m x i*rotationGamma (1/(2*(N : ℝ))) (canonicalRotations N)
      (relativeLog β J ρ) (coordinateObservable i) x ∂sphereLaw N)/(N : ℝ)=
      currentDefect β J ρ m := by
  classical
  have hlog := relativeLog_contDiff β J (hρ.of_le (by norm_num)) hpos
  have hint (i : Fin N) : Integrable (fun x : Vector N => ρ x*m x i*
      rotationGamma (1/(2*(N : ℝ))) (canonicalRotations N)
        (relativeLog β J ρ) (coordinateObservable i) x) (sphereLaw N) :=
    continuous_sphere_integrable hN
      ((hρ.continuous.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp hm)).mul
        (rotationGamma_continuous _ _ hlog ((coordinateObservable_contDiff i).of_le (by simp))))
  unfold currentDefect
  congr 1
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i)]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hs : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  rw [← coordinate_current_inner hN β J ρ (m x) x hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact source nonequilibrium fluctuation-dissipation identity, with its genuine
current. Only actual forward/backward PDEs are inputs. -/
theorem quenched_fdt_hasDerivAt {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hm : ContDiff ℝ 2 (Function.uncurry m))
    (hback : ∀ i : Fin N,∀ v,0<v → ∀ x,HasDerivAt (fun w => m w x i)
      (rotationGenerator (1/(2*(N : ℝ))) β J (canonicalRotations N) (fun y => m v y i) x) v)
    {t s : ℝ} (hst : s<t) (hpos : ∀ x,0<ρ s x)
    (hPDE : ∀ x,ρdot s x=sphericalForwardDensitySlope β J (ρ s) x) :
    HasDerivAt (fun v => quenchedCorrelation ρ m t v)
      (quenchedResponse ρ m t s-currentDefect β J (ρ s) (m (t-s))) s := by
  classical
  have hmcoord (i : Fin N) : ContDiff ℝ 2 (Function.uncurry (fun τ x => m τ x i)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff.comp hm
  have hsp : ContDiff ℝ 2 (ρ s) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (s,x)))
  have hmrow : Continuous (m (t-s)) := hm.continuous.comp (continuous_const.prodMk continuous_id)
  have hc i := single_component_fdt_hasDerivAt hN (1/(2*(N : ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ hdot hderiv (hmcoord i)
    ((coordinateObservable_contDiff i).of_le (by simp)) (hback i) hst hpos hPDE
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hc i)).div_const (N : ℝ)
  simp only [Finset.sum_sub_distrib,sub_div] at hd
  rw [coordinate_integrated_current hN β J hsp hpos hmrow] at hd
  exact hd

/-- The exact derivative identity and the true conditional-mean norm bound give
actual quenched FDT defect square≤I/N. -/
theorem quenched_fdt_fisher_bound {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hm : ContDiff ℝ 2 (Function.uncurry m))
    (hback : ∀ i : Fin N,∀ v,0<v → ∀ x,HasDerivAt (fun w => m w x i)
      (rotationGenerator (1/(2*(N : ℝ))) β J (canonicalRotations N) (fun y => m v y i) x) v)
    {t s : ℝ} (hst : s<t) (hpos : ∀ x,0<ρ s x)
    (hPDE : ∀ x,ρdot s x=sphericalForwardDensitySlope β J (ρ s) x)
    (hmass : (∫ x : Vector N,ρ s x ∂sphereLaw N)=1)
    (hmean : ∀ x,OnSphere x → ‖m (t-s) x‖^2 ≤ (N : ℝ)) :
    (quenchedResponse ρ m t s-deriv (fun v => quenchedCorrelation ρ m t v) s)^2 ≤
      fisherInformation β J (ρ s)/(N : ℝ) := by
  have hd := quenched_fdt_hasDerivAt hN β J hρ hdot hderiv hm hback hst hpos hPDE
  rw [hd.deriv]
  have hsp : ContDiff ℝ 2 (ρ s) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (s,x)))
  have hmrow : Continuous (m (t-s)) := hm.continuous.comp (continuous_const.prodMk continuous_id)
  simpa only [sub_sub_cancel] using currentDefect_fisher_bound hN β J hsp hpos hmass hmrow hmean

end SphericalAging.SphereQuenchedFDT
