module

public import SphericalAging.SphereRotationGeometry
public import SphericalAging.SphereEntropyBudget

public section

/-! Exact spherical normalization of the proved entropy identity and total Fisher
budget.  Inputs are the actual positive smooth density and its forward equation;
no entropy identity, normalization, or Fisher budget is supplied as a premise. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereCanonicalEntropy

open MeasureTheory Set Filter
open scoped Topology BigOperators
open FiniteModel SphereInitialLaw SphereGibbsEntropy SphericalIntegrationByParts
open SphereEntropyDissipation SphereEntropyBudget SphereRotationGeometry

@[expose] def sphericalForwardDensitySlope {N p : ℕ} (β : ℝ) (J : Disorder N p)
    (ρ : Vector N → ℝ) :=
  forwardDensitySlope (1/(2*(N : ℝ))) β J
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) ρ

/-- Exact physical spherical entropy derivative with the actual tangent score. -/
theorem spherical_entropy_dissipation {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x) (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (t : ℝ) (hPDE : ∀ x,ρdot t x=sphericalForwardDensitySlope β J (ρ t) x) :
    HasDerivAt (fun s => relativeEntropy β J (ρ s)) (-fisherInformation β J (ρ t)) t := by
  have hsp : ContDiff ℝ 2 (ρ t) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (t,x)))
  have hh := entropy_dissipation_hasDerivAt hN (1/(2*(N : ℝ))) β J
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ.continuous hdot hpos hderiv t hsp hPDE
  rwa [rotationFisher_eq_tangent hN β J hsp (hpos t)] at hh

/-- Genuine all-time tangent Fisher integrability and the exact initial entropy budget. -/
theorem spherical_fisher_budget {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x) (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,ρdot t x=sphericalForwardDensitySlope β J (ρ t) x) :
    IntegrableOn (fun t => fisherInformation β J (ρ t)) (Ioi 0) ∧
      (∫ t in Ioi 0,fisherInformation β J (ρ t)) ≤ initialEntropy N p β J := by
  have hh := infinite_fisher_budget hN hp
    (κ := 1/(2*(N : ℝ))) (by positivity) hβ J
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ hdot hpos hderiv hinit hPDE
  have he : (fun t => rotationFisher (1/(2*(N : ℝ))) β J
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) (ρ t))=
      (fun t => fisherInformation β J (ρ t)) := by
    funext t
    apply rotationFisher_eq_tangent hN β J
    · simpa only [Function.comp_def,Function.uncurry,id_eq] using
        hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (t,x)))
    · exact hpos t
  simpa only [he] using hh

/-- The genuine normalized quenched bound of source Lemma 5.1. -/
theorem spherical_fisher_normalized_quenched {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ ρdot : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀ t x,0<ρ t x) (hderiv : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,ρdot t x=sphericalForwardDensitySlope β J (ρ t) x) :
    (∫ t in Ioi 0,fisherInformation β J (ρ t))/(N : ℝ) ≤
      2*β*GaussianLandscape.landscapeNorm N p J := by
  exact (div_le_div_of_nonneg_right
    (spherical_fisher_budget hN hp hβ J hρ hdot hpos hderiv hinit hPDE).2 (Nat.cast_nonneg N)).trans
    (initialEntropy_normalized_quenched hN hp hβ J).2

/-- The true disorder expectation of the total Fisher budget is bounded by beta²/2.
The only additional assumption is measurability of the actual total Fisher mass. -/
theorem spherical_fisher_normalized_annealed {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {ρ ρdot : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 2 (Function.uncurry (ρ J)))
    (hdot : ∀ J,Continuous (Function.uncurry (ρdot J)))
    (hpos : ∀ J t x,0<ρ J t x)
    (hderiv : ∀ J t x,HasDerivAt (fun s => ρ J s x) (ρdot J t x) t)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,ρdot J t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : AEStronglyMeasurable
      (fun J : Disorder N p => ∫ t in Ioi 0,fisherInformation β J (ρ J t)) (disorderLaw N p)) :
    (∫ J : Disorder N p,(∫ t in Ioi 0,fisherInformation β J (ρ J t))/(N : ℝ) ∂disorderLaw N p) ≤
      β^2/2 := by
  have hbudget J := spherical_fisher_budget hN hp hβ J (hρ J) (hdot J) (hpos J)
    (hderiv J) (hinit J) (hPDE J)
  have hnon J : 0≤(∫ t in Ioi 0,fisherInformation β J (ρ J t)) :=
    integral_nonneg fun t => by
      unfold fisherInformation
      exact integral_nonneg fun x => mul_nonneg (hpos J t x).le (sq_nonneg _)
  have hint : Integrable (fun J : Disorder N p => ∫ t in Ioi 0,fisherInformation β J (ρ J t))
      (disorderLaw N p) := by
    refine (initialEntropy_annealed_integrable hN hp hβ).mono' hmeas ?_
    exact ae_of_all _ fun J => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hnon J)]
      exact (hbudget J).2
  have hh := integral_mono (hint.div_const (N : ℝ))
    ((initialEntropy_annealed_integrable hN hp hβ).div_const (N : ℝ))
    (fun J => div_le_div_of_nonneg_right (hbudget J).2 (Nat.cast_nonneg N))
  exact hh.trans (initialEntropy_normalized_annealed hN hp hβ)

end SphericalAging.SphereCanonicalEntropy
