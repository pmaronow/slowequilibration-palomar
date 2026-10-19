-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SmoothRayleighEigenvalue
public import SlowEquilibration.SphericalInfiniteCuspLiteral

/-! The source Gaussian series and the standard Rayleigh spectrum agree
with the actual original-series spherical Gibbs model and its generator. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarCusp
open MeasureTheory Set Filter
open SphericalModel SphericalForm SphericalInfiniteModel
open scoped Topology
set_option maxHeartbeats 800000

lemma source_disorderLaw_eq (N : ℕ) :
    SlowEquilibrationCuspSource.disorderLaw N=SphericalInfiniteModel.disorderLaw N := rfl

lemma source_field_eq (μ : InfiniteMixture) {N : ℕ} (J : Disorder N) :
    SlowEquilibrationCuspSource.field μ.coeff J=field μ J := rfl

theorem source_physicalEigenvalue_eq (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (k : ℕ) :
    SlowEquilibrationCuspSource.physicalEigenvalue μ.coeff J β k=
      (literalSpectralSemigroupData n hn μ J hJ β).eigenvalue k := by
  change SlowEquilibrationCuspSource.rayleighEigenvalue
    (gibbsLaw (n+1) β (field μ J)) k=(infiniteSpectralData n hn β μ J).eigenvalue k
  rw [literal_gibbsLaw_eq_regular n μ β J hJ]
  exact literal_rayleigh_eq_eigenvalue (show 2≤n+1 by omega) β
    ((regularAmbientField_contDiff n μ J).of_le (by norm_num))
    (normalizedSphericalSpectralData (show 2≤n+1 by omega) β
      (regularAmbientField n μ J) (regularAmbientField_contDiff n μ J).continuous) k

/-- The literal source spectral cusp in approved-library statement objects.
The coefficient assumptions are the original summable mixed-spin class. -/
theorem source_spectral_cusp (c : ℕ → ℝ)
    (hc : ∀ p,0≤c p) (hzero : ∀ p,p<2 → c p=0) (hne : c≠0)
    (hsum : Summable (fun p : ℕ => (p:ℝ)^(5/2:ℝ)*Real.sqrt (c p)))
    (hgap : SlowEquilibrationCuspSource.dynamicalThreshold c<
      SlowEquilibrationCuspSource.staticThreshold c) :
    (SlowEquilibrationCuspSource.globalMaximizers c).Finite ∧
      (SlowEquilibrationCuspSource.globalMaximizers c⊆Ioo (0:ℝ) 1) ∧
      SlowEquilibrationCuspSource.qD c∈SlowEquilibrationCuspSource.globalMaximizers c ∧
    ∃ m : ℕ,∃ a κ : ℝ,1 ≤ m ∧ 0<a ∧ 0<κ ∧
      ((fun y : ℝ => SlowEquilibrationCuspSource.A c (SlowEquilibrationCuspSource.qD c+y)/
          SlowEquilibrationCuspSource.Amax c-(1-a*y^(2*m)))
        =O[𝓝 (0:ℝ)] (fun y => y^(2*m+1))) ∧
      ∀ θ∈Ioo (0:ℝ) 1,∃ ε₀ : ℝ,0<ε₀ ∧ ∀ ε∈Ioo (0:ℝ) ε₀,
        ∃ a' : ℝ,0<a' ∧ ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
          ∃ Ω : Set (SlowEquilibrationCuspSource.Disorder (n+1)),MeasurableSet Ω ∧
            (SlowEquilibrationCuspSource.disorderLaw (n+1)).real Ωᶜ≤
              14*Real.exp (-a'*(n+1:ℕ)) ∧
            ∀ J∈Ω,SlowEquilibrationCuspSource.physicalEigenvalue c J
                (SlowEquilibrationCuspSource.dynamicalThreshold c*Real.sqrt (1+ε))
                (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
              Real.exp (-(1-θ)*
                ((2*(m:ℝ)*SlowEquilibrationCuspSource.qD c)/
                  ((2*(m:ℝ)+1)*(1-SlowEquilibrationCuspSource.qD c))*a^(-1/(2*(m:ℝ))))*
                ε^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) := by
  let μ : InfiniteMixture := ⟨c,hc,hzero,hne,hsum⟩
  have hg : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi := hgap
  obtain ⟨hfin,hint,hqd,m,a,κ,hm,ha,hκ,hcontact,hsource⟩ := source_cusp_literal μ hg
  refine ⟨hfin,hint,hqd,m,a,κ,hm,ha,hκ,hcontact,?_⟩
  intro θ hθ
  obtain ⟨ε₀,hε₀,heps⟩ := hsource θ hθ
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε
  obtain ⟨a',ha',n₀,hn₀,hN⟩ := heps ε hε
  refine ⟨a',ha',n₀,hn₀,?_⟩
  intro n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN n hn
  refine ⟨Ω,hΩ,hfail,?_⟩
  intro J hJ
  obtain ⟨hgJ,hb⟩ := hgood J hJ
  have hn₁ : 1≤n := hn₀.trans hn
  rw [source_physicalEigenvalue_eq n hn₁ μ J hgJ]
  exact hb hn₁

end SlowEquilibration.PalomarCusp
