-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteCuspSource
public import SlowEquilibration.SphericalInfiniteOperators

/-! The exact cusp estimate on the literal original-series Gibbs L² space.
The eigenvalues belong to its actual self-adjoint weak generator, with
C² differential action and compact resolvent already proved. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set Filter MeasureTheory ProbabilityTheory SphericalModel InfiniteMixture
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem source_cusp_literal (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.globalMaximizers.Finite ∧ (μ.globalMaximizers ⊆ Ioo (0 : ℝ) 1) ∧
      μ.qD∈μ.globalMaximizers ∧
    ∃ m : ℕ,∃ a κ : ℝ,1 ≤ m ∧ 0<a ∧ 0<κ ∧
      ((fun y : ℝ => μ.A (μ.qD+y)/μ.Amax-(1-a*y^(2*m)))
        =O[𝓝 (0:ℝ)] (fun y => y^(2*m+1))) ∧
      ∀ θ∈Ioo (0:ℝ) 1,∃ ε₀ : ℝ,0<ε₀ ∧ ∀ ε∈Ioo (0:ℝ) ε₀,
        ∃ a' : ℝ,0<a' ∧ ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
          ∃ Ω : Set (Disorder (n+1)),MeasurableSet Ω ∧
            (disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a'*(n+1:ℕ)) ∧
            ∀ J∈Ω,∃ hJ : J∈summableJetDisorder μ,∀ hn : 1≤n,
              (literalSpectralSemigroupData n hn μ J hJ
                (Thresholds.dynamicalThreshold μ.xi*Real.sqrt (1+ε))).eigenvalue
                  (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
                    Real.exp (-(1-θ)*
                      ((2*(m:ℝ)*μ.qD)/((2*(m:ℝ)+1)*(1-μ.qD))*a^(-1/(2*(m:ℝ))))*
                        ε^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) := by
  obtain ⟨hfinite,hinterior,hqD,m,a,κ,hm,ha,hκ,hcontact,hsource⟩ := source_cusp μ hgap
  refine ⟨hfinite,hinterior,hqD,m,a,κ,hm,ha,hκ,hcontact,?_⟩
  intro θ hθ
  obtain ⟨ε₀,hε₀,heps⟩ := hsource θ hθ
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε
  obtain ⟨a',ha',n₀,hn₀,hN⟩ := heps ε hε
  refine ⟨a',ha',n₀,hn₀,?_⟩
  intro n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN n hn
  obtain ⟨R,hR,hRm,hRg⟩ := (summableJetDisorder_ae (N := n+1) (by omega) μ).exists_measurable_mem
  refine ⟨Ω∩R,hΩ.inter hRm,?_,?_⟩
  · have hnull : (disorderLaw (n+1)).real Rᶜ=0 := by
      have hh : disorderLaw (n+1) Rᶜ=0 := mem_ae_iff.mp hR
      rw [measureReal_def,hh,ENNReal.toReal_zero]
    rw [compl_inter]
    exact (measureReal_union_le Ωᶜ Rᶜ).trans (by simpa only [hnull,add_zero] using hfail)
  · intro J hJ
    refine ⟨hRg J hJ.2,?_⟩
    intro hn'
    exact hgood J hJ.1 hn'

end SlowEquilibration.SphericalInfiniteModel
