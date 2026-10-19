-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteCusp
public import SlowEquilibration.InfiniteMixtureCuspSourceContact

/-! Literal source quantifiers and contact coefficient for the actual
infinite-mixture cusp theorem. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set Filter MeasureTheory ProbabilityTheory SphericalModel InfiniteMixture
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem source_cusp_temperature_parameter (μ : InfiniteMixture) {ε : ℝ} (hε : 0≤ε) :
    (Thresholds.dynamicalThreshold μ.xi*Real.sqrt (1+ε))^2*μ.Amax-1=ε := by
  rw [mul_pow,Real.sq_sqrt (by linarith),μ.dynamicalThreshold_sq]
  field_simp [μ.Amax_pos.ne']
  ring

/-- Source theorem 1.7 with its literal contact order, coefficient, epsilon
interval, dimension threshold and original infinite Gaussian disorder, for
the source summable class. The count rate is fixed before theta and epsilon. -/
theorem source_cusp (μ : InfiniteMixture)
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
            ∀ J∈Ω,∀ hn : 1≤n,
              (infiniteSpectralData n hn
                (Thresholds.dynamicalThreshold μ.xi*Real.sqrt (1+ε)) μ J).eigenvalue
                  (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
                    Real.exp (-(1-θ)*
                      ((2*(m:ℝ)*μ.qD)/((2*(m:ℝ)+1)*(1-μ.qD))*a^(-1/(2*(m:ℝ))))*
                        ε^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) := by
  obtain ⟨c,κ,hκ,hc⟩ := cusp_eigenvalues μ hgap
  refine ⟨μ.globalMaximizers_finite hgap,μ.globalMaximizers_subset_interior hgap,
    μ.qD_mem_globalMaximizers hgap,c.m,c.a,κ,c.m_pos,c.a_pos,hκ,c.sourceContact_normalized,?_⟩
  intro θ hθ
  obtain ⟨ε₀,hε₀,heps⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hc θ hθ)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε
  obtain ⟨a',ha',hev⟩ := heps hε
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  refine ⟨a',ha',max n₀ 1,le_max_right _ _,?_⟩
  intro n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hn₀ n ((le_max_left _ _).trans hn)
  refine ⟨Ω,hΩ,hfail,?_⟩
  intro J hJ hn'
  have hh := hgood J hJ hn'
  rw [c.barrierCoefficient_eq_source] at hh
  convert hh using 1 <;> congr 2 <;> ring

end SlowEquilibration.SphericalInfiniteModel
