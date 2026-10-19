-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteCuspLiteral
public import SlowEquilibration.SphericalInfiniteC2Core

/-! The source cusp estimate for the unique self-adjoint closure of the
actual C² spherical differential operator −L on the original-series Gibbs
space. This spectral identification does not assert an SDE-semigroup identity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set Filter MeasureTheory ProbabilityTheory SphericalModel InfiniteMixture
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The manuscript's temperature parameter is positive above the actual
threshold, and its positive inverse is the temperature used by the cusp proof. -/
theorem source_cusp_parameter_inverse (μ : InfiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) :
    0<β^2*μ.Amax-1 ∧
      Thresholds.dynamicalThreshold μ.xi*Real.sqrt (1+(β^2*μ.Amax-1))=β := by
  have hd : 0≤Thresholds.dynamicalThreshold μ.xi := Real.sqrt_nonneg _
  have hb : 0<β := hd.trans_lt hβ
  have hs : Thresholds.dynamicalThreshold μ.xi^2<β^2 := (sq_lt_sq₀ hd hb.le).mpr hβ
  have hmul : Thresholds.dynamicalThreshold μ.xi^2*μ.Amax=1 := by
    rw [μ.dynamicalThreshold_sq,inv_mul_cancel₀ μ.Amax_pos.ne']
  have hpos : 0<β^2*μ.Amax-1 := by
    have hh := mul_lt_mul_of_pos_right hs μ.Amax_pos
    linarith
  refine ⟨hpos,?_⟩
  apply (sq_eq_sq₀ (mul_nonneg hd (Real.sqrt_nonneg _)) hb.le).mp
  rw [mul_pow,Real.sq_sqrt (by linarith : 0≤1+(β^2*μ.Amax-1)),μ.dynamicalThreshold_sq]
  field_simp [μ.Amax_pos.ne']
  ring

/-- Literal source theorem, with β arbitrary above β_d and
ε=β² A_max−1. The eigenbasis belongs to the uniquely closed actual C²
operator −L, not merely to a separately defined diagonal operator. -/
theorem source_cusp_differential (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.globalMaximizers.Finite ∧ (μ.globalMaximizers ⊆ Ioo (0 : ℝ) 1) ∧
      μ.qD∈μ.globalMaximizers ∧ (∀ q∈μ.globalMaximizers,q≤μ.qD) ∧
    ∃ m : ℕ,∃ a κ : ℝ,1 ≤ m ∧ 0<a ∧ 0<κ ∧
      ((fun y : ℝ => μ.A (μ.qD+y)/μ.Amax-(1-a*y^(2*m)))
        =O[𝓝 (0:ℝ)] (fun y => y^(2*m+1))) ∧
      ∀ θ∈Ioo (0:ℝ) 1,∃ ε₀ : ℝ,0<ε₀ ∧
        ∀ β : ℝ,Thresholds.dynamicalThreshold μ.xi<β → β^2*μ.Amax-1<ε₀ →
        ∃ a' : ℝ,0<a' ∧ ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
          ∃ Ω : Set (Disorder (n+1)),MeasurableSet Ω ∧
            (disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a'*(n+1:ℕ)) ∧
            ∀ J∈Ω,∃ hJ : J∈summableJetDisorder μ,
              IsSelfAdjoint (literalC2DifferentialOperator n μ J hJ β).closure ∧
              (literalC2DifferentialOperator n μ J hJ β).closure=literalWeakGenerator n μ J hJ β ∧
              ∀ hn : 1≤n,
                (literalSpectralSemigroupData n hn μ J hJ β).eigenvalue
                  (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
                    Real.exp (-(1-θ)*
                      ((2*(m:ℝ)*μ.qD)/((2*(m:ℝ)+1)*(1-μ.qD))*a^(-1/(2*(m:ℝ))))*
                        (β^2*μ.Amax-1)^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) ∧
                ∀ j : ℕ,∃ hj : (literalSpectralSemigroupData n hn μ J hJ β).basis j∈
                    (literalC2DifferentialOperator n μ J hJ β).closure.domain,
                  (literalC2DifferentialOperator n μ J hJ β).closure
                    ⟨(literalSpectralSemigroupData n hn μ J hJ β).basis j,hj⟩=
                      (literalSpectralSemigroupData n hn μ J hJ β).eigenvalue j •
                        (literalSpectralSemigroupData n hn μ J hJ β).basis j := by
  obtain ⟨hfin,hint,hqd,m,a,κ,hm,ha,hκ,hcontact,hsource⟩ := source_cusp_literal μ hgap
  refine ⟨hfin,hint,hqd,fun q hq => μ.globalMaximizer_le_qD hq,m,a,κ,hm,ha,hκ,hcontact,?_⟩
  intro θ hθ
  obtain ⟨ε₀,hε₀,hε⟩ := hsource θ hθ
  refine ⟨ε₀,hε₀,?_⟩
  intro β hβ hsmall
  obtain ⟨hpos,hback⟩ := source_cusp_parameter_inverse μ hβ
  obtain ⟨a',ha',n₀,hn₀,hN⟩ := hε (β^2*μ.Amax-1) ⟨hpos,hsmall⟩
  rw [hback] at hN
  refine ⟨a',ha',n₀,hn₀,?_⟩
  intro n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN n hn
  refine ⟨Ω,hΩ,hfail,?_⟩
  intro J hJΩ
  obtain ⟨hJ,hbound⟩ := hgood J hJΩ
  refine ⟨hJ,literalC2DifferentialOperator_essentiallySelfAdjoint n μ J hJ β,
    literalC2DifferentialOperator_closure n μ J hJ β,?_⟩
  intro hn'
  refine ⟨hbound hn',?_⟩
  intro j
  rw [literalC2DifferentialOperator_closure]
  exact literalWeakGenerator_eigen n hn' μ J hJ β j

end SlowEquilibration.SphericalInfiniteModel
