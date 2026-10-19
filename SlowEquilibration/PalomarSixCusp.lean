module
public import SixHeadlines
public import SlowEquilibration.PalomarCuspSourceBridge

@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarSixCusp
open Set Filter MeasureTheory
open SphericalModel SphericalInfiniteModel
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem theorem_1_7 (c : ℕ → ℝ)
    (hc : ∀ p,0≤c p) (hzero : ∀ p,p<2 → c p=0) (hne : c≠0)
    (hsum : Summable (fun p : ℕ => (p:ℝ)^(5/2:ℝ)*Real.sqrt (c p)))
    (hgap : SlowEquilibrationCuspSource.dynamicalThreshold c<
      SlowEquilibrationCuspSource.staticThreshold c) :
    (SlowEquilibrationCuspSource.globalMaximizers c).Finite ∧
      (SlowEquilibrationCuspSource.globalMaximizers c⊆Ioo (0:ℝ) 1) ∧
      SlowEquilibrationCuspSource.qD c∈SlowEquilibrationCuspSource.globalMaximizers c ∧
      (∀ q∈SlowEquilibrationCuspSource.globalMaximizers c,q≤SlowEquilibrationCuspSource.qD c) ∧
    ∃ m : ℕ,∃ a κ : ℝ,1 ≤ m ∧ 0<a ∧ 0<κ ∧
      ((fun y : ℝ => SlowEquilibrationCuspSource.A c (SlowEquilibrationCuspSource.qD c+y)/
          SlowEquilibrationCuspSource.Amax c-(1-a*y^(2*m)))
        =O[𝓝 (0:ℝ)] (fun y => y^(2*m+1))) ∧
      ∀ θ∈Ioo (0:ℝ) 1,∃ ε₀ : ℝ,0<ε₀ ∧
        ∀ β : ℝ,SlowEquilibrationCuspSource.dynamicalThreshold c<β →
          β^2*SlowEquilibrationCuspSource.Amax c-1<ε₀ →
        ∃ a' : ℝ,0<a' ∧ ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
          ∃ Ω : Set (SlowEquilibrationCuspSource.Disorder (n+1)),MeasurableSet Ω ∧
            (SlowEquilibrationCuspSource.disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a'*(n+1:ℕ)) ∧
            ∀ J∈Ω,SlowEquilibrationCuspSource.physicalEigenvalue c J β
                (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
              Real.exp (-(1-θ)*
                ((2*(m:ℝ)*SlowEquilibrationCuspSource.qD c)/
                  ((2*(m:ℝ)+1)*(1-SlowEquilibrationCuspSource.qD c))*a^(-1/(2*(m:ℝ))))*
                (β^2*SlowEquilibrationCuspSource.Amax c-1)^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) := by
  let μ : InfiniteMixture := ⟨c,hc,hzero,hne,hsum⟩
  obtain ⟨hfin,hint,hqd,hmax,m,a,κ,hm,ha,hκ,hcontact,hsource⟩ :=
    SixHeadlines.theorem_1_7 μ hgap
  refine ⟨hfin,hint,hqd,hmax,m,a,κ,hm,ha,hκ,hcontact,?_⟩
  intro θ hθ
  obtain ⟨ε₀,hε₀,heps⟩ := hsource θ hθ
  refine ⟨ε₀,hε₀,?_⟩
  intro β hβ hsmall
  obtain ⟨a',ha',n₀,hn₀,hN⟩ := heps β hβ hsmall
  refine ⟨a',ha',n₀,hn₀,?_⟩
  intro n hn
  obtain ⟨Ω,hΩ,hfail,hgood⟩ := hN n hn
  refine ⟨Ω,hΩ,hfail,?_⟩
  intro J hJ
  obtain ⟨hgJ,_hself,_hclosure,hb⟩ := hgood J hJ
  have hn₁ : 1≤n := hn₀.trans hn
  rw [PalomarCusp.source_physicalEigenvalue_eq n hn₁ μ J hgJ]
  exact (hb hn₁).1

end SlowEquilibration.PalomarSixCusp
