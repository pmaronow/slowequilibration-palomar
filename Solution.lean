module
public import SlowEquilibration.PalomarSixCondensed
public import SlowEquilibration.PalomarMemoryBridge
public import SlowEquilibration.PalomarSixCusp

@[expose] public section
noncomputable section
set_option backward.proofsInPublic true
namespace SlowEquilibrationCondensedSource
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

theorem theorem_1_2 (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  exact SlowEquilibration.PalomarSixCondensed.theorem_1_2 μ h hChen

theorem corollary_1_3_a (p : ℕ) (hp : 4≤p) {β : ℝ}
    (hβ : staticThreshold (fun r : ℝ => r^p)<β) (hChen : Chen2013FiniteParisi) :
    UniformConclusions (pureCovariance p (by omega)) β := by
  exact SlowEquilibration.PalomarSixCondensed.corollary_1_3_a p hp hβ hChen

theorem corollary_1_3_b (μ : FiniteMixture) (hd : 4≤μ.minDegree) {β : ℝ}
    (hβ : staticThreshold μ.xi<β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1) (inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi) : UniformConclusions μ β := by
  exact SlowEquilibration.PalomarSixCondensed.corollary_1_3_b μ hd hβ hξ hChen

theorem corollary_1_3_b_degree_window (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    (hw : ((μ.minDegree : ℝ)+μ.maxDegree-5)^2 <
      6*((μ.minDegree : ℝ)-2)*((μ.maxDegree : ℝ)-2))
    {β : ℝ} (hβ : staticThreshold μ.xi<β) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  exact SlowEquilibration.PalomarSixCondensed.corollary_1_3_b_degree_window μ hd hw hβ hChen

theorem corollary_1_3_b_support (μ : FiniteMixture)
    (hs : ∀ p∈μ.coeff.support, p∈Finset.Icc 4 11)
    {β : ℝ} (hβ : staticThreshold μ.xi<β) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  exact SlowEquilibration.PalomarSixCondensed.corollary_1_3_b_support μ hs hβ hChen

theorem corollary_1_3_c (d P : ℕ) (hd : 4≤d) (heven : Even d) (hdP : d<P)
    {β : ℝ} (hβ : staticThreshold (fun r : ℝ => r^d)<β)
    (hChen : Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ b : ClassPerturbation d P,
      b.coeff.sum (fun _ c => c)=1 → ∀ (ε : ℝ) (hε : 0<ε), ε<ε₀ →
        UniformConclusions (b.covariance (by omega) ε hε.le) β := by
  exact SlowEquilibration.PalomarSixCondensed.corollary_1_3_c d P hd heven hdP hβ hChen

theorem corollary_1_3_d (hChen : Chen2013FiniteParisi) :
    UniformConclusions exampleCovariance exampleBeta := by
  exact SlowEquilibration.PalomarSixCondensed.corollary_1_3_d hChen

theorem theorem_1_4_haar {N : ℕ} (hN : 1≤N) (μ : FiniteMixture) (β : ℝ)
    (T : ℝ≥0) (ν : ProbabilityMeasure (Vector N))
    (hν : ∀ᵐ x∂ν.toMeasure, OnSphere x) :
    (∫ J, 1-distance μ β T J ν.toMeasure ∂disorderLaw N μ.maxDegree) ≤
      ∫ J, 1-distance μ β T J (sphereLaw N) ∂disorderLaw N μ.maxDegree := by
  exact SlowEquilibration.PalomarSixCondensed.theorem_1_4_haar hN μ β T ν hν

universe u v
theorem theorem_1_4 (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hChen : Chen2013FiniteParisi) :
    ∃ γ : ℝ, 0<γ ∧ SixInitialConclusions.{u,v} μ β γ := by
  exact SlowEquilibration.PalomarSixCondensed.theorem_1_4 μ h hChen

end SlowEquilibrationCondensedSource

namespace SlowEquilibrationCondensedSource
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
theorem theorem_1_5 (μ : FiniteMixture) {β b : ℝ}
    (hβd : dynamicalThreshold μ.xi < β) (hβs : β < staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) ((qStar μ.xi β)^2)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ J ∈ Ω, ∀ _hN : 2 ≤ N, MemoryConclusions μ β J b κ γ a c C := by
  exact SlowEquilibration.PalomarMemory.theorem_1_5 μ hβd hβs hb

theorem theorem_1_6 (μ : FiniteMixture) {β b : ℝ}
    (hβd : dynamicalThreshold μ.xi < β) (hβs : β < staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) (qStar μ.xi β)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      (∀ᶠ N : ℕ in atTop, ∃ Ω₀ : Set (Disorder N μ.maxDegree), MeasurableSet Ω₀ ∧
        (disorderLaw N μ.maxDegree).real Ω₀ᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ J ∈ Ω₀, ∀ _hN : 2 ≤ N, PersistentMemoryConclusions μ β J κ γ a c C) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree),
        MeasurableSet Ω ∧ (disorderLaw N μ.maxDegree).real Ωᶜ < η ∧
        ∀ J ∈ Ω, ∀ _hN : 2 ≤ N, MemoryConclusions μ β J b κ γ a c C) := by
  exact SlowEquilibration.PalomarMemory.theorem_1_6 μ hβd hβs hb

end SlowEquilibrationCondensedSource

namespace SlowEquilibrationCuspSource
open Set Filter MeasureTheory
open scoped Topology
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
  exact SlowEquilibration.PalomarSixCusp.theorem_1_7 c hc hzero hne hsum hgap

end SlowEquilibrationCuspSource
