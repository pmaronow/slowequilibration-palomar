module

public import SphericalAging.FilteredItoPullback
public import SphericalAging.AnnealedSDECore

public section

/-! A genuine random-coefficient SDE pulls back under a filtered
measure-preserving sample map that retains the actual Brownian coordinates.
The stochastic identity is proved using the actual Itô operators. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.FilteredRandomSDEPullback
open HardSphereDynamics VectorIto FilteredItoPullback AnnealedSDECore
set_option maxHeartbeats 1800000
variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'} {N : ℕ}

/-- Faithful strong-solution transfer between actual probability spaces. -/
theorem randomStrongSolution_pullback {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) (hF : ∀ t, @Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀ i t, E.coordinate i t =ᵐ[Q] (fun ω => D.coordinate i t (φ ω)))
    (b : Ω → Fin N → State N → ℝ) (sigma : Ω → Fin N → Fin N → State N → ℝ)
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D b sigma Z0 X T) :
    IsRandomStrongSolutionOn E (fun ω => b (φ ω)) (fun ω => sigma (φ ω))
      (fun ω => Z0 (φ ω)) (fun t ω => X t (φ ω)) T := by
  rcases hsol with ⟨h0,ha,hc,A,U,hA,hU,heq⟩
  refine ⟨h0.comp_measurable (hF 0),fun t => (ha t).comp_measurable (hF t),
    hφ.quasiMeasurePreserving.ae hc,fun i => predictablePullback hφ hF (A i),
    fun i j => predictablePullback hφ hF (U i j),?_,?_,?_⟩
  · intro i
    have he := (timeMap_measurePreserving hφ).quasiMeasurePreserving.ae_eq_comp (hA i)
    exact (predictablePullback_coe hφ hF (A i)).trans he
  · intro i j
    have he := (timeMap_measurePreserving hφ).quasiMeasurePreserving.ae_eq_comp (hU i j)
    exact (predictablePullback_coe hφ hF (U i j)).trans he
  · intro t ht i
    rw [vectorProcessLp_pullback hφ hF D E hB]
    have hh := hφ.quasiMeasurePreserving.ae (heq t ht i)
    filter_upwards [hh,randomPullback_coe hφ (vectorProcessLp D (U i) t)] with ω he hI
    rw [hI]
    exact he

end SphericalAging.FilteredRandomSDEPullback
