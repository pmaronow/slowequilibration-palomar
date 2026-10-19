module

public import SphericalAging.RandomCoefficientUniqueness
public import SphericalAging.HamiltonianParameter
public import SphericalAging.AnnealedGlobalSDE

public section

/-! Actual pathwise uniqueness for the finite-N physical sphere SDE with
random disorder known at time zero. Unbounded Gaussian disorder is handled
by genuine time-zero localization and countable passage, not by replacing
its law with bounded support. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.AnnealedPhysicalUniqueness
open HardSphereDynamics AnnealedSDECore RandomCoefficientUniqueness
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Full actual random-disorder physical pathwise uniqueness on a finite
horizon. The only solution premises are the genuine random-coefficient
strong SDE equation and sphere paths. -/
theorem physical_pathwise_uniqueness (D : BrownianDriver N P F) (β : ℝ)
    (J : Ω → FiniteModel.Disorder N p) (hJ : StronglyMeasurable[F 0] J)
    (Z₀ : Ω → State N) (X Y : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D
      (fun ω i x => hamiltonianDrift β (J ω) x i) (fun _ i j x => noiseColumn x j i) Z₀ X T)
    (hY : IsRandomStrongSolutionOn D
      (fun ω i x => hamiltonianDrift β (J ω) x i) (fun _ i j x => noiseColumn x j i) Z₀ Y T)
    (hXs : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω))
    (hYs : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → X t ω = Y t ω := by
  let R : ℝ≥0 := N+1
  have hR : 0 < (R : ℝ) := by
    simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; positivity
  have hXb := PhysicalUniqueness.sphere_radius_bound X T hXs
  have hYb := PhysicalUniqueness.sphere_radius_bound Y T hYs
  have hlocal : ∀ a : ℕ, ∀ᵐ ω ∂P, ‖J ω‖ ≤ (a : ℝ) → ∀ t, t ≤ T → X t ω = Y t ω := by
    intro a
    let C : Ω → ℝ := ({ω | ‖J ω‖ ≤ (a : ℝ)} : Set Ω).indicator (fun _ => 1)
    have hset : MeasurableSet[F 0] {ω | ‖J ω‖ ≤ (a : ℝ)} :=
      measurableSet_le hJ.norm.measurable measurable_const
    have hC : StronglyMeasurable[F 0] C := stronglyMeasurable_const.indicator hset
    have hCb : ∀ ω, ‖C ω‖ ≤ (1 : ℝ≥0) := by
      intro ω
      by_cases hω : ‖J ω‖ ≤ (a : ℝ) <;> simp [C,hω]
    obtain ⟨M,hM⟩ := HamiltonianParameter.cutoffDrift_uniform_state_lipschitz (N := N) (p := p)
      β R hR (a : ℝ≥0)
    obtain ⟨K,hK⟩ := CutoffSDE.cutoffNoise_lipschitz N R hR
    have hb : ∀ᵐ ω ∂P, C ω ≠ 0 → ∀ t, t ≤ T → ∀ i,
        ‖hamiltonianDrift β (J ω) (X t ω) i - hamiltonianDrift β (J ω) (Y t ω) i‖ ≤
          (M : ℝ) * ‖X t ω - Y t ω‖ := by
      filter_upwards [hXb,hYb] with ω hx hy
      intro hc t ht i
      have hJa : ‖J ω‖ ≤ (a : ℝ≥0) := by
        by_contra hnot
        change ¬ ‖J ω‖ ≤ (a : ℝ) at hnot
        exact hc (by simp [C,hnot])
      rw [← CutoffSDE.cutoffDrift_eq β (J ω) R hR _ (hx t ht) i,
        ← CutoffSDE.cutoffDrift_eq β (J ω) R hR _ (hy t ht) i]
      have hi := ((CutoffSDE.coordinate_lipschitz i).comp (hM (J ω) hJa)).dist_le_mul
        (X t ω) (Y t ω)
      simpa only [Function.comp_def,CutoffSDE.cutoffDrift,dist_eq_norm,NNReal.coe_mul,
        NNReal.coe_one,one_mul] using hi
    have hsigma : ∀ᵐ ω ∂P, C ω ≠ 0 → ∀ t, t ≤ T → ∀ i j,
        ‖noiseColumn (X t ω) j i - noiseColumn (Y t ω) j i‖ ≤
          (K : ℝ) * ‖X t ω - Y t ω‖ := by
      filter_upwards [hXb,hYb] with ω hx hy
      intro _ t ht i j
      rw [← CutoffSDE.cutoffNoise_eq N R hR _ (hx t ht) i j,
        ← CutoffSDE.cutoffNoise_eq N R hR _ (hy t ht) i j]
      simpa only [dist_eq_norm] using (hK i j).dist_le_mul (X t ω) (Y t ω)
    have hzero := localized_strongSolutions_eq D
      (fun ω i x => hamiltonianDrift β (J ω) x i) (fun _ i j x => noiseColumn x j i)
      Z₀ X Y T hX hY R hXb hYb C hC 1 M K hCb hb hsigma
    filter_upwards [hzero] with ω hω
    intro hJa
    exact hω (by simp [C,hJa])
  have hall := ae_all_iff.mpr hlocal
  filter_upwards [hall] with ω hω
  obtain ⟨a,ha⟩ := exists_nat_ge ‖J ω‖
  exact hω a ha

/-- Common-path all-time uniqueness of actual random-disorder sphere
solutions, derived from finite-horizon uniqueness and integer horizons. -/
theorem physical_global_pathwise_uniqueness (D : BrownianDriver N P F) (β : ℝ)
    (J : Ω → FiniteModel.Disorder N p) (hJ : StronglyMeasurable[F 0] J)
    (Z₀ : Ω → State N) (X Y : ℝ≥0 → Ω → State N)
    (hX : ∀ T, IsRandomStrongSolutionOn D
      (fun ω i x => hamiltonianDrift β (J ω) x i) (fun _ i j x => noiseColumn x j i) Z₀ X T)
    (hY : ∀ T, IsRandomStrongSolutionOn D
      (fun ω i x => hamiltonianDrift β (J ω) x i) (fun _ i j x => noiseColumn x j i) Z₀ Y T)
    (hXs : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω))
    (hYs : ∀ᵐ ω ∂P, ∀ t, OnSphere (Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t, t ≤ (n : ℝ≥0) → X t ω = Y t ω := by
    apply ae_all_iff.mpr
    intro n
    exact physical_pathwise_uniqueness D β J hJ Z₀ X Y n (hX n) (hY n)
      (hXs.mono (fun ω h t _ => h t)) (hYs.mono (fun ω h t _ => h t))
  filter_upwards [hall] with ω hω
  intro t
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact hω n t hn

end SphericalAging.AnnealedPhysicalUniqueness
