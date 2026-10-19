module

public import SphericalAging.GlobalHamiltonianParameter

public section

/-! Genuine joint parameter dependence of the nonlinear coefficient classes.
All classes are the actual finite-time predictable coefficients used by the
Hamiltonian Picard equation; coefficient estimates come from the concrete
cutoff polynomial model.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianCoefficientDependence
open HardSphereDynamics PredictableItoTime PredictableDriftTime LocalSDE
open HamiltonianParameter HamiltonianPicardDependence GlobalHamiltonianParameter
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual nonlinear drift coefficient class for bounded disorder. -/
@[expose] def boundedDriftClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (i : Fin N) (q : BoundedDisorder N p A × State N) : PredictableProcessL2 F P :=
  predictableCoefficient (drift_family_lipschitz β R hR A q.1 i)
    (hamiltonianClass D β R hR A T q) T

lemma boundedDriftClass_lipschitz (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (A T : ℝ≥0) (i : Fin N) : ∃ K : ℝ≥0, LipschitzWith K (boundedDriftClass (p := p) D β R hR A T i) := by
  obtain ⟨K,hK⟩ := hamiltonianClass_lipschitz (p := p) D β R hR A T
  obtain ⟨C,hC⟩ := cutoffDrift_disorder_lipschitz (N := N) (p := p) β R hR
  let L : ℝ≥0 := driftBound (N := N) (p := p) β R hR A*K+C*PicardDependence.initialScale (P := P) T
  refine ⟨L,LipschitzWith.of_dist_le_mul (fun q r => ?_)⟩
  let U := hamiltonianClass D β R hR A T q
  let V := hamiltonianClass D β R hR A T r
  let middle := predictableCoefficient (drift_family_lipschitz β R hR A q.1 i) V T
  have hfirst : dist (boundedDriftClass D β R hR A T i q) middle ≤
      (driftBound (N := N) (p := p) β R hR A : ℝ)*(K : ℝ)*dist q r := by
    simp only [dist_eq_norm]
    exact (norm_predictableCoefficient_sub_le (drift_family_lipschitz β R hR A q.1 i) U V T).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hK.dist_le_mul q r)
        (driftBound (N := N) (p := p) β R hR A).coe_nonneg) |>.trans_eq (by ring)
  have hpoint : ∀ x, ‖CutoffSDE.cutoffDrift β q.1.1 R hR i x-CutoffSDE.cutoffDrift β r.1.1 R hR i x‖ ≤
      (C : ℝ)*‖q.1.1-r.1.1‖ := by
    intro x
    change ‖(cutoffCoefficient R hR (hamiltonianDrift β q.1.1) x) i-
      (cutoffCoefficient R hR (hamiltonianDrift β r.1.1) x) i‖ ≤ _
    rw [← PiLp.sub_apply]
    exact (PiLp.norm_apply_le _ i).trans (hC _ _ x)
  have hsecond : dist middle (boundedDriftClass D β R hR A T i r) ≤
      (C : ℝ)*(PicardDependence.initialScale (P := P) T : ℝ)*dist q r := by
    have hh := coefficient_family_sub_norm_bound
      (drift_family_lipschitz β R hR A q.1 i) (drift_family_lipschitz β R hR A r.1 i)
      V T ((C : ℝ)*‖q.1.1-r.1.1‖) (mul_nonneg C.coe_nonneg (norm_nonneg _)) hpoint
    have hdist : ‖q.1.1-r.1.1‖ ≤ dist q r := by
      simpa only [Subtype.dist_eq,dist_eq_norm] using
        (show dist q.1 r.1 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_left _ _)
    change dist middle _ ≤ _
    rw [dist_eq_norm]
    calc
      _ ≤ (C : ℝ)*‖q.1.1-r.1.1‖*(PicardDependence.initialScale (P := P) T : ℝ) := hh
      _ ≤ (C : ℝ)*dist q r*(PicardDependence.initialScale (P := P) T : ℝ) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ dist (boundedDriftClass D β R hR A T i q) middle+
        dist middle (boundedDriftClass D β R hR A T i r) := dist_triangle _ _ _
    _ ≤ (driftBound (N := N) (p := p) β R hR A : ℝ)*K*dist q r+
        (C : ℝ)*(PicardDependence.initialScale (P := P) T : ℝ)*dist q r := add_le_add hfirst hsecond
    _ = (L : ℝ)*dist q r := by dsimp [L]; ring

/-- Actual nonlinear noise coefficient class for bounded disorder. -/
@[expose] def boundedNoiseClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (i j : Fin N) (q : BoundedDisorder N p A × State N) : PredictableProcessL2 F P :=
  predictableCoefficient (noise_family_lipschitz N R hR i j) (hamiltonianClass D β R hR A T q) T

lemma boundedNoiseClass_lipschitz (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (A T : ℝ≥0) (i j : Fin N) : ∃ K : ℝ≥0, LipschitzWith K (boundedNoiseClass (p := p) D β R hR A T i j) := by
  obtain ⟨K,hK⟩ := hamiltonianClass_lipschitz (p := p) D β R hR A T
  have hc : LipschitzWith (noiseBound N R hR)
      (fun U : PredictableStateL2 N F P => predictableCoefficient (noise_family_lipschitz N R hR i j) U T) := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simpa only [dist_eq_norm] using norm_predictableCoefficient_sub_le (noise_family_lipschitz N R hR i j) U V T
  exact ⟨noiseBound N R hR*K,hc.comp hK⟩

/-- Actual nonlinear drift coefficient class on unrestricted disorder. -/
@[expose] def driftClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (i : Fin N) (q : FiniteModel.Disorder N p × State N) : PredictableProcessL2 F P :=
  boundedDriftClass D β R hR (‖q.1‖₊+1) T i (⟨q.1,by simp⟩,q.2)

lemma driftClass_eq_bounded (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (i : Fin N) (J : FiniteModel.Disorder N p) (hA : ‖J‖ ≤ A) (x : State N) :
    driftClass D β R hR T i (J,x) = boundedDriftClass D β R hR A T i (⟨J,hA⟩,x) := by
  unfold driftClass boundedDriftClass
  rw [hamiltonianClass_bound_independent D β R hR _ A T J _ hA x]
  exact predictableCoefficient_bound_independent _ _ _ _

private lemma continuous_of_bounded_lipschitz {V : Type*} [PseudoMetricSpace V]
    (f : FiniteModel.Disorder N p × State N → V)
    (fA : (A : ℝ≥0) → BoundedDisorder N p A × State N → V)
    (hA : ∀ A, ∃ K : ℝ≥0, LipschitzWith K (fA A))
    (he : ∀ (A : ℝ≥0) J (hJ : ‖J‖ ≤ A) x, f (J,x)=fA A (⟨J,hJ⟩,x)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let A : ℝ≥0 := ‖q.1‖₊+1
  have hqA : ‖q.1‖ ≤ A := by dsimp [A]; simp
  obtain ⟨K,hK⟩ := hA A
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 (ε/((K : ℝ)+1)),lt_min (by norm_num) (div_pos hε (by positivity)),?_⟩
  intro r hr
  have hr1 := hr.trans_le (min_le_left _ _)
  have hJdist : dist r.1 q.1 ≤ dist r q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hrA : ‖r.1‖ ≤ A := by
    have hnorm := norm_le_norm_add_norm_sub q.1 r.1
    rw [← dist_eq_norm,dist_comm q.1 r.1] at hnorm
    change ‖r.1‖ ≤ ‖q.1‖+1
    linarith
  rw [he A r.1 hrA r.2,he A q.1 hqA q.2]
  have hd : dist ((⟨r.1,hrA⟩,r.2) : BoundedDisorder N p A × State N)
      ((⟨q.1,hqA⟩,q.2) : BoundedDisorder N p A × State N) = dist r q := by
    simp only [Prod.dist_eq,Subtype.dist_eq]
  calc
    _ ≤ (K : ℝ)*dist r q := by simpa only [hd] using hK.dist_le_mul (⟨r.1,hrA⟩,r.2) (⟨q.1,hqA⟩,q.2)
    _ ≤ ((K : ℝ)+1)*dist r q := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by
      have hm := (lt_div_iff₀ (by positivity : (0 : ℝ)<(K : ℝ)+1)).mp (hr.trans_le (min_le_right _ _))
      simpa only [mul_comm] using hm

lemma driftClass_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T : ℝ≥0) (i : Fin N) : Continuous (driftClass (p := p) D β R hR T i) :=
  continuous_of_bounded_lipschitz _ (fun A => boundedDriftClass D β R hR A T i)
    (fun A => boundedDriftClass_lipschitz D β R hR A T i)
    (fun A J hJ x => driftClass_eq_bounded D β R hR A T i J hJ x)

/-- Actual unrestricted-disorder noise class. -/
@[expose] def noiseClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (i j : Fin N) (q : FiniteModel.Disorder N p × State N) : PredictableProcessL2 F P :=
  predictableCoefficient (noise_family_lipschitz N R hR i j) (globalClass D β R hR T q) T

lemma noiseClass_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T : ℝ≥0) (i j : Fin N) : Continuous (noiseClass (p := p) D β R hR T i j) := by
  have hc : LipschitzWith (noiseBound N R hR)
      (fun U : PredictableStateL2 N F P => predictableCoefficient (noise_family_lipschitz N R hR i j) U T) := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simpa only [dist_eq_norm] using norm_predictableCoefficient_sub_le (noise_family_lipschitz N R hR i j) U V T
  exact hc.continuous.comp (globalClass_continuous D β R hR T)

end SphericalAging.HamiltonianCoefficientDependence
