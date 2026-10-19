module

public import SphericalAging.PredictableLinearCoefficient

public section

/-! Genuine bounded random linear coefficient operators on vector L². -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.RandomLpCoefficient
open HardSphereDynamics
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K : ℝ≥0}

structure Coefficient (K : ℝ≥0) where
  value : Ω → (State N →L[ℝ] State N)
  measurable : AEStronglyMeasurable value (P)
  bound : ∀ᵐ q ∂P, ‖value q‖ ≤ K

theorem evaluation_measurable {K : ℝ≥0} (a : Coefficient (N := N) (P := P) K)
    (U : Lp (State N) 2 P) : AEStronglyMeasurable
      (fun q => a.value q ((U : Lp (State N) 2 (P)) q))
      (P) :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (a.measurable.prodMk (Lp.aestronglyMeasurable U))

theorem evaluation_memLp {K : ℝ≥0} (a : Coefficient (N := N) (P := P) K)
    (U : Lp (State N) 2 P) : MemLp
      (fun q => a.value q ((U : Lp (State N) 2 (P)) q))
      2 (P) := by
  apply (Lp.memLp (U : Lp (State N) 2 (P))).of_le_mul
    (evaluation_measurable a U) (c := (K : ℝ))
  filter_upwards [a.bound] with q hq
  exact (a.value q).le_of_opNorm_le hq _

@[expose] def apply (a : Coefficient (N := N) (P := P) K)
    (U : Lp (State N) 2 P) : Lp (State N) 2 P :=
  (evaluation_memLp a U).toLp _

theorem apply_coeFn (a : Coefficient (N := N) (P := P) K)
    (U : Lp (State N) 2 P) :
    (apply a U : Lp (State N) 2 (P)) =ᵐ[P]
      fun q => a.value q ((U : Lp (State N) 2 (P)) q) :=
  (evaluation_memLp a U).coeFn_toLp

theorem apply_add (a : Coefficient (N := N) (P := P) K)
    (U V : Lp (State N) 2 P) : apply a (U+V) = apply a U + apply a V := by
  apply Lp.ext
  filter_upwards [apply_coeFn a (U+V),apply_coeFn a U,apply_coeFn a V,
    Lp.coeFn_add (U : Lp (State N) 2 (P)) V,
    Lp.coeFn_add (apply a U : Lp (State N) 2 (P)) (apply a V)]
    with q hu hv hw hsum happ
  simpa only [hu,hv,hw,hsum,Pi.add_apply,map_add] using happ.symm

theorem apply_sub (a : Coefficient (N := N) (P := P) K)
    (U V : Lp (State N) 2 P) : apply a (U-V) = apply a U - apply a V := by
  apply Lp.ext
  filter_upwards [apply_coeFn a (U-V),apply_coeFn a U,apply_coeFn a V,
    Lp.coeFn_sub (U : Lp (State N) 2 (P)) V,
    Lp.coeFn_sub (apply a U : Lp (State N) 2 (P)) (apply a V)]
    with q hu hv hw hsum happ
  simpa only [hu,hv,hw,hsum,Pi.sub_apply,map_sub] using happ.symm

theorem apply_zero (a : Coefficient (N := N) (P := P) K) : apply a 0 = 0 := by
  have h := apply_sub a 0 0
  simpa only [sub_self] using h

theorem apply_smul (a : Coefficient (N := N) (P := P) K)
    (c : ℝ) (U : Lp (State N) 2 P) : apply a (c • U) = c • apply a U := by
  apply Lp.ext
  filter_upwards [apply_coeFn a (c • U),apply_coeFn a U,
    Lp.coeFn_smul c (U : Lp (State N) 2 (P)),
    Lp.coeFn_smul c (apply a U : Lp (State N) 2 (P))]
    with q hu hv hsum happ
  simpa only [hu,hv,hsum,Pi.smul_apply,map_smul] using happ.symm

theorem norm_apply_le (a : Coefficient (N := N) (P := P) K)
    (U : Lp (State N) 2 P) : ‖apply a U‖ ≤ (K : ℝ) * ‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [apply_coeFn a U,a.bound] with q hq hb
  change ‖(apply a U : Lp (State N) 2 (P)) q‖ ≤
    (K : ℝ) * ‖(U : Lp (State N) 2 (P)) q‖
  rw [hq]
  exact (a.value q).le_of_opNorm_le hb _

/-- True random bounded matrix multiplication is a continuous linear L² operator. -/
@[expose] def operator (a : Coefficient (N := N) (P := P) K) :
    Lp (State N) 2 P →L[ℝ] Lp (State N) 2 P :=
  LinearMap.mkContinuous
    { toFun := apply a
      map_add' := apply_add a
      map_smul' := apply_smul a }
    K (norm_apply_le a)

@[simp] theorem operator_apply (a : Coefficient (N := N) (P := P) K)
    (U : Lp (State N) 2 P) : operator a U=apply a U := rfl

end SphericalAging.RandomLpCoefficient
