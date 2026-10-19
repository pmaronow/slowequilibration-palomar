module
public import QuantitativePaper.VectorConvexity

@[expose] public section

/-! The actual terminal Hamiltonian as a continuous linear function of all
Gaussian disorder and field coordinates, and a joint Lipschitz bound for
every depth of the genuine vector recursion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

def energyLinear (n : ℕ) (σ : Configuration n) : Couplings n →L[ℝ] ℝ :=
  (1/Real.sqrt (n : ℝ)) • ∑ e : Edge n,
    (Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)) • ContinuousLinearMap.proj e

theorem energyLinear_apply (n : ℕ) (σ : Configuration n) (g : Couplings n) :
    energyLinear n σ g = energy n g σ := by
  unfold energyLinear energy Paper.skHamiltonian
  simp only [smul_apply,sum_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,zero_mul,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  ring

def fieldDotLinear {n : ℕ} (σ : Configuration n) : Field n →L[ℝ] ℝ :=
  ∑ i,Paper.spinSign (σ i) • EuclideanSpace.proj i

theorem fieldDotLinear_apply {n : ℕ} (σ : Configuration n) (x : Field n) :
    fieldDotLinear σ x = fieldDot x σ := by
  unfold fieldDotLinear fieldDot
  simp only [sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

def vectorTerminalLinear (n : ℕ) (β t : ℝ) (σ : Configuration n) :
    VectorParameter n →L[ℝ] ℝ :=
  (β*Real.sqrt t) •
    ((energyLinear n σ).comp ((ContinuousLinearMap.fst ℝ (Couplings n) ℝ).comp
      (ContinuousLinearMap.fst ℝ (Couplings n × ℝ) (Field n)))+
      (ContinuousLinearMap.snd ℝ (Couplings n) ℝ).comp
        (ContinuousLinearMap.fst ℝ (Couplings n × ℝ) (Field n)))+
    (fieldDotLinear σ).comp (ContinuousLinearMap.snd ℝ (Couplings n × ℝ) (Field n))

theorem vectorTerminalLinear_apply (n : ℕ) (β t : ℝ) (σ : Configuration n) (p : VectorParameter n) :
    vectorTerminalLinear n β t σ p = vectorTerminalExponent n β t p.1 p.2 σ := by
  simp only [vectorTerminalLinear,add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,
    energyLinear_apply,fieldDotLinear_apply,smul_eq_mul,vectorTerminalExponent]
  rfl

def vectorJointLipschitzConstant (n : ℕ) (β t : ℝ) : ℝ≥0 :=
  (∑ σ : Configuration n,‖vectorTerminalLinear n β t σ‖).toNNReal

theorem vectorTerminalExponent_direction_bound (n : ℕ) (β t : ℝ) (w : VectorParameter n)
    (σ : Configuration n) :
    |vectorTerminalExponent n β t w.1 w.2 σ| ≤ (vectorJointLipschitzConstant n β t : ℝ)*‖w‖ := by
  rw [←vectorTerminalLinear_apply,←Real.norm_eq_abs]
  apply (vectorTerminalLinear n β t σ).le_opNorm w |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold vectorJointLipschitzConstant
  rw [Real.coe_toNNReal _ (by positivity)]
  exact Finset.single_le_sum (f := fun σ => ‖vectorTerminalLinear n β t σ‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)

theorem vectorRecursion_joint_lipschitz {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    LipschitzWith (vectorJointLipschitzConstant n β t)
      (fun p : VectorParameter n => vectorRecursion s β t p.1 j p.2) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro p z
  let w := z-p
  let R := ((vectorJointLipschitzConstant n β t : ℝ)*‖w‖).toNNReal
  have hb (σ : Configuration n) : |vectorTerminalExponent n β t w.1 w.2 σ| ≤ (R : ℝ) := by
    rw [show (R : ℝ) = (vectorJointLipschitzConstant n β t : ℝ)*‖w‖ from Real.coe_toNNReal _ (by positivity)]
    exact vectorTerminalExponent_direction_bound n β t w σ
  let f := fun r : ℝ => vectorRecursion s β t (p.1+r • w.1) j (p.2+r • w.2)
  have hd (r : ℝ) := hasDerivAt_vectorRecursion_joint_line s β t p w j r
  have hLip : LipschitzWith R f := lipschitzWith_of_nnnorm_deriv_le
    (fun r => (hd r).differentiableAt) (fun r => by
      rw [←NNReal.coe_le_coe,coe_nnnorm,Real.norm_eq_abs,(hd r).deriv]
      exact abs_vectorObservableResponse_le s β t p.1 _ R hb j r p.2)
  have hh := hLip.dist_le_mul 0 1
  have hw : p+w = z := by dsimp [w];abel
  have hp : p.1+w.1 = z.1 := congrArg Prod.fst hw
  have hx : p.2+w.2 = z.2 := congrArg Prod.snd hw
  have hR : (R : ℝ) = (vectorJointLipschitzConstant n β t : ℝ)*‖w‖ :=
    Real.coe_toNNReal _ (by positivity)
  simpa [f,zero_smul,add_zero,one_smul,hp,hx,hR,w,dist_eq_norm,norm_sub_rev] using hh

end QuantitativePaper
