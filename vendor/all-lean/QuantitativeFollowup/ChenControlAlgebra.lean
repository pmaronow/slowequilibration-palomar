module
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Tactic

@[expose] public section

/-! The signed-control convexity algebra in Chen's proof. These are actual
pointwise payoff inequalities. The separate Brownian variational representation
is needed to identify a control value with the normalized Gaussian log moment. -/
noncomputable section
open Set
namespace QuantitativeFollowup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def chenControlPayoff (F : E → ℝ) (b : E) (lam : ℝ) (u : E) : ℝ :=
  F (b+lam • u)-lam/2*‖u‖^2

theorem convexOn_chenControlPayoff_parameter (F : E → ℝ)
    (hF : ConvexOn ℝ univ F) (b u : E) :
    ConvexOn ℝ univ (fun lam => chenControlPayoff F b lam u) := by
  refine ⟨convex_univ,?_⟩
  intro lam0 _ lam1 _ a c ha hc hac
  have he : b+(a*lam0+c*lam1) • u=
      a • (b+lam0 • u)+c • (b+lam1 • u) := by
    calc
      _ = (a+c) • b+(a*lam0+c*lam1) • u := by rw [hac,one_smul]
      _ = _ := by module
  have hh := hF.2 (mem_univ (b+lam0 • u)) (mem_univ (b+lam1 • u)) ha hc hac
  simp only [smul_eq_mul] at hh ⊢
  unfold chenControlPayoff
  rw [he]
  nlinarith

def chenNegativeControlMix (a c lam0 lam1 : ℝ) (u0 u1 : E) : E :=
  (a*lam0/(a*lam0+c*lam1)) • u0+(c*lam1/(a*lam0+c*lam1)) • u1

theorem chen_negative_energy_mix (a c lam0 lam1 : ℝ) (u0 u1 : E)
    (ha : 0≤a) (hc : 0≤c) (hac : a+c=1) (hlam0 : lam0<0) (hlam1 : lam1<0) :
    -(a*lam0+c*lam1)*‖chenNegativeControlMix a c lam0 lam1 u0 u1‖^2 ≤
      -(a*lam0)*‖u0‖^2-(c*lam1)*‖u1‖^2 := by
  let lam := a*lam0+c*lam1
  have hlam : lam<0 := by
    dsimp [lam]
    have h0 := mul_le_mul_of_nonneg_left hlam0.le ha
    have h1 := mul_le_mul_of_nonneg_left hlam1.le hc
    rcases lt_or_eq_of_le ha with ha'|ha'
    · have h0' := mul_neg_of_pos_of_neg ha' hlam0
      linarith
    · have hc' : c=1 := by linarith
      rw [←ha',zero_mul,hc',one_mul,zero_add]
      exact hlam1
  let w0 := a*lam0/lam
  let w1 := c*lam1/lam
  have hw0 : 0≤w0 := div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hlam0.le) hlam.le
  have hw1 : 0≤w1 := div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc hlam1.le) hlam.le
  have hwsum : w0+w1=1 := by dsimp [w0,w1];rw [←add_div];exact div_self hlam.ne
  have hconv : ConvexOn ℝ univ (fun u : E => ‖u‖^2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have hh := hconv.2 (mem_univ u0) (mem_univ u1) hw0 hw1 hwsum
  simp only [smul_eq_mul] at hh
  have hc0 : -lam*w0=-(a*lam0) := by dsimp [w0];field_simp [hlam.ne]
  have hc1 : -lam*w1=-(c*lam1) := by dsimp [w1];field_simp [hlam.ne]
  have hmul := mul_le_mul_of_nonneg_left hh (neg_nonneg.mpr hlam.le)
  rw [mul_add,←mul_assoc,←mul_assoc,hc0,hc1] at hmul
  simpa [chenNegativeControlMix,w0,w1,lam,sub_eq_add_neg,neg_mul] using hmul

theorem chen_negative_payoff_mix (F : E → ℝ) (hF : ConvexOn ℝ univ F)
    (b : E) (a c lam0 lam1 : ℝ) (u0 u1 : E)
    (ha : 0≤a) (hc : 0≤c) (hac : a+c=1) (hlam0 : lam0<0) (hlam1 : lam1<0) :
    chenControlPayoff F b (a*lam0+c*lam1) (chenNegativeControlMix a c lam0 lam1 u0 u1) ≤
      a*chenControlPayoff F b lam0 u0+c*chenControlPayoff F b lam1 u1 := by
  let lam := a*lam0+c*lam1
  have hlam : lam<0 := by
    dsimp [lam]
    have h0 := mul_le_mul_of_nonneg_left hlam0.le ha
    have h1 := mul_le_mul_of_nonneg_left hlam1.le hc
    rcases lt_or_eq_of_le ha with ha'|ha'
    · linarith [mul_neg_of_pos_of_neg ha' hlam0]
    · have hc' : c=1 := by linarith
      rw [←ha',zero_mul,hc',one_mul,zero_add]
      exact hlam1
  have hc0 : lam*(a*lam0/lam)=a*lam0 := by field_simp [hlam.ne]
  have hc1 : lam*(c*lam1/lam)=c*lam1 := by field_simp [hlam.ne]
  have he : b+lam • chenNegativeControlMix a c lam0 lam1 u0 u1=
      a • (b+lam0 • u0)+c • (b+lam1 • u1) := by
    dsimp only [chenNegativeControlMix]
    change b+lam • ((a*lam0/lam) • u0+(c*lam1/lam) • u1)=_
    rw [smul_add,smul_smul,smul_smul,hc0,hc1]
    calc
      _ = (a+c) • b+(a*lam0) • u0+(c*lam1) • u1 := by rw [hac,one_smul,add_assoc]
      _ = _ := by module
  have hh := hF.2 (mem_univ (b+lam0 • u0)) (mem_univ (b+lam1 • u1)) ha hc hac
  rw [←he] at hh
  have henergy := chen_negative_energy_mix a c lam0 lam1 u0 u1 ha hc hac hlam0 hlam1
  simp only [smul_eq_mul] at hh
  unfold chenControlPayoff
  dsimp [lam] at hh
  nlinarith

end QuantitativeFollowup
