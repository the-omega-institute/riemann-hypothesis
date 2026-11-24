import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Absolute Laplace moments and signed window bounds -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Analytic.Laplace.GeneralLaplaceMoments

private def kernel (g : ℝ → ℝ) (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (g u : ℂ))

private theorem kernel_continuous {g : ℝ → ℝ} (hg : Continuous g) (k : ℕ) (s : ℂ) :
    Continuous (kernel g k s) := by
  unfold kernel
  have h := Complex.continuous_ofReal.comp hg
  exact (Complex.continuous_ofReal.neg.pow k).mul
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul h)

private theorem kernel_norm (g : ℝ → ℝ) (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel g k s u‖ = u ^ k * (Real.exp (-s.re * u) * |g u|) := by
  simp [kernel, norm_pow, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]

private theorem kernel_bound (g : ℝ → ℝ) (k : ℕ) {a d : ℝ} (hd : 0 < d) {s : ℂ} (hs : a + d ≤ s.re)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖kernel g k s u‖ ≤ (k.factorial : ℝ) / d ^ k * ‖kernel g 0 a u‖ := by
  have hp := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) k
  have hf : 0 < (k.factorial : ℝ) := by positivity
  have hdk : 0 < d ^ k := pow_pos hd _
  rw [mul_pow, div_le_iff₀ hf] at hp
  have huPow : u ^ k ≤ (k.factorial : ℝ) / d ^ k * Real.exp (d * u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
    simpa [mul_comm] using hp
  rw [kernel_norm g k s hu, kernel_norm g 0 a hu]
  simp only [Complex.ofReal_re, pow_zero, one_mul]
  calc
    _ ≤ ((k.factorial : ℝ) / d ^ k * Real.exp (d * u)) *
        (Real.exp (-s.re * u) * |g u|) :=
      mul_le_mul_of_nonneg_right huPow (by positivity)
    _ = ((k.factorial : ℝ) / d ^ k * Real.exp ((d - s.re) * u)) * |g u| := by
      rw [show (d - s.re) * u = d * u + (-s.re) * u by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      rw [← mul_assoc]
      gcongr
      linarith

variable {g : ℝ → ℝ} {σ₀ : ℝ}

private theorem kernel_integrable (hg : Continuous g)
    (hbase : ∀ a : ℝ, σ₀ < a → IntegrableOn (kernel g 0 (a : ℂ)) (Ioi 0))
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (kernel g k s) (Ioi 0) := by
  let d := (s.re - σ₀) / 3
  let a := σ₀ + d
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : σ₀ < a := by dsimp [a]; linarith
  have h : IntegrableOn (fun u => (k.factorial : ℝ) / d ^ k * ‖kernel g 0 a u‖) (Ioi 0) :=
    (hbase a ha).norm.const_mul _
  refine h.mono' (kernel_continuous hg k s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  exact kernel_bound g k hd (by dsimp [a,d]; linarith) (le_of_lt hu)

private theorem kernel_derivative (g : ℝ → ℝ) (k : ℕ) (s : ℂ) (u : ℝ) :
    HasDerivAt (fun z => kernel g k z u) (kernel g (k+1) s u) s := by
  unfold kernel
  have h := (((hasDerivAt_id s).neg.mul_const (u : ℂ)).cexp.mul_const (g u : ℂ)).const_mul
    ((-(u : ℂ)) ^ k)
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq, neg_one_mul, pow_succ]
  ring

private theorem integral_derivative (hg : Continuous g)
    (hbase : ∀ a : ℝ, σ₀ < a → IntegrableOn (kernel g 0 (a : ℂ)) (Ioi 0))
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    HasDerivAt (fun z => ∫ u : ℝ in Ioi 0, kernel g k z u)
      (∫ u : ℝ in Ioi 0, kernel g (k+1) s u) s := by
  let d := (s.re - σ₀) / 3
  let a := σ₀ + d
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : σ₀ < a := by dsimp [a]; linarith
  have hn : {z : ℂ | a + d < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [a,d]; linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) hn
    (Eventually.of_forall fun z => (kernel_continuous hg k z).aestronglyMeasurable)
    (kernel_integrable hg hbase k hs) (kernel_continuous hg (k+1) s).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu z hz
      exact kernel_bound g (k+1) hd (le_of_lt hz) (le_of_lt hu))
    ((hbase a ha).norm.const_mul ((k+1).factorial / d ^ (k+1) : ℝ))
    (Eventually.of_forall fun u z _ => kernel_derivative g k z u)).2

/-- Absolute Laplace convergence on an initial half-plane implies all logarithmic
moments and identifies them with the iterated derivatives of the transform. -/
theorem iterated_derivative_moment {F : ℂ → ℂ} (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (fun u : ℝ => (-(u : ℂ)) ^ k *
      (Complex.exp (-s * u) * (g u : ℂ))) (Ioi 0) ∧
    iteratedDeriv k F s = ∫ u : ℝ in Ioi 0, (-(u : ℂ)) ^ k *
      (Complex.exp (-s * u) * (g u : ℂ)) := by
  have hbase (a : ℝ) (ha : σ₀ < a) : IntegrableOn (kernel g 0 (a : ℂ)) (Ioi 0) := by
    unfold kernel
    simp only [pow_zero, one_mul]
    exact (hF (a : ℂ) (by simpa only [Complex.ofReal_re] using ha)).1
  refine ⟨kernel_integrable hg hbase k hs, ?_⟩
  change iteratedDeriv k F s = ∫ u : ℝ in Ioi 0, kernel g k s u
  induction k generalizing s with
  | zero =>
    simpa only [iteratedDeriv_zero, kernel, pow_zero, one_mul] using (hF s hs).2.symm
  | succ k ih =>
    have hopen : {z : ℂ | σ₀ < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have heq : iteratedDeriv k F =ᶠ[𝓝 s]
        (fun z => ∫ u : ℝ in Ioi 0, kernel g k z u) := by
      filter_upwards [hopen] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq, (integral_derivative hg hbase k hs).deriv]

private def weight (k : ℕ) (σ u : ℝ) : ℝ :=
  u ^ k * Real.exp (-σ * u) / k.factorial

private def normalizedDerivative (F : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k F s

private def complexMoment (g : ℝ → ℝ) (k : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  ((u : ℂ) ^ k / k.factorial) * (Complex.exp (-s * u) * (g u : ℂ))

variable {F : ℂ → ℂ}

private lemma normalizedDerivative_integral (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (complexMoment g k s) (Ioi 0) ∧
      normalizedDerivative F k s = ∫ u in Ioi 0, complexMoment g k s u := by
  have hm := iterated_derivative_moment hg hF k hs
  have hkernel :
      (fun u : ℝ => ((-1 : ℂ) ^ k / k.factorial) *
        ((-(u : ℂ)) ^ k * (Complex.exp (-s * u) * (g u : ℂ)))) = complexMoment g k s := by
    funext u
    have hpow : (-1 : ℂ) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
      rw [← mul_pow, neg_one_mul, neg_neg]
    unfold complexMoment
    calc
      _ = (((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) / k.factorial) *
          (Complex.exp (-s * u) * (g u : ℂ)) := by ring
      _ = _ := by rw [hpow]
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, hkernel] using hm.1.const_mul ((-1 : ℂ) ^ k / k.factorial)
  · rw [normalizedDerivative, hm.2, ← integral_const_mul, hkernel]

private lemma norm_complexMoment (g : ℝ → ℝ) (k : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖complexMoment g k s u‖ = |g u| * weight k s.re u := by
  simp [complexMoment, weight, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hu]
  ring

private lemma complexMoment_real (g : ℝ → ℝ) (k : ℕ) (σ u : ℝ) :
    complexMoment g k (σ : ℂ) u = ((g u * weight k σ u : ℝ) : ℂ) := by
  simp [complexMoment, weight, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div]
  ring

private lemma weight_nonneg (k : ℕ) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ weight k σ u := by unfold weight; positivity

private lemma weight_bound (k : ℕ) {σ α : ℝ} (hα : α < σ) {u : ℝ} (hu : 0 ≤ u) :
    weight k σ u ≤ (σ - α)⁻¹ ^ k * Real.exp (-α * u) := by
  let d := σ - α
  have hd : 0 < d := sub_pos.mpr hα
  have hp := Real.pow_div_factorial_le_exp (d * u) (mul_nonneg hd.le hu) k
  rw [mul_pow] at hp
  unfold weight
  calc
    _ = (d ^ k * u ^ k / k.factorial) * (d⁻¹ ^ k * Real.exp (-σ * u)) := by
      rw [div_mul_eq_mul_div, mul_assoc (d ^ k), mul_left_comm (u ^ k),
        ← mul_assoc (d ^ k), ← mul_pow, mul_inv_cancel₀ hd.ne', one_pow, one_mul]
    _ ≤ Real.exp (d * u) * (d⁻¹ ^ k * Real.exp (-σ * u)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add, show d * u + -σ * u = -α * u by dsimp [d]; ring]

/-- A paired moment bounds the prescribed sign of the remainder inside a log
window, with the absolute moment as the allowance outside the window. -/
theorem signed_window_moment_bound (hg : Continuous g)
    (hF : ∀ s : ℂ, σ₀ < s.re →
      IntegrableOn (fun u : ℝ => Complex.exp (-s * u) * (g u : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) * (g u : ℂ)) = F s)
    (k : ℕ) {p : ℂ} (hp : σ₀ < p.re)
    {a b α e : ℝ} (ha : 0 < a) (hab : a ≤ b) (hα : α < p.re)
    (he : e = 1 ∨ e = -1) :
    let D := fun s : ℂ =>
      ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k F s
    ‖D p‖ + e * (D (p.re : ℂ)).re ≤
      2 * (p.re - α)⁻¹ ^ k * (∫ u in a..b, max (e * g u) 0 * Real.exp (-α * u)) +
      2 * ∫ u in Ioi (0 : ℝ) \ Icc a b,
        |g u| * (u ^ k * Real.exp (-p.re * u) / k.factorial) := by
  let σ := p.re
  let A := Ioi (0 : ℝ)
  let W := Icc a b
  let K := weight k σ
  let f := fun u => max (e * g u) 0 * K u
  let absoluteMoment := fun u => |g u| * K u
  let G := fun u => max (e * g u) 0 * Real.exp (-α * u)
  have hWA : W ⊆ A := fun _ hu => ha.trans_le hu.1
  have hpMoment := normalizedDerivative_integral hg hF k hp
  have hrealMoment := normalizedDerivative_integral hg hF k (s := (σ : ℂ))
    (by simpa only [Complex.ofReal_re, σ] using hp)
  have hF : IntegrableOn absoluteMoment A := by
    apply (integrable_congr _).mp hpMoment.1.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_complexMoment g k p hu.le
  have hSigned : IntegrableOn (fun u => g u * K u) A := by
    have h := hrealMoment.1.re
    change IntegrableOn (fun u => (complexMoment g k (σ : ℂ) u).re) A at h
    simpa only [complexMoment_real, Complex.ofReal_re, K] using h
  have hePoint (u : ℝ) : |g u| * K u + e * (g u * K u) = 2 * f u := by
    have h : |g u| + e * g u = 2 * max (e * g u) 0 := by
      rcases he with rfl | rfl
      · by_cases h : 0 ≤ g u
        · simp [abs_of_nonneg h, max_eq_left h]; ring
        · have hn := le_of_not_ge h
          simp [abs_of_nonpos hn, max_eq_right hn]
      · by_cases h : 0 ≤ g u
        · simp [abs_of_nonneg h, max_eq_right (neg_nonpos.mpr h)]
        · have hn := le_of_not_ge h
          simp [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]; ring
    dsimp only [f]
    calc
      _ = (|g u| + e * g u) * K u := by ring
      _ = _ := by rw [h]; ring
  have hf : IntegrableOn f A := by
    have hf' := (hF.add (hSigned.const_mul e)).const_mul (1 / 2 : ℝ)
    refine hf'.congr (ae_of_all _ fun u => ?_)
    symm
    change f u = (1 / 2) * (|g u| * K u + e * (g u * K u))
    rw [hePoint]
    ring
  have hnorm : ‖normalizedDerivative F k p‖ ≤ ∫ u in A, absoluteMoment u := by
    rw [hpMoment.2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_complexMoment g k p hu.le
  have hre : (normalizedDerivative F k (σ : ℂ)).re = ∫ u in A, g u * K u := by
    rw [hrealMoment.2]
    simp only [complexMoment_real, integral_complex_ofReal, Complex.ofReal_re, A, K]
  have hpair : ‖normalizedDerivative F k p‖ + e * (normalizedDerivative F k (σ : ℂ)).re ≤
      2 * ∫ u in A, f u := by
    rw [hre, ← integral_const_mul e]
    refine (add_le_add_left hnorm _).trans_eq ?_
    rw [← integral_add hF (hSigned.const_mul e), ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hePoint)
  have hsplit : (∫ u in A, f u) = (∫ u in W, f u) + ∫ u in A \ W, f u := by
    rw [setIntegral_sdiff measurableSet_Icc hf hWA]
    ring
  have hG : IntegrableOn G W := by
    have hcont : Continuous G :=
      ((hg.const_mul e).max continuous_const).mul (by fun_prop)
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hwindow : (∫ u in W, f u) ≤ (σ - α)⁻¹ ^ k * ∫ u in a..b, G u := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_mono_on (hf.mono_set hWA) (hG.const_mul _) measurableSet_Icc ?_
    intro u hu
    have hu0 : 0 ≤ u := (show 0 < u from hWA hu).le
    change max (e * g u) 0 * K u ≤ (σ - α)⁻¹ ^ k * (max (e * g u) 0 * Real.exp (-α * u))
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (weight_bound k hα hu0) (le_max_right _ _)
  have htail : (∫ u in A \ W, f u) ≤ ∫ u in A \ W, absoluteMoment u := by
    refine setIntegral_mono_on (hf.mono_set sdiff_subset) (hF.mono_set sdiff_subset)
      (measurableSet_Ioi.diff measurableSet_Icc) ?_
    intro u hu
    have hmajor : max (e * g u) 0 ≤ |g u| := by
      apply max_le _ (abs_nonneg _)
      rcases he with rfl | rfl
      · simpa using le_abs_self (g u)
      · simpa using neg_le_abs (g u)
    exact mul_le_mul_of_nonneg_right hmajor (weight_nonneg k σ hu.1.le)
  change ‖normalizedDerivative F k p‖ + e * (normalizedDerivative F k (σ : ℂ)).re ≤
    2 * (σ - α)⁻¹ ^ k * (∫ u in a..b, G u) + 2 * ∫ u in A \ W, absoluteMoment u
  rw [hsplit, mul_add] at hpair
  exact hpair.trans (by linarith only [hwindow, htail])


#print axioms iterated_derivative_moment
#print axioms signed_window_moment_bound

end D5.S3.Analytic.Laplace.GeneralLaplaceMoments
