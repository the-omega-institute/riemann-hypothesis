import Formalism.StatementOC
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData
import Verification.PairedLaplacePoleWindow
import Verification.EqualRadiusZeroDisks
import Verification.RightHalfStripRiemannReduction

/-! The pure-zeta transform from Alpöge's pinned source supplies the poles.
The paired-disk argument gives both signs of oscillation for the actual Gz. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Set Topology
open D5.S3.Analytic.Laplace
open D5.S3.Weil.ZetaBridge

namespace PureZetaGammaBridge

private def chi : DirichletCharacter ℂ 1 := 1

private lemma chi_apply (n : ℕ) : chi n = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

private lemma ramp_real (x : ℝ) :
    Deduction.ramp (fun _ => 1) x = (Formalism.Sz x : ℂ) := by
  have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.range (⌊x⌋₊ + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  unfold Deduction.ramp Formalism.Sz
  push_cast
  calc
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * 1 *
        ((max (x / n - 1) 0 : ℝ) : ℂ) := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnot
      have hn0 : n = 0 := by
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hnot
        omega
      subst n
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have ⟨hn1, hnF⟩ := Finset.mem_Icc.mp hn
      have hx : 0 ≤ x := by
        by_contra! hx
        rw [Nat.floor_eq_zero.mpr (hx.trans zero_lt_one)] at hnF
        omega
      have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr hnF).trans (Nat.floor_le hx)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [max_eq_left (sub_nonneg.mpr ((one_le_div hn0).mpr hnx)), mul_one]
      push_cast
      ring

private lemma chi_remainder (x : ℝ) : Deduction.Gchi chi x = (Formalism.Gz x : ℂ) := by
  unfold Deduction.Gchi
  rw [if_pos (show chi = 1 from rfl)]
  simp only [chi_apply, ramp_real, Formalism.Gz, Complex.ofReal_add, Complex.ofReal_sub]

private lemma continuous_ramp_at {x : ℝ} (hx : 0 < x) :
    ContinuousAt (Deduction.ramp (fun _ => 1)) x := by
  let N : ℕ := ⌈x + 1⌉₊ + 1
  have hxN : x < (N : ℝ) := by
    have h := Nat.le_ceil (x + 1)
    dsimp [N]
    push_cast
    linarith
  let f (n : ℕ) (y : ℝ) : ℂ :=
    (ArithmeticFunction.vonMangoldt n : ℂ) * 1 * ((max (y / n - 1) 0 : ℝ) : ℂ)
  have heq : Deduction.ramp (fun _ => 1) =ᶠ[𝓝 x] fun y => ∑ n ∈ Finset.range N, f n y := by
    filter_upwards [Ioo_mem_nhds hx hxN] with y hy
    unfold Deduction.ramp
    change ∑ n ∈ Finset.range (⌊y⌋₊ + 1), f n y = ∑ n ∈ Finset.range N, f n y
    have hfloor : ⌊y⌋₊ < N := (Nat.floor_lt hy.1.le).2 hy.2
    apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_of_lt hfloor))
    intro n _ hn
    have hle : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hyn : y < n := (Nat.lt_floor_add_one y).trans_le (by exact_mod_cast hle)
    simp [f, max_eq_right (sub_nonpos.mpr ((div_lt_one hn0).mpr hyn).le)]
  have hc : Continuous (fun y : ℝ => ∑ n ∈ Finset.range N, f n y) := by
    apply continuous_finsetSum
    intro n _
    unfold f
    fun_prop
  exact hc.continuousAt.congr heq.symm

private lemma continuous_log_remainder : Continuous fun u : ℝ => Formalism.Gz (Real.exp u) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hr := (continuous_ramp_at (Real.exp_pos u)).comp Real.continuous_exp.continuousAt
  have hr' : ContinuousAt (fun v : ℝ => Formalism.Sz (Real.exp v)) u := by
    have he (v : ℝ) := congrArg Complex.re (ramp_real (Real.exp v))
    simp only [Complex.ofReal_re] at he
    exact (Complex.continuous_re.continuousAt.comp hr).congr
      (Filter.Eventually.of_forall he)
  have hl : ContinuousAt (fun v : ℝ => Real.exp v * Real.log (Real.exp v)) u := by
    simp only [Real.log_exp]
    fun_prop
  exact (hr'.sub hl).add (by fun_prop)

/-- A right-half-strip zero forces positive and negative excursions beyond
`C * x ^ α` in every sufficiently late power window. -/
theorem signed_peaks {z : ℂ} (hz : riemannZeta z = 0) {α b C : ℝ}
    (hα : (1 / 2 : ℝ) ≤ α) (hβ : α < z.re) (hb : 1 < b) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ e : ℝ, e = 1 ∨ e = -1 → ∃ u ∈ Icc T (b*T),
      C * Real.exp (α*u) < e * Formalism.Gz (Real.exp u) := by
  obtain ⟨h, hh, hhb⟩ := exists_between hb
  let δ := (z.re - α) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hβ)
  have hδ' : δ < z.re - 1/2 := by dsimp [δ]; linarith
  obtain ⟨σ, hσ, htilt, hL, hR⟩ :=
    ((eventually_gt_atTop (2 : ℝ)).and ((CriticalGammaWindow.adjustable_window_off_mass hh hhb).1 0)).exists
  obtain ⟨p, ρ, r, hp, hρ, hd, hdr, hr, hre, hcomplex⟩ :=
    EqualRadiusZeroDisks.equal_radius_zero_disks hz hσ hδ hδ'
  have hd' : 0 < ‖p-ρ‖ := by simpa only [dist_eq_norm] using hd
  have hdr' : ‖p-ρ‖ < r := by simpa only [dist_eq_norm] using hdr
  have hρb : ρ ∈ Metric.closedBall p r := Metric.mem_closedBall.mpr (by rw [dist_comm]; exact hdr.le)
  have hne (w : ℂ) (hw : 1/2 < w.re) : w ≠ 0 := by rintro rfl; norm_num at hw
  have hρ0 := hne ρ (hcomplex ρ hρb).1
  have hρ1 : ρ ≠ 1 := fun he => riemannZeta_ne_zero_of_one_le_re (by simp [he]) hρ
  obtain ⟨F, hFF, hreg, hger, _⟩ := Deduction.poleData_char chi (Or.inl rfl)
  simp only [DirichletCharacter.LFunction_modOne_eq] at hreg hger
  obtain ⟨m, hm, H, hH, hprincipal⟩ := hger ρ hρ0
  have hm0 : m ≠ 0 := fun h => (hm.mp h) hρ
  have hc : (m : ℂ) * (-1 / (ρ * (ρ - 1))) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hm0)
      (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)))
  obtain ⟨M, hM⟩ := Deduction.Gchi_growth chi
  have hM' (u : ℝ) (hu : 0 ≤ u) : |Formalism.Gz (Real.exp u)| ≤ M * Real.exp (2*u) := by
    have hg := hM (Real.exp u) (Real.one_le_exp hu)
    rw [chi_remainder, Complex.norm_real, Real.norm_eq_abs] at hg
    rw [show Real.exp (2*u) = (Real.exp u) ^ 2 by rw [two_mul, Real.exp_add, pow_two]]
    exact hg
  have hM0 : 0 ≤ M := by simpa using (abs_nonneg _).trans (hM' 0 le_rfl)
  have hF (s : ℂ) (hs : 2 < s.re) :
      IntegrableOn (fun u : ℝ => Complex.exp (-s*u) * (Formalism.Gz (Real.exp u) : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, Complex.exp (-s*u) * (Formalism.Gz (Real.exp u) : ℂ)) = F s := by
    simpa only [chi_remainder, mul_comm] using
      And.intro (Deduction.poleData_integrable chi s hs) (hFF s hs).symm
  have hA (s : ℂ) (hs : s ∈ Metric.closedBall p r) (hsρ : s ≠ ρ) : AnalyticAt ℂ F s :=
    hreg s (hne s (hcomplex s hs).1) (fun he => hsρ ((hcomplex s hs).2 he))
  have hB : AnalyticOnNhd ℂ F (Metric.closedBall (p.re : ℂ) r) := by
    rw [hp]
    exact fun s hs => hreg s (hne s (hre s hs).1) (hre s hs).2
  have hgap : ‖p-ρ‖ < p.re - α := by rw [hp]; dsimp [δ] at hr; linarith
  exact PairedLaplacePoleWindow.signed_peaks_of_paired_disks
    continuous_log_remainder hF hM' hM0 (by rwa [hp]) (by rw [hp]; linarith)
    (by linarith) hc hd' hdr' hgap hA hB hH hprincipal hh hhb
    (by rwa [hp]) (by rw [hp]; exact hL.le) (by rw [hp]; exact hR.le) hC

/-- The independent analytic implication from the literal public window bound. -/
theorem rh_of_pure_zeta_windows
    (windows : ∀ κ : ℝ, 0 < κ → ∀ R : ℝ, ∃ Y : ℝ, max R 2 ≤ Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) → Formalism.Gz x ≤ x ^ (1 / 2 + κ)) :
    RiemannHypothesis := by
  apply RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro z hz hβ hβ1
  let κ := (z.re - (1/2 : ℝ)) / 2
  have hk : 0 < κ := half_pos (sub_pos.mpr hβ)
  have hα : (1/2 : ℝ) + κ < z.re := by dsimp [κ]; linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (signed_peaks hz (α := (1/2 : ℝ) + κ) (b := 3/2) (C := 1)
      (by linarith) hα (by norm_num) (by norm_num))
  obtain ⟨Y, hY, hW⟩ := windows κ hk (Real.exp T)
  have hY0 : 0 < Y := (Real.exp_pos T).trans_le ((le_max_left _ _).trans hY)
  have hTY : T ≤ Real.log Y := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hY0]
    exact (le_max_left _ _).trans hY
  obtain ⟨u, hu, hpeak⟩ := hT (Real.log Y) hTY 1 (Or.inl rfl)
  have hleft : Y ≤ Real.exp u := by rw [← Real.exp_log hY0]; exact Real.exp_le_exp.mpr hu.1
  have hright : Real.exp u ≤ Y ^ (3/2 : ℝ) := by
    rw [Real.rpow_def_of_pos hY0, mul_comm]
    exact Real.exp_le_exp.mpr hu.2
  have hle := hW (Real.exp u) hleft hright
  rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm] at hle
  simp only [one_mul] at hpeak
  exact (not_lt_of_ge hle) hpeak

#print axioms signed_peaks
#print axioms rh_of_pure_zeta_windows

end PureZetaGammaBridge
