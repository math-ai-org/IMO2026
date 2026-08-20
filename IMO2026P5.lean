import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace IMO2026P5

abbrev PositiveReal : Type := {x : ℝ // 0 < x}

def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    ((f x : ℝ) + (y : ℝ)) / 2 ≤
        Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ∧
      Real.sqrt ((x : ℝ) * (f y : ℝ)) ≤
        ((f x : ℝ) + (y : ℝ)) / 2

abbrev answer : Set (PositiveReal → PositiveReal) :=
  {f | ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c}

private lemma rms_am_two (x y : ℝ) :
    (x + y) / 2 ≤ Real.sqrt ((x ^ 2 + y ^ 2) / 2) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (x - y)]

private lemma sqrt_mul_le_arithMean {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  have hs : Real.sqrt (x * y) ^ 2 = x * y :=
    Real.sq_sqrt (mul_nonneg hx hy)
  have htwo : 2 * Real.sqrt (x * y) ≤ x + y :=
    two_mul_le_add_of_sq_eq_mul hx hy hs
  linarith

private lemma translation_admissible
    (f : PositiveReal → PositiveReal) (c : ℝ)
    (hf : ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c) :
    IsAdmissible f := by
  intro x y
  have hsum : (f x : ℝ) + (y : ℝ) = (x : ℝ) + (f y : ℝ) := by
    rw [hf x, hf y]
    ring
  constructor
  · rw [hsum]
    exact rms_am_two (x : ℝ) (f y : ℝ)
  · rw [hsum]
    exact sqrt_mul_le_arithMean x.property.le (f y).property.le

/-- Admissibility forces the second iterate of `f` to satisfy a linear recurrence. -/
private theorem second_iterate_eq (f : PositiveReal → PositiveReal) (hf : IsAdmissible f)
    (t : PositiveReal) :
    (f (f t) : ℝ) = 2 * (f t : ℝ) - (t : ℝ) := by
  have hsqrt_sq : Real.sqrt ((f t : ℝ) ^ 2) = (f t : ℝ) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (f t).property]
  have hupper := (hf (f t) t).1
  have hlower := (hf (f t) t).2
  have hadd_sq : (((f t : ℝ) ^ 2 + (f t : ℝ) ^ 2) / 2) = (f t : ℝ) ^ 2 := by
    ring
  have hmul_sq : (f t : ℝ) * (f t : ℝ) = (f t : ℝ) ^ 2 := by
    ring
  rw [hadd_sq, hsqrt_sq] at hupper
  rw [hmul_sq, hsqrt_sq] at hlower
  linarith

/-- Every finite iterate lies on the arithmetic progression starting at `t`
with common difference `f t - t`. -/
private theorem iterate_eq_arithmetic_progression (f : PositiveReal → PositiveReal)
    (hf : IsAdmissible f) (n : ℕ) (t : PositiveReal) :
    ((f^[n]) t : ℝ) = (t : ℝ) + (n : ℝ) * ((f t : ℝ) - (t : ℝ)) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (f t), second_iterate_eq f hf t]
      push_cast
      ring

/-- The common difference of the iterate progression is nonnegative. -/
private theorem sub_nonneg_of_admissible (f : PositiveReal → PositiveReal)
    (hf : IsAdmissible f) (t : PositiveReal) :
    0 ≤ (f t : ℝ) - (t : ℝ) := by
  by_contra hnonneg
  have hdiff : (f t : ℝ) - (t : ℝ) < 0 := lt_of_not_ge hnonneg
  have hstep : 0 < -((f t : ℝ) - (t : ℝ)) := neg_pos.mpr hdiff
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / -((f t : ℝ) - (t : ℝ)))
  have hn' : (t : ℝ) < (n : ℝ) * -((f t : ℝ) - (t : ℝ)) :=
    (div_lt_iff₀ hstep).mp hn
  have hpositive := ((f^[n]) t).property
  rw [iterate_eq_arithmetic_progression f hf n t] at hpositive
  nlinarith

variable (f : PositiveReal → PositiveReal)

/-- Safe squaring of the upper admissibility inequality at `x = f a`, `y = b`. -/
private lemma upper_square_at_iterate
    (upper : ∀ x y : PositiveReal,
      ((f x : ℝ) + (y : ℝ)) / 2 ≤
        Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2))
    (a b : PositiveReal) :
    (((f (f a) : ℝ) + (b : ℝ)) / 2) ^ 2 ≤
      ((f a : ℝ) ^ 2 + (f b : ℝ) ^ 2) / 2 := by
  have h := upper (f a) b
  have hfa : 0 < (f (f a) : ℝ) := (f (f a)).property
  have hb : 0 < (b : ℝ) := b.property
  have hleft : 0 ≤ ((f (f a) : ℝ) + (b : ℝ)) / 2 := by positivity
  have hradicand : 0 ≤ ((f a : ℝ) ^ 2 + (f b : ℝ) ^ 2) / 2 := by positivity
  have hright : 0 ≤ Real.sqrt (((f a : ℝ) ^ 2 + (f b : ℝ) ^ 2) / 2) :=
    Real.sqrt_nonneg _
  calc
    (((f (f a) : ℝ) + (b : ℝ)) / 2) ^ 2 ≤
        (Real.sqrt (((f a : ℝ) ^ 2 + (f b : ℝ) ^ 2) / 2)) ^ 2 := by
      nlinarith
    _ = ((f a : ℝ) ^ 2 + (f b : ℝ) ^ 2) / 2 :=
      Real.sq_sqrt hradicand

/-- Denominator-free lower bound for the increment of `t ↦ f t - t`. -/
private lemma pairwise_lower
    (upper : ∀ x y : PositiveReal,
      ((f x : ℝ) + (y : ℝ)) / 2 ≤
        Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2))
    (iterate : ∀ t : PositiveReal, (f (f t) : ℝ) = 2 * (f t : ℝ) - t)
    (a b : PositiveReal) :
    -((b : ℝ) - (a : ℝ)) ^ 2 ≤
      4 * (f b : ℝ) *
        (((f b : ℝ) - (b : ℝ)) - ((f a : ℝ) - (a : ℝ))) := by
  have hsq := upper_square_at_iterate f upper a b
  rw [iterate a] at hsq
  nlinarith [sq_nonneg
    (((f b : ℝ) - (b : ℝ)) - ((f a : ℝ) - (a : ℝ)))]

/-- The swapped form of `pairwise_lower`, written as an upper bound. -/
private lemma pairwise_upper
    (upper : ∀ x y : PositiveReal,
      ((f x : ℝ) + (y : ℝ)) / 2 ≤
        Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2))
    (iterate : ∀ t : PositiveReal, (f (f t) : ℝ) = 2 * (f t : ℝ) - t)
    (a b : PositiveReal) :
    4 * (f a : ℝ) *
        (((f b : ℝ) - (b : ℝ)) - ((f a : ℝ) - (a : ℝ))) ≤
      ((b : ℝ) - (a : ℝ)) ^ 2 := by
  have h := pairwise_lower f upper iterate b a
  nlinarith

/-- A real number bounded in absolute value by `C / n` for every positive natural
number `n` is zero. -/
private theorem eq_zero_of_abs_le_div_nat (x C : ℝ)
    (h : ∀ n : ℕ, 0 < n → |x| ≤ C / n) : x = 0 := by
  by_contra hx
  have hxabs : 0 < |x| := abs_pos.mpr hx
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C / |x|) 0)
  have hlarge : C / |x| < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnreal : 0 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < n := by exact_mod_cast hnreal
  have hbound := h n hnpos
  have hcontra : C / (n : ℝ) < |x| := by
    rw [div_lt_iff₀ hnreal]
    have := (div_lt_iff₀ hxabs).mp hlarge
    nlinarith
  exact (not_lt_of_ge hbound) hcontra

/-- Two real numbers are equal if their difference is bounded by `C / n` in
absolute value for every positive natural number `n`. -/
private theorem eq_of_abs_sub_le_div_nat (x y C : ℝ)
    (h : ∀ n : ℕ, 0 < n → |x - y| ≤ C / n) : x = y := by
  exact sub_eq_zero.mp (eq_zero_of_abs_le_div_nat (x - y) C h)

private theorem eq_of_ordered_pair_bounds (D F : ℝ → ℝ)
    (hF : ∀ x : ℝ, 0 < x → x ≤ F x)
    (hpair : ∀ a b : ℝ, 0 < a → 0 < b →
      4 * F a * (D b - D a) ≤ (b - a) ^ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : D b = D a := by
  apply eq_of_abs_sub_le_div_nat (D b) (D a) ((b - a) ^ 2 / (4 * a))
  intro n hn
  let t : ℕ → ℝ := fun i => a + (i : ℝ) * (b - a) / (n : ℝ)
  let step : ℝ := (b - a) / (n : ℝ)
  let q : ℝ := step ^ 2 / (4 * a)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hapos : 0 < 4 * a := by positivity
  have hba_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have ht_pos (i : ℕ) : 0 < t i := by
    dsimp [t]
    have hi_nonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have : 0 ≤ (i : ℝ) * (b - a) / (n : ℝ) :=
      div_nonneg (mul_nonneg hi_nonneg hba_nonneg) hnreal.le
    linarith
  have ht_ge (i : ℕ) : a ≤ t i := by
    dsimp [t]
    have hi_nonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have : 0 ≤ (i : ℝ) * (b - a) / (n : ℝ) :=
      div_nonneg (mul_nonneg hi_nonneg hba_nonneg) hnreal.le
    linarith
  have ht_succ (i : ℕ) : t (i + 1) - t i = step := by
    dsimp [t, step]
    push_cast
    field_simp
    ring
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hupper (i : ℕ) :
      D (t (i + 1)) - D (t i) ≤ q := by
    have hpair_i := hpair (t i) (t (i + 1)) (ht_pos i) (ht_pos (i + 1))
    rw [ht_succ] at hpair_i
    by_cases hdiff : 0 ≤ D (t (i + 1)) - D (t i)
    · have hcoef := mul_le_mul_of_nonneg_right
        (le_trans (ht_ge i) (hF (t i) (ht_pos i))) hdiff
      apply (le_div_iff₀ hapos).2
      dsimp [q]
      nlinarith
    · exact le_trans (le_of_not_ge hdiff) hq_nonneg
  have hlower (i : ℕ) :
      D (t i) - D (t (i + 1)) ≤ q := by
    have hpair_i := hpair (t (i + 1)) (t i) (ht_pos (i + 1)) (ht_pos i)
    rw [show t i - t (i + 1) = -step by rw [← ht_succ]; ring] at hpair_i
    rw [neg_sq] at hpair_i
    by_cases hdiff : 0 ≤ D (t i) - D (t (i + 1))
    · have hcoef := mul_le_mul_of_nonneg_right
        (le_trans (ht_ge (i + 1)) (hF (t (i + 1)) (ht_pos (i + 1)))) hdiff
      apply (le_div_iff₀ hapos).2
      dsimp [q]
      nlinarith
    · exact le_trans (le_of_not_ge hdiff) hq_nonneg
  have htel :
      ∑ i ∈ Finset.range n, (D (t (i + 1)) - D (t i)) = D b - D a := by
    have hsum :
        ∑ i ∈ Finset.range n, (D (t (i + 1)) - D (t i)) =
          D (t n) - D (t 0) := Finset.sum_range_sub (fun i => D (t i)) n
    rw [hsum]
    have htn : t n = b := by
      dsimp [t]
      field_simp
      ring
    simp [htn, t]
  have htel_rev :
      ∑ i ∈ Finset.range n, (D (t i) - D (t (i + 1))) = D a - D b := by
    calc
      ∑ i ∈ Finset.range n, (D (t i) - D (t (i + 1))) =
          ∑ i ∈ Finset.range n, -(D (t (i + 1)) - D (t i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = -(∑ i ∈ Finset.range n, (D (t (i + 1)) - D (t i))) := by
        exact Finset.sum_neg_distrib _
      _ = D a - D b := by rw [htel]; ring
  have hsum_upper : D b - D a ≤ ∑ _i ∈ Finset.range n, q := by
    rw [← htel]
    exact Finset.sum_le_sum fun i _hi => hupper i
  have hsum_lower : D a - D b ≤ ∑ _i ∈ Finset.range n, q := by
    rw [← htel_rev]
    exact Finset.sum_le_sum fun i _hi => hlower i
  have hsum_q :
      (∑ _i ∈ Finset.range n, q) = ((b - a) ^ 2 / (4 * a)) / (n : ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    dsimp [q, step]
    field_simp
  rw [hsum_q] at hsum_upper hsum_lower
  exact abs_le.mpr ⟨by linarith, hsum_upper⟩

/-- If every pair of positive inputs satisfies the two denominator-free pair
bounds, then `D` is constant on the positive reals. -/
private theorem eq_on_pos_of_pair_bounds (D F : ℝ → ℝ)
    (hF : ∀ x : ℝ, 0 < x → x ≤ F x)
    (hpair : ∀ a b : ℝ, 0 < a → 0 < b →
      4 * F a * (D b - D a) ≤ (b - a) ^ 2)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : D b = D a := by
  rcases le_total a b with hab | hba
  · exact eq_of_ordered_pair_bounds D F hF hpair ha hab
  · exact (eq_of_ordered_pair_bounds D F hF hpair hb hba).symm

theorem imo2026_p5 (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔ f ∈ answer := by
  constructor
  · intro hf
    let F : ℝ → ℝ := fun r => if h : 0 < r then (f ⟨r, h⟩ : ℝ) else 0
    let D : ℝ → ℝ := fun r => F r - r
    have hF_pos (r : ℝ) (hr : 0 < r) :
        F r = (f ⟨r, hr⟩ : ℝ) := by
      simp [F, hr]
    have hD_pos (r : ℝ) (hr : 0 < r) :
        D r = (f ⟨r, hr⟩ : ℝ) - r := by
      simp [D, F, hr]
    have hF : ∀ r : ℝ, 0 < r → r ≤ F r := by
      intro r hr
      rw [hF_pos r hr]
      exact sub_nonneg.mp (sub_nonneg_of_admissible f hf ⟨r, hr⟩)
    have hpair : ∀ a b : ℝ, 0 < a → 0 < b →
        4 * F a * (D b - D a) ≤ (b - a) ^ 2 := by
      intro a b ha hb
      let aa : PositiveReal := ⟨a, ha⟩
      let bb : PositiveReal := ⟨b, hb⟩
      have h := pairwise_upper f (fun x y => (hf x y).1)
        (second_iterate_eq f hf) aa bb
      simpa [F, D, ha, hb, aa, bb] using h
    have hD_const : ∀ {a b : ℝ}, 0 < a → 0 < b → D b = D a := by
      intro a b ha hb
      exact eq_on_pos_of_pair_bounds D F hF hpair ha hb
    let one : PositiveReal := ⟨1, by norm_num⟩
    let c : ℝ := (f one : ℝ) - 1
    refine ⟨c, ?_, ?_⟩
    · dsimp [c]
      exact sub_nonneg_of_admissible f hf one
    · intro x
      have hxD := (hD_const x.property one.property).symm
      rw [hD_pos (x : ℝ) x.property, hD_pos 1 one.property] at hxD
      change (f x : ℝ) - (x : ℝ) = (f one : ℝ) - 1 at hxD
      dsimp [c]
      linarith
  · rintro ⟨c, _hc, hf⟩
    exact translation_admissible f c hf

end IMO2026P5
