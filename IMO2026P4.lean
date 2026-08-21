import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic

namespace IMO2026P4

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

private lemma wins_first_multiple (θ : ℝ) (hθ0 : 0 < θ)
    (k : ℕ) (hk : 0 < k) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 180) (hαk : α = (k : ℝ) * θ) :
    MulanWins θ {α, β, γ} := by
  induction k using Nat.strong_induction_on generalizing α β γ with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      apply MulanWins.win
      simp only [HasAngle]
      rw [show α = θ by norm_num at hαk; exact hαk]
      simp
    · have hk2 : 2 ≤ k := by omega
      let x : ℝ := γ + (k - 1 : ℕ) * θ
      let L : Multiset ℝ := {β, x, 180 - β - x}
      let R : Multiset ℝ := {γ, 180 - x, x - γ}
      have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hsum' : (k : ℝ) * θ + β + γ = 180 := by
        rw [← hαk]
        exact hsum
      apply MulanWins.move (L := L) (R := R)
      · refine ⟨α, β, γ, x, rfl, ?_, ?_, rfl, rfl⟩
        · dsimp [x]
          have hcast : (0 : ℝ) < (k - 1 : ℕ) := by
            exact_mod_cast (show 0 < k - 1 by omega)
          nlinarith
        · dsimp [x]
          rw [hkcast]
          nlinarith
      · apply MulanWins.win
        simp only [HasAngle, L]
        apply Multiset.mem_cons_of_mem
        apply Multiset.mem_cons_of_mem
        rw [Multiset.mem_singleton]
        dsimp [x]
        rw [hkcast]
        ring_nf at hsum' ⊢
        nlinarith
      · have hkm1 : 0 < k - 1 := by omega
        have hxγ : 0 < x - γ := by
          dsimp [x]
          rw [hkcast]
          have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
          nlinarith
        have hw := ih (k - 1) (by omega) hkm1 (x - γ) γ (180 - x)
          hxγ
          hγ
          (by
            dsimp [x]
            rw [hkcast]
            nlinarith)
          (by dsimp [x]; ring)
          (by dsimp [x]; ring)
        have heq : R = ({x - γ, γ, 180 - x} : Multiset ℝ) := by
          dsimp [R]
          exact
            (congrArg (Multiset.cons γ)
                (Multiset.cons_swap (180 - x) (x - γ) 0)).trans
              (Multiset.cons_swap γ (x - γ) {180 - x})
        rw [heq]
        exact hw

private lemma wins_sorted
    (θ : ℝ) (hθ180 : θ < 180) (n : ℕ) (hn : 0 < n)
    (hnθ : (n : ℝ) * θ = 180) (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsum : A + B + C = 180) (hAB : A ≤ B) (hBC : B ≤ C) :
    MulanWins θ {A, B, C} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ0 : 0 < θ := by nlinarith
  by_cases hAt : A = θ
  · exact .win (by simp [HasAngle, hAt])
  by_cases hBt : B = θ
  · exact .win (by simp [HasAngle, hBt])
  by_cases hCt : C = θ
  · exact .win (by simp [HasAngle, hCt])
  have hn2 : 2 ≤ n := by
    by_contra hh
    have hn1 : n = 1 := by omega
    subst n
    norm_num at hnθ
    nlinarith
  let k : ℕ := Nat.ceil (A / θ)
  have hkpos : 0 < k := Nat.ceil_pos.mpr (div_pos hA hθ0)
  have hkge : A / θ ≤ (k : ℝ) := Nat.le_ceil (A / θ)
  have hklt : (k : ℝ) < A / θ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hA.le hθ0.le)
  have hAk_le : A ≤ (k : ℝ) * θ := by
    have hh := (div_le_iff₀ hθ0).mp hkge
    nlinarith
  have hkltAθ : (k : ℝ) * θ < A + θ := by
    have hh : (k : ℝ) - 1 < A / θ := by linarith [hklt]
    have hh' := (lt_div_iff₀ hθ0).mp hh
    nlinarith
  by_cases hAk_eq : A = (k : ℝ) * θ
  · exact wins_first_multiple θ hθ0 k hkpos A B C hA hB hC hsum hAk_eq
  have hAk : A < (k : ℝ) * θ := lt_of_le_of_ne hAk_le hAk_eq
  have hxupper : (k : ℝ) * θ < 180 - B := by
    by_cases hn2eq : n = 2
    · have hnθ' : 2 * θ = 180 := by
        rw [← hnθ]
        norm_num [hn2eq]
      have hAθ : A < θ := by nlinarith [hAB, hBC, hA, hB, hC]
      have hk1 : k = 1 := by
        have hratio : A / θ < 1 := by
          rw [div_lt_one hθ0]
          exact hAθ
        have hkR : (k : ℝ) < 2 := by linarith [hklt]
        have hkNat : k < 2 := by exact_mod_cast hkR
        omega
      have hBθ : B < θ := by
        by_contra hnot
        have hθB : θ ≤ B := le_of_not_gt hnot
        have hθC : θ ≤ C := hθB.trans hBC
        nlinarith
      rw [hk1]
      norm_num
      nlinarith
    · have hn3 : 3 ≤ n := by omega
      have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hθ60 : θ ≤ 60 := by
        have hp := mul_nonneg (show 0 ≤ (n : ℝ) - 3 by nlinarith) hθ0.le
        nlinarith
      have hC60 : 60 ≤ C := by nlinarith
      have hθC : θ < C := lt_of_le_of_ne (hθ60.trans hC60) (Ne.symm hCt)
      nlinarith [hkltAθ]
  have hkn : k < n := by
    have hh : (k : ℝ) * θ < (n : ℝ) * θ := by nlinarith
    have hkR : (k : ℝ) < n := lt_of_mul_lt_mul_right hh hθ0.le
    exact_mod_cast hkR
  let L : Multiset ℝ := {B, (k : ℝ) * θ, 180 - B - (k : ℝ) * θ}
  let R : Multiset ℝ := {A, 180 - (k : ℝ) * θ, (k : ℝ) * θ - A}
  have hcut : IsCut ({A, B, C} : Multiset ℝ) L R := by
    refine ⟨C, B, A, (k : ℝ) * θ, ?_, hAk, hxupper, ?_, ?_⟩
    · calc
        {A, B, C} = {B, A, C} := Multiset.cons_swap A B _
        _ = {B, C, A} :=
          congrArg (Multiset.cons B) (Multiset.cons_swap A C 0)
        _ = {C, B, A} := Multiset.cons_swap B C _
    · rfl
    · rfl
  have hLwin : MulanWins θ L := by
    have hw := wins_first_multiple θ hθ0 k hkpos ((k : ℝ) * θ) B
      (180 - B - (k : ℝ) * θ) (mul_pos (by exact_mod_cast hkpos) hθ0)
      hB (by nlinarith) (by ring) rfl
    rw [show L = ({(k : ℝ) * θ, B, 180 - B - (k : ℝ) * θ} : Multiset ℝ) by
      dsimp [L]
      exact Multiset.cons_swap B ((k : ℝ) * θ) _]
    exact hw
  have hRwin : MulanWins θ R := by
    have hnk : 0 < n - k := by omega
    have heq : 180 - (k : ℝ) * θ = ((n - k : ℕ) : ℝ) * θ := by
      rw [Nat.cast_sub (by omega), sub_mul, hnθ]
    have hw := wins_first_multiple θ hθ0 (n - k) hnk
      (180 - (k : ℝ) * θ) A ((k : ℝ) * θ - A)
      (by nlinarith) hA (by nlinarith) (by ring) heq
    rw [show R = ({180 - (k : ℝ) * θ, A, (k : ℝ) * θ - A} : Multiset ℝ) by
      dsimp [R]
      exact Multiset.cons_swap A (180 - (k : ℝ) * θ) _]
    exact hw
  exact MulanWins.move hcut hLwin hRwin

private lemma wins_of_divisor
    (θ : ℝ) (hθ180 : θ < 180) (n : ℕ) (hn : 0 < n)
    (hnθ : (n : ℝ) * θ = 180) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 180) : MulanWins θ {α, β, γ} := by
  rcases le_total α β with hαβ | hβα
  · rcases le_total β γ with hβγ | hγβ
    · exact wins_sorted θ hθ180 n hn hnθ α β γ hα hβ hγ hsum hαβ hβγ
    · rcases le_total α γ with hαγ | hγα
      · rw [show ({α, β, γ} : Multiset ℝ) = {α, γ, β} by
          exact congrArg (Multiset.cons α) (Multiset.cons_swap β γ 0)]
        exact wins_sorted θ hθ180 n hn hnθ α γ β hα hγ hβ (by nlinarith) hαγ hγβ
      · rw [show ({α, β, γ} : Multiset ℝ) = {γ, α, β} by
          calc
            {α, β, γ} = {β, α, γ} := Multiset.cons_swap α β _
            _ = {β, γ, α} :=
              congrArg (Multiset.cons β) (Multiset.cons_swap α γ 0)
            _ = {γ, β, α} := Multiset.cons_swap β γ _
            _ = {γ, α, β} :=
              congrArg (Multiset.cons γ) (Multiset.cons_swap β α 0)]
        exact wins_sorted θ hθ180 n hn hnθ γ α β hγ hα hβ (by nlinarith) hγα hαβ
  · rcases le_total α γ with hαγ | hγα
    · rw [show ({α, β, γ} : Multiset ℝ) = {β, α, γ} by
          exact Multiset.cons_swap α β {γ}]
      exact wins_sorted θ hθ180 n hn hnθ β α γ hβ hα hγ (by nlinarith) hβα hαγ
    · rcases le_total β γ with hβγ | hγβ
      · rw [show ({α, β, γ} : Multiset ℝ) = {β, γ, α} by
          calc
            {α, β, γ} = {β, α, γ} := Multiset.cons_swap α β _
            _ = {β, γ, α} :=
              congrArg (Multiset.cons β) (Multiset.cons_swap α γ 0)]
        exact wins_sorted θ hθ180 n hn hnθ β γ α hβ hγ hα (by nlinarith) hβγ hγα
      · rw [show ({α, β, γ} : Multiset ℝ) = {γ, β, α} by
          calc
            {α, β, γ} = {β, α, γ} := Multiset.cons_swap α β _
            _ = {β, γ, α} :=
              congrArg (Multiset.cons β) (Multiset.cons_swap α γ 0)
            _ = {γ, β, α} := Multiset.cons_swap β γ _]
        exact wins_sorted θ hθ180 n hn hnθ γ β α hγ hβ hα (by nlinarith) hγβ hβα

private lemma cut_triangles (s L R : Multiset ℝ)
    (hs : IsTriangle s) (hc : IsCut s L R) : IsTriangle L ∧ IsTriangle R := by
  rcases hc with ⟨α, β, γ, x, rfl, hγx, hxβ, rfl, rfl⟩
  have hα : 0 < α := hs.2.1 α (by simp)
  have hβ : 0 < β := hs.2.1 β (by simp)
  have hγ : 0 < γ := hs.2.1 γ (by simp)
  constructor
  · refine ⟨by simp, ?_, by simp⟩
    intro y hy
    have : y = β ∨ y = x ∨ y = 180 - β - x := by simpa using hy
    rcases this with rfl | rfl | rfl <;> nlinarith
  · refine ⟨by simp, ?_, by simp⟩
    intro y hy
    have : y = γ ∨ y = 180 - x ∨ y = x - γ := by simpa using hy
    rcases this with rfl | rfl | rfl <;> nlinarith

private def NoPositiveMultiple (θ : ℝ) (s : Multiset ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → (k : ℝ) * θ ∉ s

private lemma not_wins_of_no_positive_multiple
    (θ : ℝ) (s : Multiset ℝ) (hθ0 : 0 < θ)
    (h180 : ∀ k : ℕ, 0 < k → (k : ℝ) * θ ≠ 180)
    (hs : IsTriangle s) (hno : NoPositiveMultiple θ s) : ¬ MulanWins θ s := by
  intro hw
  induction hw with
  | win ha =>
      exact hno 1 (by omega) (by simpa [HasAngle] using ha)
  | @move s L R hc hwL hwR ihL ihR =>
      obtain ⟨hsL, hsR⟩ := cut_triangles s L R hs hc
      by_cases hLn : NoPositiveMultiple θ L
      · exact ihL hsL hLn
      by_cases hRn : NoPositiveMultiple θ R
      · exact ihR hsR hRn
      rcases hc with ⟨α, β, γ, x, hsrep, hγx, hxβ, hLe, hRe⟩
      subst s
      subst L
      subst R
      have hsum : α + β + γ = 180 := by
        simpa [IsTriangle, add_assoc] using hs.2.2
      have hα : 0 < α := hs.2.1 α (by simp)
      have hβ : 0 < β := hs.2.1 β (by simp)
      have hγ : 0 < γ := hs.2.1 γ (by simp)
      have hLex := not_forall.mp hLn
      obtain ⟨m, hmnot⟩ := hLex
      have hmpos : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := by omega
        subst m
        simp at hmnot
      have hmL : (m : ℝ) * θ ∈ ({β, x, 180 - β - x} : Multiset ℝ) := by
        by_contra hmm
        exact hmnot (fun _ => hmm)
      have hmlem :
          (m : ℝ) * θ = β ∨ (m : ℝ) * θ = x ∨
            (m : ℝ) * θ = 180 - β - x := by
        simpa using hmL
      have hRex := not_forall.mp hRn
      obtain ⟨n, hnnot⟩ := hRex
      have hnpos : 0 < n := by
        by_contra hn
        have hn0 : n = 0 := by omega
        subst n
        simp at hnnot
      have hnR : (n : ℝ) * θ ∈ ({γ, 180 - x, x - γ} : Multiset ℝ) := by
        by_contra hnn
        exact hnnot (fun _ => hnn)
      have hnlem :
          (n : ℝ) * θ = γ ∨ (n : ℝ) * θ = 180 - x ∨
            (n : ℝ) * θ = x - γ := by
        simpa using hnR
      rcases hmlem with hmβ | hmx | hmthird
      · exact hno m hmpos (by simp [hmβ])
      · rcases hnlem with hnγ | hnsecond | hnthird
        · exact hno n hnpos (by simp [hnγ])
        · apply h180 (m + n) (by omega)
          norm_num [Nat.cast_add]
          nlinarith
        · have hnmR : (n : ℝ) < (m : ℝ) := by nlinarith
          have hnm : n < m := by exact_mod_cast hnmR
          apply hno (m - n) (by omega)
          rw [show ((m - n : ℕ) : ℝ) * θ = γ by
            rw [Nat.cast_sub (by omega), sub_mul]
            nlinarith]
          simp
      · rcases hnlem with hnγ | hnsecond | hnthird
        · exact hno n hnpos (by simp [hnγ])
        · have hmnR : (m : ℝ) < (n : ℝ) := by nlinarith
          have hmn : m < n := by exact_mod_cast hmnR
          apply hno (n - m) (by omega)
          rw [show ((n - m : ℕ) : ℝ) * θ = β by
            rw [Nat.cast_sub (by omega), sub_mul]
            nlinarith]
          simp
        · apply hno (m + n) (by omega)
          rw [show ((m + n : ℕ) : ℝ) * θ = α by
            norm_num [Nat.cast_add]
            nlinarith]
          simp

private lemma exists_losing_triangle
    (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180)
    (h180 : ∀ k : ℕ, 0 < k → (k : ℝ) * θ ≠ 180) :
    ∃ s : Multiset ℝ, IsTriangle s ∧ ¬ MulanWins θ s := by
  let N : ℕ := ⌊180 / θ⌋₊
  have hdiv1 : 1 < 180 / θ := by
    rw [lt_div_iff₀ hθ0]
    simpa using hθ180
  have hNpos : 0 < N := by
    apply Nat.floor_pos.mpr
    exact hdiv1.le
  have hNle : (N : ℝ) ≤ 180 / θ := Nat.floor_le (by positivity)
  have hN1gt : 180 / θ < N + 1 := Nat.lt_floor_add_one (180 / θ)
  let a : ℝ := (180 - N * θ) / 3
  have ha : 0 < a := by
    dsimp [a]
    have hle : (N : ℝ) * θ ≤ 180 := (le_div_iff₀ hθ0).mp hNle
    have hne : (N : ℝ) * θ ≠ 180 := h180 N hNpos
    have hlt : (N : ℝ) * θ < 180 := lt_of_le_of_ne hle hne
    linarith
  have halft : a < θ := by
    dsimp [a]
    have hlt : 180 < ((N : ℝ) + 1) * θ := by
      apply (div_lt_iff₀ hθ0).mp
      exact_mod_cast hN1gt
    nlinarith
  let s : Multiset ℝ := {a, a, 180 - 2 * a}
  have hs : IsTriangle s := by
    refine ⟨by simp [s], ?_, ?_⟩
    · intro x hx
      have : x = a ∨ x = a ∨ x = 180 - 2 * a := by
        simpa [s] using hx
      rcases this with rfl | rfl | rfl
      · exact ha
      · exact ha
      · dsimp [a]
        have hNθ : 0 < (N : ℝ) * θ := mul_pos (by positivity) hθ0
        linarith
    · simp [s]
      ring
  have hno : NoPositiveMultiple θ s := by
    intro k hk hmem
    have hcases :
        (k : ℝ) * θ = a ∨ (k : ℝ) * θ = a ∨
          (k : ℝ) * θ = 180 - 2 * a := by
      simpa [s] using hmem
    rcases hcases with hka | hka | hkbig
    · have hkθ : θ ≤ (k : ℝ) * θ := by
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      nlinarith
    · have hkθ : θ ≤ (k : ℝ) * θ := by
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
      nlinarith
    · dsimp [a] at hkbig
      have heq : ((3 : ℝ) * (k : ℝ) - 2 * (N : ℝ)) * θ = 180 := by
        ring_nf
        nlinarith
      have hcoef : (2 : ℝ) * (N : ℝ) < 3 * (k : ℝ) := by
        have hp : 0 < ((3 : ℝ) * (k : ℝ) - 2 * (N : ℝ)) * θ := by
          rw [heq]
          norm_num
        have hpos := (pos_iff_pos_of_mul_pos hp).mpr hθ0
        nlinarith
      have hNat : 2 * N < 3 * k := by exact_mod_cast hcoef
      apply h180 (3 * k - 2 * N) (by omega)
      rw [Nat.cast_sub (by omega)]
      norm_num [Nat.cast_mul]
      nlinarith
  exact ⟨s, hs, not_wins_of_no_positive_multiple θ s hθ0 h180 hs hno⟩

/- determine -/ abbrev answer : Set ℝ :=
  {θ | ∃ n : ℕ, 1 < n ∧ (n : ℝ) * θ = 180}

theorem imo2026_p4 (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ θ ∈ answer := by
  constructor
  · intro hwin
    by_contra hnot
    have h180 : ∀ n : ℕ, 0 < n → (n : ℝ) * θ ≠ 180 := by
      intro n hn hnθ
      by_cases hn1 : n = 1
      · subst n
        norm_num at hnθ
        nlinarith
      · exact hnot ⟨n, by omega, hnθ⟩
    obtain ⟨s, hs, hlose⟩ := exists_losing_triangle θ hθ0 hθ180 h180
    exact hlose (hwin s hs)
  · rintro ⟨n, hn, hnθ⟩ s ⟨hcard, hpos, hsum⟩
    obtain ⟨α, β, γ, rfl⟩ := Multiset.card_eq_three.mp hcard
    have hα : 0 < α := hpos α (by simp)
    have hβ : 0 < β := hpos β (by simp)
    have hγ : 0 < γ := hpos γ (by simp)
    have hsum' : α + β + γ = 180 := by
      simpa [add_assoc] using hsum
    exact wins_of_divisor θ hθ180 n (by omega) hnθ α β γ hα hβ hγ hsum'

end IMO2026P4
