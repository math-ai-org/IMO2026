import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Prod.Lex
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Imo2026P1

abbrev Board := Multiset ℕ

def IsInitial (B : Board) : Prop :=
  B.card = 2026 ∧ ∀ a ∈ B, 1 < a

def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board),
    1 < m ∧ 1 < n ∧
      B = m ::ₘ n ::ₘ s ∧
      B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

def IsTerminal (B : Board) : Prop :=
  (B.filter fun a => 1 < a).card ≤ 1

def HasUniqueLarge (B : Board) : Prop :=
  (B.filter fun a => 1 < a).card = 1

def Reachable (B B' : Board) : Prop :=
  Relation.ReflTransGen Move B B'

noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map fun a => padicValNat p a).gcd

noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

private def PositiveBoard (B : Board) : Prop :=
  ∀ a ∈ B, 0 < a

private lemma initial_positive {B : Board} (hB : IsInitial B) : PositiveBoard B := by
  intro a ha
  exact (hB.2 a ha).trans' Nat.zero_lt_one

private lemma gcd_dvd_lcm (m n : ℕ) : Nat.gcd m n ∣ Nat.lcm m n :=
  (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)

private lemma move_positive {B B' : Board} (hB : PositiveBoard B) (hmove : Move B B') :
    PositiveBoard B' := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : 0 < m := Nat.zero_lt_one.trans hm
  have hn0 : 0 < n := Nat.zero_lt_one.trans hn
  have hgcd : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm0
  have hlcm : 0 < Nat.lcm m n := Nat.lcm_pos hm0 hn0
  have hquot : 0 < Nat.lcm m n / Nat.gcd m n :=
    Nat.div_pos (Nat.le_of_dvd hlcm (gcd_dvd_lcm m n)) hgcd
  intro a ha
  simp only [Multiset.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact hgcd
  · exact hquot
  · exact hB a (by simp [ha])

private lemma reachable_positive {B B' : Board} (hB : PositiveBoard B)
    (hreach : Reachable B B') : PositiveBoard B' := by
  induction hreach with
  | refl => exact hB
  | tail _ hmove ih => exact move_positive ih hmove

private lemma padicValNat_gcd (p m n : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
    ← Nat.factorization_def _ hp]
  exact congrFun (congrArg DFunLike.coe (Nat.factorization_gcd hm hn)) p

private lemma padicValNat_lcm_div_gcd (p m n : ℕ) (hp : p.Prime) (hm : m ≠ 0)
    (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n / Nat.gcd m n) =
      max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.div_of_dvd (gcd_dvd_lcm m n), padicValNat_gcd p m n hp hm hn]
  have hlcm : padicValNat p (Nat.lcm m n) =
      max (padicValNat p m) (padicValNat p n) := by
    rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
      ← Nat.factorization_def _ hp]
    have h := congrFun (congrArg DFunLike.coe (Nat.factorization_lcm hm hn)) p
    simpa using h
  rw [hlcm]

private lemma gcd_min_max_sub (a b : ℕ) :
    Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, max_eq_right hab, Nat.gcd_sub_self_right hab]
  · simp [min_eq_right hba, max_eq_left hba, Nat.gcd_sub_self_right hba, Nat.gcd_comm]

private lemma gExp_move (p : ℕ) (hp : p.Prime) {B B' : Board} (hmove : Move B B') :
    gExp p B' = gExp p B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hm0 : m ≠ 0 := (Nat.zero_lt_one.trans hm).ne'
  have hn0 : n ≠ 0 := (Nat.zero_lt_one.trans hn).ne'
  unfold gExp
  simp only [Multiset.map_cons, Multiset.gcd_cons]
  rw [padicValNat_gcd p m n hp hm0 hn0,
    padicValNat_lcm_div_gcd p m n hp hm0 hn0]
  calc
    Nat.gcd (min (padicValNat p m) (padicValNat p n))
        (Nat.gcd (max (padicValNat p m) (padicValNat p n) -
          min (padicValNat p m) (padicValNat p n))
          (s.map fun a => padicValNat p a).gcd) =
        Nat.gcd (Nat.gcd (min (padicValNat p m) (padicValNat p n))
          (max (padicValNat p m) (padicValNat p n) -
            min (padicValNat p m) (padicValNat p n)))
          (s.map fun a => padicValNat p a).gcd :=
      (Nat.gcd_assoc _ _ _).symm
    _ = Nat.gcd (Nat.gcd (padicValNat p m) (padicValNat p n))
        (s.map fun a => padicValNat p a).gcd := by rw [gcd_min_max_sub]
    _ = Nat.gcd (padicValNat p m)
        (Nat.gcd (padicValNat p n) (s.map fun a => padicValNat p a).gcd) :=
      Nat.gcd_assoc _ _ _

private lemma gExp_reachable (p : ℕ) (hp : p.Prime) {B B' : Board}
    (hreach : Reachable B B') : gExp p B' = gExp p B := by
  induction hreach with
  | refl => rfl
  | tail _ hmove ih => exact (gExp_move p hp hmove).trans ih

private lemma prime_dvd_board_prod_iff (p : ℕ) (hp : p.Prime) (B : Board) :
    p ∣ B.prod ↔ ∃ a ∈ B, p ∣ a := by
  induction B using Multiset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @cons a B ih =>
      simp only [Multiset.prod_cons, hp.dvd_mul, Multiset.mem_cons, exists_eq_or_imp, ih]

private lemma prime_support_pair_move (p m n : ℕ) (hp : p.Prime) :
    (p ∣ m ∨ p ∣ n) ↔
      p ∣ Nat.gcd m n ∨ p ∣ Nat.lcm m n / Nat.gcd m n := by
  have hfactor : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' (gcd_dvd_lcm m n)
  constructor
  · intro h
    have hplcm : p ∣ Nat.lcm m n := h.elim
      (fun hpm => hpm.trans (Nat.dvd_lcm_left m n))
      (fun hpn => hpn.trans (Nat.dvd_lcm_right m n))
    rw [← hfactor] at hplcm
    exact hp.dvd_mul.mp hplcm
  · rintro (hpgcd | hpquot)
    · exact Or.inl (hpgcd.trans (Nat.gcd_dvd_left m n))
    · have hp_lcm : p ∣ Nat.lcm m n :=
        hpquot.trans (Nat.div_dvd_of_dvd (gcd_dvd_lcm m n))
      have hlcm_prod : Nat.lcm m n ∣ m * n :=
        Nat.lcm_dvd (Nat.dvd_mul_right m n) (Nat.dvd_mul_left n m)
      exact hp.dvd_mul.mp (hp_lcm.trans hlcm_prod)

private lemma board_prod_ne_zero {B : Board} (hB : PositiveBoard B) : B.prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro hzero
  exact Nat.lt_irrefl 0 (hB 0 hzero)

private lemma primeFactors_move {B B' : Board} (hB : PositiveBoard B) (hmove : Move B B') :
    B'.prod.primeFactors = B.prod.primeFactors := by
  have hnewpos := move_positive hB hmove
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hold0 : (m ::ₘ n ::ₘ s).prod ≠ 0 := board_prod_ne_zero hB
  have hnew0 : (Nat.gcd m n ::ₘ Nat.lcm m n / Nat.gcd m n ::ₘ s).prod ≠ 0 :=
    board_prod_ne_zero hnewpos
  ext p
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpnew, -⟩
    have hsupport : p ∣ Nat.gcd m n ∨ p ∣ Nat.lcm m n / Nat.gcd m n ∨
        ∃ a ∈ s, p ∣ a := by
      rw [prime_dvd_board_prod_iff p hp] at hpnew
      simpa only [Multiset.mem_cons, exists_eq_or_imp] using hpnew
    refine ⟨hp, ?_, hold0⟩
    rw [prime_dvd_board_prod_iff p hp]
    rcases hsupport with hphead | hphead | ⟨a, ha, hpa⟩
    · rcases (prime_support_pair_move p m n hp).mpr (Or.inl hphead) with hpm | hpn
      · exact ⟨m, by simp, hpm⟩
      · exact ⟨n, by simp, hpn⟩
    · rcases (prime_support_pair_move p m n hp).mpr (Or.inr hphead) with hpm | hpn
      · exact ⟨m, by simp, hpm⟩
      · exact ⟨n, by simp, hpn⟩
    · exact ⟨a, by simp [ha], hpa⟩
  · rintro ⟨hp, hpold, -⟩
    have hsupport : p ∣ m ∨ p ∣ n ∨ ∃ a ∈ s, p ∣ a := by
      rw [prime_dvd_board_prod_iff p hp] at hpold
      simpa only [Multiset.mem_cons, exists_eq_or_imp] using hpold
    refine ⟨hp, ?_, hnew0⟩
    rw [prime_dvd_board_prod_iff p hp]
    rcases hsupport with hpm | hpn | ⟨a, ha, hpa⟩
    · rcases (prime_support_pair_move p m n hp).mp (Or.inl hpm) with hpg | hpq
      · exact ⟨Nat.gcd m n, by simp, hpg⟩
      · exact ⟨Nat.lcm m n / Nat.gcd m n, by simp, hpq⟩
    · rcases (prime_support_pair_move p m n hp).mp (Or.inr hpn) with hpg | hpq
      · exact ⟨Nat.gcd m n, by simp, hpg⟩
      · exact ⟨Nat.lcm m n / Nat.gcd m n, by simp, hpq⟩
    · exact ⟨a, by simp [ha], hpa⟩

private lemma primeFactors_reachable {B B' : Board} (hB : PositiveBoard B)
    (hreach : Reachable B B') : B'.prod.primeFactors = B.prod.primeFactors := by
  induction hreach with
  | refl => rfl
  | tail hreach hmove ih =>
      have hmid := reachable_positive hB hreach
      exact (primeFactors_move hmid hmove).trans ih

private lemma Mval_reachable {B B' : Board} (hB : PositiveBoard B)
    (hreach : Reachable B B') : Mval B' = Mval B := by
  unfold Mval
  rw [primeFactors_reachable hB hreach]
  apply Finset.prod_congr rfl
  intro p hp
  rw [gExp_reachable p (Nat.prime_of_mem_primeFactors hp) hreach]

private lemma primeFactors_product_padicValNat (M : ℕ) (hM : M ≠ 0) :
    (∏ p ∈ M.primeFactors, p ^ padicValNat p M) = M := by
  calc
    (∏ p ∈ M.primeFactors, p ^ padicValNat p M) =
        ∏ p ∈ M.primeFactors, p ^ M.factorization p := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.factorization_def M (Nat.prime_of_mem_primeFactors hp)]
    _ = M := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact Nat.prod_factorization_pow_eq_self hM

private lemma terminal_mval_eq_large {B : Board} (hB : PositiveBoard B)
    (hterm : IsTerminal B) {M : ℕ} (hM : 1 < M) (hMem : M ∈ B) : Mval B = M := by
  let large : Board := B.filter fun a => 1 < a
  let small : Board := B.filter fun a => ¬1 < a
  have hMlarge : M ∈ large := Multiset.mem_filter.mpr ⟨hMem, hM⟩
  have hlargecard : large.card = 1 := by
    have hlarge_ne : large ≠ 0 := by
      intro hz
      rw [hz] at hMlarge
      simp at hMlarge
    have hpositive : 0 < large.card := Multiset.card_pos.mpr hlarge_ne
    exact Nat.le_antisymm hterm (by omega)
  have hlarge : large = {M} := by
    rcases Multiset.card_eq_one.mp hlargecard with ⟨N, hN⟩
    have : M = N := by simpa [hN] using hMlarge
    simpa [this] using hN
  have hdecomp : large + small = B := Multiset.filter_add_not (fun a => 1 < a) B
  have hsmall_one : ∀ a ∈ small, a = 1 := by
    intro a ha
    have haB : a ∈ B := (Multiset.mem_filter.mp ha).1
    have hnot : ¬1 < a := (Multiset.mem_filter.mp ha).2
    have hapos := hB a haB
    omega
  have hprod : B.prod = M := by
    rw [← hdecomp, Multiset.prod_add, hlarge, Multiset.prod_singleton,
      Multiset.prod_eq_one hsmall_one, mul_one]
  have hgexp : ∀ p, gExp p B = padicValNat p M := by
    intro p
    have hsmallval : (small.map fun a => padicValNat p a).gcd = 0 := by
      apply (Multiset.gcd_eq_zero_iff _).mpr
      intro x hx
      rcases Multiset.mem_map.mp hx with ⟨a, ha, rfl⟩
      simp [hsmall_one a ha]
    unfold gExp
    rw [← hdecomp, Multiset.map_add, hlarge, Multiset.map_singleton,
      Multiset.gcd_add, Multiset.gcd_singleton, hsmallval, gcd_zero_right]
    simp
  unfold Mval
  rw [hprod]
  simp_rw [hgexp]
  exact primeFactors_product_padicValNat M (by omega)

private lemma mval_eq_one_of_no_large {B : Board} (hB : PositiveBoard B)
    (hnone : ∀ a ∈ B, ¬1 < a) : Mval B = 1 := by
  have hall : ∀ a ∈ B, a = 1 := by
    intro a ha
    have ha0 := hB a ha
    have ha1 := hnone a ha
    omega
  have hprod : B.prod = 1 := Multiset.prod_eq_one hall
  simp [Mval, hprod]

private lemma initial_mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  have hne : B₀ ≠ 0 := by
    intro hz
    subst B₀
    simp [IsInitial] at hB₀
  rcases Multiset.exists_mem_of_ne_zero hne with ⟨a, ha⟩
  have ha_large := hB₀.2 a ha
  rcases Nat.exists_prime_and_dvd (by omega : a ≠ 1) with ⟨p, hp, hpa⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hpos := initial_positive hB₀
  have hprod0 : B₀.prod ≠ 0 := board_prod_ne_zero hpos
  have hp_prod : p ∣ B₀.prod := hpa.trans (Multiset.dvd_prod ha)
  have hp_mem : p ∈ B₀.prod.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hp_prod, hprod0⟩
  have hgpos : gExp p B₀ ≠ 0 := by
    unfold gExp
    apply (Multiset.gcd_ne_zero_iff _).mpr
    refine ⟨padicValNat p a, Multiset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact ne_of_gt (one_le_padicValNat_of_dvd (by omega) hpa)
  have hfactor : p ^ gExp p B₀ ∣ Mval B₀ := by
    unfold Mval
    exact Finset.dvd_prod_of_mem (fun q => q ^ gExp q B₀) hp_mem
  have hmval0 : Mval B₀ ≠ 0 := by
    unfold Mval
    exact Finset.prod_ne_zero_iff.mpr fun q hq =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
  have hfactor_gt : 1 < p ^ gExp p B₀ := Nat.one_lt_pow hgpos hp.one_lt
  exact hfactor_gt.trans_le (Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hmval0) hfactor)

private lemma terminal_has_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  have hpos := reachable_positive (initial_positive hB₀) hreach
  have hge : 0 < (B'.filter fun a => 1 < a).card := by
    by_contra hnot
    have hzero : (B'.filter fun a => 1 < a).card = 0 := by omega
    have hnone : ∀ a ∈ B', ¬1 < a := by
      intro a ha hlarge
      have hafilter : a ∈ B'.filter fun x => 1 < x :=
        Multiset.mem_filter.mpr ⟨ha, hlarge⟩
      rw [Multiset.card_eq_zero.mp hzero] at hafilter
      simp at hafilter
    have hmval_one := mval_eq_one_of_no_large hpos hnone
    have hinvariant := Mval_reachable (initial_positive hB₀) hreach
    have hgt := initial_mval_gt_one B₀ hB₀
    rw [hmval_one] at hinvariant
    omega
  exact Nat.le_antisymm hterm (by omega)

private lemma terminal_large_eq_initial_mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') : M = Mval B₀ := by
  have hpos := reachable_positive (initial_positive hB₀) hreach
  calc
    M = Mval B' := (terminal_mval_eq_large hpos hterm hM hMem).symm
    _ = Mval B₀ := Mval_reachable (initial_positive hB₀) hreach

private def largeCount (B : Board) : ℕ :=
  (B.filter fun a => 1 < a).card

private def boardMeasure (B : Board) : ℕ ×ₗ ℕ :=
  toLex (largeCount B, B.prod)

private lemma sequence_entries_positive (B₀ : Board) (hB₀ : IsInitial B₀)
    (f : ℕ → Board) (hf0 : f 0 = B₀)
    (hmoves : ∀ k, Move (f k) (f (k + 1))) :
    ∀ k a, a ∈ f k → 0 < a := by
  intro k
  induction k with
  | zero =>
      intro a ha
      rw [hf0] at ha
      exact (hB₀.2 a ha).trans' (by omega)
  | succ k ih =>
      exact move_positive ih (hmoves k)

private lemma move_decreases_measure {B B' : Board}
    (hB : PositiveBoard B) (hmove : Move B B') :
    boardMeasure B' < boardMeasure B := by
  rcases hmove with ⟨m, n, s, hm, hn, rfl, rfl⟩
  have hspos : 0 < s.prod := by
    have hs : PositiveBoard s := by
      intro a ha
      exact hB a (by simp [ha])
    clear hB
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        rw [Multiset.prod_cons]
        exact Nat.mul_pos (hs a (by simp)) (ih fun b hb => hs b (by simp [hb]))
  have hq : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' (gcd_dvd_lcm m n)
  simp only [boardMeasure]
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hg : 1 < Nat.gcd m n
  · by_cases hqLarge : 1 < Nat.lcm m n / Nat.gcd m n
    · right
      constructor
      · simp [largeCount, hm, hn, hg, hqLarge]
      · have hglcm : Nat.gcd m n * Nat.lcm m n = m * n := Nat.gcd_mul_lcm m n
        simp only [Multiset.prod_cons]
        calc
          Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n * s.prod) =
              (Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n)) * s.prod := by
                rw [mul_assoc]
          _ = Nat.lcm m n * s.prod := by rw [hq]
          _ < (Nat.gcd m n * Nat.lcm m n) * s.prod :=
            Nat.mul_lt_mul_of_pos_right
              (show Nat.lcm m n < Nat.gcd m n * Nat.lcm m n by
                simpa only [one_mul] using
                  Nat.mul_lt_mul_of_pos_right hg (Nat.lcm_pos (by omega) (by omega)))
              hspos
          _ = (m * n) * s.prod := by rw [hglcm]
          _ = m * (n * s.prod) := by rw [mul_assoc]
    · left
      simp [largeCount, hm, hn, hg, hqLarge]
  · left
    by_cases hqLarge : 1 < Nat.lcm m n / Nat.gcd m n <;>
      simp [largeCount, hm, hn, hg, hqLarge]

theorem imo2026_p1a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  rintro ⟨f, hf0, hmoves⟩
  have hpositive := sequence_entries_positive B₀ hB₀ f hf0 hmoves
  obtain ⟨k, hk⟩ :=
    WellFounded.not_rel_apply_succ
      (r := fun x y : ℕ ×ₗ ℕ => x < y) (fun k => boardMeasure (f k))
  exact hk (move_decreases_measure (hpositive k) (hmoves k))

theorem imo2026_p1a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' :=
  terminal_has_unique_large B₀ hB₀ B' hreach hterm

theorem imo2026_p1b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  intro M
  constructor
  · rintro ⟨hM, hMem⟩
    have hvalue := terminal_large_eq_initial_mval B₀ hB₀ B₁ h₁ t₁ M hM hMem
    have hu := terminal_has_unique_large B₀ hB₀ B₂ h₂ t₂
    rcases Multiset.card_eq_one.mp hu with ⟨N, hfilter⟩
    have hNfilter : N ∈ B₂.filter fun a => 1 < a := by simp [hfilter]
    have hN : 1 < N := (Multiset.mem_filter.mp hNfilter).2
    have hNmem : N ∈ B₂ := (Multiset.mem_filter.mp hNfilter).1
    have hNvalue := terminal_large_eq_initial_mval B₀ hB₀ B₂ h₂ t₂ N hN hNmem
    subst M
    rw [← hNvalue]
    exact ⟨hN, hNmem⟩
  · rintro ⟨hM, hMem⟩
    have hvalue := terminal_large_eq_initial_mval B₀ hB₀ B₂ h₂ t₂ M hM hMem
    have hu := terminal_has_unique_large B₀ hB₀ B₁ h₁ t₁
    rcases Multiset.card_eq_one.mp hu with ⟨N, hfilter⟩
    have hNfilter : N ∈ B₁.filter fun a => 1 < a := by simp [hfilter]
    have hN : 1 < N := (Multiset.mem_filter.mp hNfilter).2
    have hNmem : N ∈ B₁ := (Multiset.mem_filter.mp hNfilter).1
    have hNvalue := terminal_large_eq_initial_mval B₀ hB₀ B₁ h₁ t₁ N hN hNmem
    subst M
    rw [← hNvalue]
    exact ⟨hN, hNmem⟩

theorem imo2026_p1_terminal_value (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ :=
  terminal_large_eq_initial_mval B₀ hB₀ B' hreach hterm M hM hMem

theorem imo2026_p1_mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) :
    1 < Mval B₀ :=
  initial_mval_gt_one B₀ hB₀

end Imo2026P1
