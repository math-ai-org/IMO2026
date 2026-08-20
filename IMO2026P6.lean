import Mathlib.Data.Nat.Squarefree

import Mathlib.Tactic

namespace IMO2026P6

open scoped BigOperators

def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

private def Accepted (a : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ (∀ p ∈ S, p.Prime) ∧ ∀ n, (S ∩ (a n).primeFactors).Nonempty

private lemma prime_of_mem_support {x p : ℕ} (hp : p ∈ x.primeFactors) : p.Prime :=
  Nat.prime_of_mem_primeFactors hp

private lemma support_nonempty {x : ℕ} (hx : 1 < x) : x.primeFactors.Nonempty :=
  Nat.nonempty_primeFactors.mpr hx

private lemma exists_large_with_support (A : ℕ) {S : Finset ℕ} (hS : S.Nonempty)
    (hprime : ∀ p ∈ S, p.Prime) :
    ∃ x, A < x ∧ x.primeFactors = S := by
  let P := ∏ p ∈ S, p
  let r := S.min' hS
  have hrmem : r ∈ S := S.min'_mem hS
  have hrprime : r.Prime := hprime r hrmem
  let x := P * r ^ (A + 1)
  refine ⟨x, ?_, ?_⟩
  · have hPpos : 0 < P := Finset.prod_pos fun p hp => (hprime p hp).pos
    have hpow : A < r ^ (A + 1) := by
      exact (A.lt_pow_self hrprime.one_lt).trans_le
        (Nat.pow_le_pow_right hrprime.pos (Nat.le_add_right A 1))
    have hle : r ^ (A + 1) ≤ x := by
      simpa [x, P, mul_comm] using Nat.le_mul_of_pos_left (r ^ (A + 1)) hPpos
    exact hpow.trans_le hle
  · have hPzero : P ≠ 0 := (Finset.prod_pos fun p hp => (hprime p hp).pos).ne'
    have hrpowzero : r ^ (A + 1) ≠ 0 := pow_ne_zero _ hrprime.ne_zero
    rw [show x = P * r ^ (A + 1) by rfl, Nat.primeFactors_mul hPzero hrpowzero,
      Nat.primeFactors_prod hprime, Nat.primeFactors_pow r (by omega), hrprime.primeFactors]
    exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hrmem)

private lemma support_inter_of_gcd_gt_one {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 1 < Nat.gcd x y) : (x.primeFactors ∩ y.primeFactors).Nonempty := by
  rw [← Nat.primeFactors_gcd hx hy]
  exact support_nonempty h

private lemma greedy_range {a : ℕ → ℕ} (ha : IsValidSeq a)
    {x : ℕ} (hx : a 0 < x) (hcompat : ∀ n, 1 < Nat.gcd x (a n)) :
    x ∈ Set.range a := by
  have hstep : ∀ n, a n < a (n + 1) := fun n => (ha.2 n).1
  have hmono : StrictMono a := strictMono_nat_of_lt_succ hstep
  have hunbounded : ∃ n, x ≤ a n := by
    refine ⟨x, ?_⟩
    have hadd : x + a 0 ≤ a (x + 0) := hmono.add_le_nat x 0
    have hxa : x ≤ x + a 0 := Nat.le_add_right x (a 0)
    simpa using hxa.trans hadd
  let n := Nat.find hunbounded
  have hnle : x ≤ a n := Nat.find_spec hunbounded
  rcases n.eq_zero_or_pos with hnzero | hnpos
  · simp only [hnzero] at hnle
    exact ⟨0, (Nat.le_antisymm hnle hx.le).symm⟩
  · have hprevlt : a (n - 1) < x := by
      exact Nat.lt_of_not_ge (Nat.find_min hunbounded (Nat.pred_lt hnpos.ne'))
    have hnrepr : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnpos.ne')
    by_contra hnotrange
    have hxne : x ≠ a n := fun he => hnotrange ⟨n, he.symm⟩
    have hxlt : x < a n := lt_of_le_of_ne hnle hxne
    obtain ⟨i, hi, hgcd⟩ := (ha.2 (n - 1)).2.2 x hprevlt (by simpa [hnrepr] using hxlt)
    have := hcompat i
    omega

private lemma skipped_has_coprime {a : ℕ → ℕ} (ha : IsValidSeq a)
    {x : ℕ} (hx : a 0 < x) (hnot : x ∉ Set.range a) :
    ∃ i, a i < x ∧ Nat.gcd x (a i) = 1 := by
  have hmono : StrictMono a := strictMono_nat_of_lt_succ fun k => (ha.2 k).1
  by_contra h
  apply hnot
  apply greedy_range ha hx
  intro n
  have hne : Nat.gcd x (a n) ≠ 1 := by
    intro heq
    by_cases hlt : a n < x
    · exact h ⟨n, hlt, heq⟩
    · have hxle : x ≤ a n := Nat.le_of_not_gt hlt
      have hunbounded : ∃ m, x ≤ a m := ⟨n, hxle⟩
      let m := Nat.find hunbounded
      have hmle : x ≤ a m := Nat.find_spec hunbounded
      rcases m.eq_zero_or_pos with hmzero | hmpos
      · have hmle0 : x ≤ a 0 := by simpa [hmzero] using hmle
        omega
      · have hprev : a (m - 1) < x := by
          exact Nat.lt_of_not_ge (Nat.find_min hunbounded (Nat.pred_lt hmpos.ne'))
        have hmrepr : m - 1 + 1 = m :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmpos.ne')
        by_cases hxm : x = a m
        · exact hnot ⟨m, hxm.symm⟩
        · have hxmlt : x < a m := lt_of_le_of_ne hmle hxm
          obtain ⟨j, hj, hgj⟩ :=
            (ha.2 (m - 1)).2.2 x hprev (by simpa [hmrepr] using hxmlt)
          have hjlt : a j < x := (hmono.monotone hj).trans_lt hprev
          exact h ⟨j, hjlt, hgj⟩
  have hpos : 0 < Nat.gcd x (a n) := Nat.gcd_pos_of_pos_left _ (by omega)
  omega

private lemma range_support_accepted {a : ℕ → ℕ} (ha : IsValidSeq a) (n : ℕ) :
    Accepted a (a n).primeFactors := by
  refine ⟨support_nonempty (ha.1 n), fun p hp => prime_of_mem_support hp, ?_⟩
  intro m
  have hmono : StrictMono a := strictMono_nat_of_lt_succ fun k => (ha.2 k).1
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hg : 1 < Nat.gcd (a n) (a m) := by
      have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
      have hmle : m ≤ n - 1 := Nat.le_pred_of_lt hmn
      have hnr : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnpos.ne')
      simpa [hnr] using (ha.2 (n - 1)).2.1 m hmle
    exact support_inter_of_gcd_gt_one (ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 n)))
      (ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 m))) hg
  · subst m
    exact ⟨(a n).primeFactors.min' (support_nonempty (ha.1 n)),
      Finset.mem_inter.mpr ⟨Finset.min'_mem _ _, Finset.min'_mem _ _⟩⟩
  · have hg : 1 < Nat.gcd (a n) (a m) := by
      have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
      have hnle : n ≤ m - 1 := Nat.le_pred_of_lt hnm
      have hmr : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmpos.ne')
      rw [Nat.gcd_comm]
      simpa [hmr] using (ha.2 (m - 1)).2.1 n hnle
    exact support_inter_of_gcd_gt_one (ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 n)))
      (ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 m))) hg

private lemma accepted_iff_large_range {a : ℕ → ℕ} (ha : IsValidSeq a)
    {S : Finset ℕ} (hS : S.Nonempty) (hprime : ∀ p ∈ S, p.Prime) :
    Accepted a S ↔ ∀ x, a 0 < x → x.primeFactors = S → x ∈ Set.range a := by
  constructor
  · rintro ⟨-, -, hhit⟩ x hx hsupp
    apply greedy_range ha hx
    intro n
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans (Nat.zero_lt_one) (lt_trans (ha.1 0) hx))
    have han0 : a n ≠ 0 := ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 n))
    rw [← Nat.nonempty_primeFactors]
    rw [Nat.primeFactors_gcd hx0 han0, hsupp]
    exact hhit n
  · intro hrange
    refine ⟨hS, hprime, ?_⟩
    intro n
    obtain ⟨x, hx, hsupp⟩ := exists_large_with_support (a 0) hS hprime
    obtain ⟨k, hk⟩ := hrange x hx hsupp
    subst x
    rw [hsupp.symm]
    exact (range_support_accepted ha k).2.2 n

private lemma accepted_pairwise_inter {a : ℕ → ℕ} (ha : IsValidSeq a)
    {S U : Finset ℕ} (hS : Accepted a S) (hU : Accepted a U) :
    (S ∩ U).Nonempty := by
  obtain ⟨x, hx, hsupp⟩ := exists_large_with_support (a 0) hS.1 hS.2.1
  obtain ⟨n, hn⟩ := (accepted_iff_large_range ha hS.1 hS.2.1).mp hS x hx hsupp
  subst x
  rw [hsupp.symm]
  simpa [Finset.inter_comm] using hU.2.2 n

private lemma exists_smaller_after_erase (A m q : ℕ) {S : Finset ℕ}
    (hm : A < m) (hsupp : m.primeFactors = S) (hq : q ∈ S) (hqprime : q.Prime)
    (hlarge : A < q) (hC : (S.erase q).Nonempty)
    (hprime : ∀ p ∈ S, p.Prime) :
    ∃ y, A < y ∧ y.primeFactors = S.erase q ∧ y < m := by
  let C := S.erase q
  let P := ∏ p ∈ C, p
  let r := C.min' hC
  have hrC : r ∈ C := C.min'_mem hC
  have hrprime : r.Prime := hprime r (Finset.mem_of_mem_erase hrC)
  have hprimeC : ∀ p ∈ C, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_of_mem_erase hp)
  have hPpos : 0 < P := Finset.prod_pos fun p hp => (hprimeC p hp).pos
  have hPzero : P ≠ 0 := hPpos.ne'
  have hPsupp : P.primeFactors = C := Nat.primeFactors_prod hprimeC
  have hqP_le : q * P ≤ m := by
    have hprodEq : ∏ p ∈ S, p = q * P := by
      simpa [C, P] using (Finset.mul_prod_erase S id hq).symm
    rw [← hprodEq, ← hsupp]
    exact Nat.le_of_dvd (lt_of_le_of_lt (Nat.zero_le A) hm)
      (Nat.prod_primeFactors_dvd m)
  by_cases hPA : A < P
  · refine ⟨P, hPA, hPsupp, ?_⟩
    have hPltqP : P < q * P := by
      nlinarith [Nat.mul_le_mul_right P hqprime.one_lt]
    exact hPltqP.trans_le hqP_le
  · have hPleA : P ≤ A := Nat.le_of_not_gt hPA
    have hexp : ∃ k, A < P * r ^ k := by
      refine ⟨A + 1, ?_⟩
      have hpow : A < r ^ (A + 1) :=
        (A.lt_pow_self hrprime.one_lt).trans_le
          (Nat.pow_le_pow_right hrprime.pos (Nat.le_add_right A 1))
      have hrpow_le : r ^ (A + 1) ≤ P * r ^ (A + 1) := by
        exact Nat.le_mul_of_pos_left _ hPpos
      exact hpow.trans_le hrpow_le
    let k := Nat.find hexp
    have hk_spec : A < P * r ^ k := Nat.find_spec hexp
    have hkpos : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      simp [hk0] at hk_spec
      omega
    have hkprev : P * r ^ (k - 1) ≤ A := by
      exact Nat.le_of_not_gt (Nat.find_min hexp (Nat.pred_lt hkpos.ne'))
    have hrleP : r ≤ P := by
      exact Nat.le_of_dvd hPpos (Finset.dvd_prod_of_mem id hrC)
    have hyltqP : P * r ^ k < q * P := by
      have hkdecomp : k - 1 + 1 = k :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hkpos.ne')
      rw [← hkdecomp, pow_succ]
      have h1 : P * r ^ (k - 1) * r ≤ A * r := Nat.mul_le_mul_right r hkprev
      have h2 : A * r < q * r := Nat.mul_lt_mul_of_pos_right hlarge hrprime.pos
      have h3 : q * r ≤ q * P := Nat.mul_le_mul_left q hrleP
      simpa [mul_assoc] using h1.trans_lt (h2.trans_le h3)
    refine ⟨P * r ^ k, hk_spec, ?_, hyltqP.trans_le hqP_le⟩
    rw [Nat.primeFactors_mul hPzero (pow_ne_zero _ hrprime.ne_zero), hPsupp,
      Nat.primeFactors_pow r hkpos.ne', hrprime.primeFactors]
    exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hrC)

private lemma accepted_delete_large {a : ℕ → ℕ} (ha : IsValidSeq a)
    {S : Finset ℕ} (hS : Accepted a S) {q : ℕ} (hq : q ∈ S) (hlarge : a 0 < q) :
    Accepted a (S.erase q) := by
  have hqprime : q.Prime := hS.2.1 q hq
  have hprimeErase : ∀ p ∈ S.erase q, p.Prime := by
    intro p hp
    exact hS.2.1 p (Finset.mem_of_mem_erase hp)
  have herase_nonempty : (S.erase q).Nonempty := by
    by_contra hempty
    have hSeq : S = {q} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hq, ?_⟩
      intro p hp
      by_contra hpq
      have : p ∈ S.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty] at this
    have haccq : Accepted a {q} := by simpa [hSeq] using hS
    have hqmem0 : q ∈ (a 0).primeFactors := by
      rcases haccq.2.2 0 with ⟨p, hp⟩
      have hpq : p = q := by simpa using (Finset.mem_inter.mp hp).1
      exact hpq ▸ (Finset.mem_inter.mp hp).2
    exact (not_lt_of_ge (Nat.le_of_mem_primeFactors hqmem0)) hlarge
  have main : ∀ m, a 0 < m → (∀ p ∈ m.primeFactors, p.Prime) →
      Accepted a m.primeFactors → q ∈ m.primeFactors → Accepted a (m.primeFactors.erase q) := by
    intro m hm0 hprimeM hmacc hqm
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_contra hreject
      let C := m.primeFactors.erase q
      have hCnonempty : C.Nonempty := by
        by_contra hCempty
        have hmSingleton : m.primeFactors = {q} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hqm, ?_⟩
          intro p hp
          by_contra hpq
          have : p ∈ C := Finset.mem_erase.mpr ⟨hpq, hp⟩
          simp [C, Finset.not_nonempty_iff_eq_empty.mp hCempty] at this
        have haccSingleton : Accepted a {q} := by simpa [hmSingleton] using hmacc
        have hqmem0 : q ∈ (a 0).primeFactors := by
          rcases haccSingleton.2.2 0 with ⟨p, hp⟩
          have hpq : p = q := by simpa using (Finset.mem_inter.mp hp).1
          exact hpq ▸ (Finset.mem_inter.mp hp).2
        exact (not_lt_of_ge (Nat.le_of_mem_primeFactors hqmem0)) hlarge
      obtain ⟨y, hy0, hysupp, hym⟩ := exists_smaller_after_erase (a 0) m q
        hm0 rfl hqm hqprime hlarge hCnonempty hprimeM
      have hnoty : y ∉ Set.range a := by
        intro hyrange
        obtain ⟨n, hn⟩ := hyrange
        have hn : a n = y := hn
        have hrangeacc := range_support_accepted ha n
        exact hreject (by simpa [C, hn, hysupp] using hrangeacc)
      obtain ⟨i, haiy, hgcd⟩ := skipped_has_coprime ha hy0 hnoty
      let B := (a i).primeFactors
      have hBacc : Accepted a B := range_support_accepted ha i
      have hdisjC : Disjoint B C := by
        have hBCeq : C = m.primeFactors.erase q := rfl
        rw [hBCeq, ← hysupp]
        apply (Nat.disjoint_primeFactors
          (ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 i)))
          (ne_of_gt (lt_of_le_of_lt (Nat.zero_le (a 0)) hy0))).mpr
        rw [Nat.coprime_iff_gcd_eq_one]
        simpa [Nat.gcd_comm] using hgcd
      rcases accepted_pairwise_inter ha hBacc hmacc with ⟨r, hr⟩
      have hrB : r ∈ B := (Finset.mem_inter.mp hr).1
      have hrM : r ∈ m.primeFactors := (Finset.mem_inter.mp hr).2
      have hrq : r = q := by
        by_contra hrne
        exact Finset.disjoint_left.mp hdisjC hrB
          (by exact Finset.mem_erase.mpr ⟨hrne, hrM⟩)
      have hqB : q ∈ B := hrq ▸ hrB
      have hBnum : a i < m := haiy.trans hym
      have hB0 : a 0 < a i := by
        have hmono : StrictMono a := strictMono_nat_of_lt_succ fun k => (ha.2 k).1
        have hi0 : i ≠ 0 := by
          intro hi
          subst i
          exact (not_lt_of_ge (Nat.le_of_mem_primeFactors hqB)) hlarge
        exact hmono (Nat.pos_of_ne_zero hi0)
      have hBdel : Accepted a (B.erase q) :=
        ih (a i) hBnum hB0 hBacc.2.1 hBacc hqB
      rcases accepted_pairwise_inter ha hBdel hmacc with ⟨r, hr⟩
      have hrBdel : r ∈ B.erase q := (Finset.mem_inter.mp hr).1
      have hrM : r ∈ m.primeFactors := (Finset.mem_inter.mp hr).2
      have hrne : r ≠ q := (Finset.mem_erase.mp hrBdel).1
      exact Finset.disjoint_left.mp hdisjC (Finset.mem_of_mem_erase hrBdel)
        (Finset.mem_erase.mpr ⟨hrne, hrM⟩)
  obtain ⟨M, hMlarge, hMsupport⟩ := exists_large_with_support (a 0) hS.1 hS.2.1
  simpa [hMsupport] using main M hMlarge (by simpa [hMsupport] using hS.2.1)
    (by simpa [hMsupport] using hS) (by simpa [hMsupport] using hq)

private lemma accepted_filter_small {a : ℕ → ℕ} (ha : IsValidSeq a)
    {S : Finset ℕ} (hS : Accepted a S) :
    Accepted a (S.filter (· ≤ a 0)) := by
  let Large := S.filter (a 0 < ·)
  have hdecomp : S \ Large = S.filter (· ≤ a 0) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hpS, hpnot⟩
      refine ⟨hpS, Nat.le_of_not_gt ?_⟩
      intro hlt
      exact hpnot (by simpa [Large] using (Finset.mem_filter.mpr ⟨hpS, hlt⟩))
    · rintro ⟨hpS, hple⟩
      refine ⟨hpS, ?_⟩
      intro hpLarge
      have hlt : a 0 < p := (Finset.mem_filter.mp (by simpa [Large] using hpLarge)).2
      omega
  have hdel : Accepted a (S \ Large) := by
    have general : ∀ U : Finset ℕ, U ⊆ Large → Accepted a (S \ U) := by
      intro U hU
      induction U using Finset.induction_on with
      | empty => simpa using hS
      | @insert q V hqV ih =>
        have hVsub : V ⊆ Large := fun p hp => hU (Finset.mem_insert_of_mem hp)
        have hqLarge : q ∈ Large := hU (Finset.mem_insert_self q V)
        have hqS : q ∈ S := (Finset.mem_filter.mp hqLarge).1
        have hqlarge : a 0 < q := (Finset.mem_filter.mp hqLarge).2
        have hprev : Accepted a (S \ V) := ih hVsub
        have hqprev : q ∈ S \ V := Finset.mem_sdiff.mpr ⟨hqS, hqV⟩
        have hnext := accepted_delete_large ha hprev hqprev hqlarge
        simpa [Finset.sdiff_insert] using hnext
    exact general Large (fun _ hp => hp)
  simpa [hdecomp] using hdel

private lemma support_shift_period (A x : ℕ) (hx : A ≤ x) :
    x.primeFactors ∩ Finset.Iic A = (x + Nat.factorial A).primeFactors ∩ Finset.Iic A := by
  ext p
  constructor
  · intro h
    have hpx : p ∈ x.primeFactors := (Finset.mem_inter.mp h).1
    have hpA : p ≤ A := by simpa using (Finset.mem_inter.mp h).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpx
    have hpdvdx : p ∣ x := Nat.dvd_of_mem_primeFactors hpx
    have hpdvdfact : p ∣ Nat.factorial A := Nat.dvd_factorial hpprime.pos hpA
    have hsum0 : x + Nat.factorial A ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (Nat.factorial_pos A) (Nat.le_add_left (Nat.factorial A) x))
    exact Finset.mem_inter.mpr ⟨hpprime.mem_primeFactors (dvd_add hpdvdx hpdvdfact) hsum0,
      by simpa using hpA⟩
  · intro h
    have hpsum : p ∈ (x + Nat.factorial A).primeFactors := (Finset.mem_inter.mp h).1
    have hpA : p ≤ A := by simpa using (Finset.mem_inter.mp h).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpsum
    have hpdvdsum : p ∣ x + Nat.factorial A := Nat.dvd_of_mem_primeFactors hpsum
    have hpdvdfact : p ∣ Nat.factorial A := Nat.dvd_factorial hpprime.pos hpA
    have hpdvdx : p ∣ x := (Nat.dvd_add_left hpdvdfact).mp hpdvdsum
    have hx0 : x ≠ 0 := by
      have hA0 : 0 < A := lt_of_lt_of_le hpprime.pos hpA
      exact ne_of_gt (hA0.trans_le hx)
    exact Finset.mem_inter.mpr ⟨hpprime.mem_primeFactors hpdvdx hx0, by simpa using hpA⟩

private lemma range_iff_shift {a : ℕ → ℕ} (ha : IsValidSeq a) {x : ℕ} (hx : a 0 ≤ x) :
    x ∈ Set.range a ↔ x + Nat.factorial (a 0) ∈ Set.range a := by
  have hxfact : 0 < Nat.factorial (a 0) := Nat.factorial_pos _
  have hsmallEq := support_shift_period (a 0) x hx
  constructor
  · rintro ⟨n, rfl⟩
    have hacc : Accepted a (a n).primeFactors := range_support_accepted ha n
    have hcore := accepted_filter_small ha hacc
    apply greedy_range ha
    · nlinarith [hxfact]
    · intro m
      have hinter := hcore.2.2 m
      rcases hinter with ⟨p, hp⟩
      have hpCore : p ∈ (a n).primeFactors.filter (· ≤ a 0) := (Finset.mem_inter.mp hp).1
      have hpam : p ∈ (a m).primeFactors := (Finset.mem_inter.mp hp).2
      have hpSmall : p ≤ a 0 := (Finset.mem_filter.mp hpCore).2
      have hpshift : p ∈ (a n + Nat.factorial (a 0)).primeFactors := by
        have hpInter : p ∈ (a n).primeFactors ∩ Finset.Iic (a 0) :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hpCore).1, by simp [hpSmall]⟩
        have hle : a 0 ≤ a n :=
          (strictMono_nat_of_lt_succ fun k => (ha.2 k).1).monotone (Nat.zero_le n)
        exact (Finset.mem_inter.mp ((support_shift_period (a 0) (a n) hle) ▸ hpInter)).1
      have hshift0 : a n + Nat.factorial (a 0) ≠ 0 := by omega
      have ham0 : a m ≠ 0 := ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 m))
      rw [← Nat.nonempty_primeFactors, Nat.primeFactors_gcd hshift0 ham0]
      exact ⟨p, Finset.mem_inter.mpr ⟨hpshift, hpam⟩⟩
  · intro hshift
    obtain ⟨n, hn⟩ := hshift
    have hacc : Accepted a (x + Nat.factorial (a 0)).primeFactors := by
      simpa [hn] using range_support_accepted ha n
    have hcore := accepted_filter_small ha hacc
    by_cases hxeq : x = a 0
    · exact ⟨0, hxeq.symm⟩
    · apply greedy_range ha (lt_of_le_of_ne hx (Ne.symm hxeq))
      intro m
      rcases hcore.2.2 m with ⟨p, hp⟩
      have hpCore : p ∈ (x + Nat.factorial (a 0)).primeFactors.filter (· ≤ a 0) :=
        (Finset.mem_inter.mp hp).1
      have hpam : p ∈ (a m).primeFactors := (Finset.mem_inter.mp hp).2
      have hpSmall : p ≤ a 0 := (Finset.mem_filter.mp hpCore).2
      have hpx : p ∈ x.primeFactors := by
        have hpInter : p ∈ (x + Nat.factorial (a 0)).primeFactors ∩ Finset.Iic (a 0) :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hpCore).1, by simp [hpSmall]⟩
        exact (Finset.mem_inter.mp (hsmallEq ▸ hpInter)).1
      have hx0 : x ≠ 0 := by omega
      have ham0 : a m ≠ 0 := ne_of_gt (lt_trans (Nat.zero_lt_one) (ha.1 m))
      rw [← Nat.nonempty_primeFactors, Nat.primeFactors_gcd hx0 ham0]
      exact ⟨p, Finset.mem_inter.mpr ⟨hpx, hpam⟩⟩

theorem imo2026_p6 (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  let L := Nat.factorial (a 0)
  have hLpos : 0 < L := Nat.factorial_pos _
  have ha0shift : a 0 + L ∈ Set.range a :=
    (range_iff_shift ha (x := a 0) le_rfl).mp ⟨0, rfl⟩
  let T := Nat.find ha0shift
  have hTvalue : a T = a 0 + L := Nat.find_spec ha0shift
  have hTpos : 0 < T := by
    by_contra hT
    have hT0 : T = 0 := Nat.eq_zero_of_not_pos hT
    simp [hT0] at hTvalue
    omega
  refine ⟨T, L, hTpos, hLpos, ?_⟩
  have hmono : StrictMono a := strictMono_nat_of_lt_succ fun k => (ha.2 k).1
  have hmem : ∀ n, a n + L ∈ Set.range a := by
    intro n
    exact (range_iff_shift ha (x := a n) (hmono.monotone (Nat.zero_le n))).mp ⟨n, rfl⟩
  let f : ℕ → ℕ := fun n => Nat.find (hmem n)
  have hfvalue : ∀ n, a (f n) = a n + L := fun n => Nat.find_spec (hmem n)
  have hfzero : f 0 = T := by
    apply hmono.injective
    simp [hfvalue, hTvalue]
  have hfmono : StrictMono f := by
    intro m n hmn
    apply (hmono.lt_iff_lt).mp
    rw [hfvalue, hfvalue]
    exact Nat.add_lt_add_right (hmono hmn) L
  have hfindex : ∀ n, f n = n + T := by
    intro n
    induction n with
    | zero => simpa using hfzero
    | succ n ih =>
      have hlower : n + T + 1 ≤ f (n + 1) := by
        have hlt : f n < f (n + 1) := hfmono (Nat.lt_succ_self n)
        omega
      have htarget : n + 1 + T = n + T + 1 := by omega
      rw [htarget]
      apply Nat.le_antisymm ?_ hlower
      by_contra hnotle
      have hgap : n + T + 1 < f (n + 1) := Nat.lt_of_not_ge hnotle
      let j := n + T + 1
      have hTj : T ≤ j := by omega
      have haTj : a T ≤ a j := hmono.monotone hTj
      have hbase : a 0 + L ≤ a j := by simpa [hTvalue] using haTj
      have hLaj : L ≤ a j := le_trans (Nat.le_add_left L (a 0)) hbase
      have hxbase : a 0 ≤ a j - L := Nat.le_sub_of_add_le hbase
      have hback : a j - L ∈ Set.range a := by
        apply (range_iff_shift ha hxbase).mpr
        have hadd : a j - L + L = a j := Nat.sub_add_cancel hLaj
        exact ⟨j, hadd.symm⟩
      obtain ⟨r, hr⟩ := hback
      have hfrj : f r = j := by
        apply hmono.injective
        rw [hfvalue, hr]
        exact Nat.sub_add_cancel hLaj
      have hrlt : r < n + 1 := by
        apply (hfmono.lt_iff_lt).mp
        rw [hfrj]
        exact hgap
      have hfrle : f r ≤ f n := hfmono.monotone (Nat.le_of_lt_succ hrlt)
      rw [hfrj, ih] at hfrle
      omega
  intro n
  rw [← hfindex n]
  exact hfvalue n

end IMO2026P6
