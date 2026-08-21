/-
Verified with Lean 4.30.0-rc2 and Mathlib v4.30.0-rc2.
-/

import Mathlib
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.PicardGroup

set_option maxHeartbeats 1000000

namespace IMO2026P3

noncomputable section
open scoped BigOperators

def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum


def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

/-- The exact value of the game. -/
def answer (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

lemma answer_den_pos (n : ℕ) : 0 < (2 : ℝ) ^ (n + 1) - 1 := by
  have hpow : (1 : ℝ) < 2 ^ (n + 1) := by
    exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  linarith

lemma answer_pos (n : ℕ) : 0 < answer n := by
  unfold answer
  exact div_pos (pow_pos (by norm_num) n) (answer_den_pos n)

lemma answer_le_one (n : ℕ) : answer n ≤ 1 := by
  unfold answer
  rw [div_le_one (answer_den_pos n)]
  rw [pow_succ]
  have h : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith

def evenSumFrom (k : ℕ) (xs : List ℝ) : ℝ :=
  ((xs.zipIdx k).filter (fun p => p.2 % 2 = 0)).map Prod.fst |>.sum

lemma evenSumFrom_add_two (k : ℕ) (xs : List ℝ) :
    evenSumFrom (k + 2) xs = evenSumFrom k xs := by
  induction xs generalizing k with
  | nil => simp [evenSumFrom]
  | cons x xs ih =>
      simp only [evenSumFrom, List.zipIdx_cons, List.filter_cons]
      have hmod : (k + 2) % 2 = k % 2 := by omega
      simp only [hmod]
      split
      · simp only [List.map_cons, List.sum_cons]
        congr 1
        simpa only [evenSumFrom, Nat.add_assoc] using ih (k + 1)
      · simpa only [evenSumFrom, Nat.add_assoc] using ih (k + 1)

/-- Alternating sum, beginning with a positive sign. -/
def altSum : List ℝ → ℝ
  | [] => 0
  | x :: xs => x - altSum xs

lemma sum_add_altSum (xs : List ℝ) :
    xs.sum + altSum xs = 2 * evenSumFrom 0 xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [altSum, evenSumFrom]
  | singleton x => simp [altSum, evenSumFrom, two_mul]
  | cons_cons x y xs ih =>
      rw [show altSum (x :: y :: xs) = x - (y - altSum xs) by rfl]
      simp only [List.sum_cons]
      rw [show evenSumFrom 0 (x :: y :: xs) = x + evenSumFrom 2 xs by
        simp [evenSumFrom]]
      rw [evenSumFrom_add_two]
      linarith

lemma zipWith_sub_sum : ∀ (xs ys : List ℝ), ys = xs.tail → ys.length = xs.length - 1 →
    (List.zipWith (fun a b : ℝ => b - a) xs ys).sum = xs.getLastD 0 - xs.getD 0 0 := by
  intro xs
  induction xs with
  | nil => intro ys hys _; subst ys; simp
  | cons x xs ih =>
      intro ys hys _
      subst ys
      cases xs with
      | nil => simp
      | cons y ys =>
          simp only [List.tail_cons, List.zipWith, List.sum_cons]
          have h := ih (ys := ys) rfl (by simp)
          simp only [List.getD_cons_zero]
          rw [h]
          simp

lemma pieceLengths_sum (S : Finset ℝ) : (pieceLengths S).sum = 1 := by
  unfold pieceLengths
  let l : List ℝ := (0 : ℝ) :: S.sort (· ≤ ·) ++ [1]
  change (List.zipWith (fun a b : ℝ => b - a) l l.tail).sum = 1
  rw [zipWith_sub_sum l l.tail rfl (by simp)]
  change ((0 :: S.sort (· ≤ ·) ++ [1]).getLast?.getD 0 - 0) = 1
  rw [List.getLast?_append]
  simp

lemma pieceLengths_length (S : Finset ℝ) : (pieceLengths S).length = S.card + 1 := by
  unfold pieceLengths
  simp

lemma zipWith_adjacent_sub_nonneg : ∀ (xs : List ℝ), xs.Pairwise (· ≤ ·) →
    ∀ x ∈ List.zipWith (fun a b : ℝ => b - a) xs xs.tail, 0 ≤ x := by
  intro xs hxs x hx
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      cases xs with
      | nil => simp at hx
      | cons b ys =>
          simp only [List.tail_cons, List.zipWith, List.mem_cons] at hx
          rw [List.pairwise_cons] at hxs
          rcases hx with rfl | hx
          · exact sub_nonneg.mpr (hxs.1 b (by simp))
          · exact ih hxs.2 hx

lemma pieceLengths_nonneg {S : Finset ℝ} (hS : (↑S : Set ℝ) ⊆ Set.Ioo 0 1) :
    ∀ x ∈ pieceLengths S, 0 ≤ x := by
  let l : List ℝ := (0 : ℝ) :: S.sort (· ≤ ·) ++ [1]
  have hsorted : l.Pairwise (· ≤ ·) := by
    dsimp [l]
    rw [List.pairwise_cons]
    constructor
    · intro y hy
      simp only [List.mem_append, Finset.mem_sort, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact le_of_lt (hS hy).1
      · norm_num
    · rw [List.pairwise_append]
      refine ⟨S.pairwise_sort (· ≤ ·), by simp, ?_⟩
      intro y hy z hz
      simp only [Finset.mem_sort] at hy
      simp only [List.mem_singleton] at hz
      subst z
      exact le_of_lt (hS hy).2
  intro x hx
  apply zipWith_adjacent_sub_nonneg l hsorted x
  simpa only [pieceLengths, l] using hx

def binaryMarks (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun k =>
    (((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n - k)) / ((2 : ℝ) ^ (n + 1) - 1))

lemma binaryMarks_mem (n k : ℕ) (hk : k < n) :
    (((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n - k)) / ((2 : ℝ) ^ (n + 1) - 1)) ∈
      binaryMarks n := by
  unfold binaryMarks
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩

lemma binaryMarks_injective (n : ℕ) : Function.Injective fun k : Fin n =>
    (((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n - k.1)) / ((2 : ℝ) ^ (n + 1) - 1)) := by
  intro i j hij
  apply Fin.ext
  have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := ne_of_gt (answer_den_pos n)
  have hnum := congrArg (fun z : ℝ => z * ((2 : ℝ) ^ (n + 1) - 1)) hij
  simp only [div_mul_cancel₀ _ hden] at hnum
  have hpow : (2 : ℝ) ^ (n - i.1) = 2 ^ (n - j.1) := by
    linarith
  have hexp : n - i.1 = n - j.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hlt
      exact this.ne hpow
    · have := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hgt
      exact this.ne hpow.symm
  omega

lemma binaryMarks_nat_injective (n : ℕ) : Set.InjOn
    (fun k : ℕ =>
      (((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n - k)) / ((2 : ℝ) ^ (n + 1) - 1)))
    (Finset.range n) := by
  intro i hi j hj hij
  have hi' : i < n := Finset.mem_range.mp hi
  have hj' : j < n := Finset.mem_range.mp hj
  have hfin : (⟨i, hi'⟩ : Fin n) = ⟨j, hj'⟩ :=
    binaryMarks_injective n hij
  exact Fin.ext_iff.mp hfin

lemma binaryMarks_card (n : ℕ) : (binaryMarks n).card = n := by
  unfold binaryMarks
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.mp hi
    have hj' : j < n := Finset.mem_range.mp hj
    have hfin : (⟨i, hi'⟩ : Fin n) = ⟨j, hj'⟩ :=
      binaryMarks_injective n hij
    exact Fin.ext_iff.mp hfin

lemma binaryMarks_in_interval (n : ℕ) :
    (↑(binaryMarks n) : Set ℝ) ⊆ Set.Ioo 0 1 := by
  intro x hx
  rw [Finset.mem_coe, binaryMarks, Finset.mem_image] at hx
  rcases hx with ⟨k, hk, rfl⟩
  have hklt : k < n := Finset.mem_range.mp hk
  have hden := answer_den_pos n
  constructor
  · apply div_pos
    · have hpow : (2 : ℝ) ^ (n - k) < 2 ^ (n + 1) := by
        exact pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
    · exact hden
  · rw [div_lt_one hden]
    have hpow : (1 : ℝ) < 2 ^ (n - k) := by
      exact one_lt_pow₀ (by norm_num) (by omega)
    linarith

lemma binaryMarks_admissible (n : ℕ) : AdmissibleMark n (binaryMarks n) := by
  exact ⟨binaryMarks_in_interval n, (binaryMarks_card n).le⟩

lemma firstPlayerShare_eq (xs : List ℝ) :
    firstPlayerShare xs = (xs.sum + altSum (xs.mergeSort (· ≥ ·))) / 2 := by
  rw [firstPlayerShare]
  change evenSumFrom 0 (xs.mergeSort (· ≥ ·)) = _
  have h := sum_add_altSum (xs.mergeSort (· ≥ ·))
  rw [List.Perm.sum_eq (List.mergeSort_perm xs (· ≥ ·))] at h
  linarith

lemma L_eq (A B : Finset ℝ) :
    L A B = (1 + altSum ((pieceLengths (A ∪ B)).mergeSort (· ≥ ·))) / 2 := by
  rw [L, firstPlayerShare_eq, pieceLengths_sum]


lemma altSum_duplicate_each_sorted : ∀ l : List ℝ, l.Pairwise (· ≥ ·) →
    altSum (l.flatMap fun x => [x / 2, x / 2]) = 0 := by
  intro l hl
  induction l with
  | nil => simp [altSum]
  | cons x l ih =>
      rw [List.pairwise_cons] at hl
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, altSum]
      linarith [ih hl.2]

lemma pairwise_duplicate_each_sorted {l : List ℝ} (hl : l.Pairwise (· ≥ ·)) :
    (l.flatMap fun x => [x / 2, x / 2]).Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.pairwise_cons] at hl
      simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      rw [List.pairwise_cons, List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_rfl
        · rcases List.mem_flatMap.mp hy with ⟨z, hz, hy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
              (hl.1 z hz)
          · rw [List.mem_singleton] at hy
            subst y
            exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
              (hl.1 z hz)
      · constructor
        · intro y hy
          rcases List.mem_flatMap.mp hy with ⟨z, hz, hy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
              (hl.1 z hz)
          · rw [List.mem_singleton] at hy
            subst y
            exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
              (hl.1 z hz)
        · exact ih hl.2

lemma firstPlayerShare_duplicate_each (l : List ℝ) :
    firstPlayerShare (l.flatMap fun x => [x / 2, x / 2]) = l.sum / 2 := by
  rw [firstPlayerShare_eq]
  let s := l.mergeSort (· ≥ ·)
  have hs : s.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) l
  have hperm :
      (s.flatMap fun x => [x / 2, x / 2]).Perm
        (l.flatMap fun x => [x / 2, x / 2]) :=
    (List.mergeSort_perm l (· ≥ ·)).flatMap (fun _ _ => List.Perm.refl _)
  have hsort :
      (l.flatMap fun x => [x / 2, x / 2]).mergeSort (· ≥ ·) =
        s.flatMap fun x => [x / 2, x / 2] := by
    apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
      (List.pairwise_mergeSort' (· ≥ ·) _) (pairwise_duplicate_each_sorted hs)
    exact (List.mergeSort_perm _ _).trans hperm.symm
  rw [hsort]
  have halt := altSum_duplicate_each_sorted s hs
  rw [halt]
  have hsum : (l.flatMap fun x => [x / 2, x / 2]).sum = l.sum := by
    clear s hs hperm hsort halt
    induction l with
    | nil => simp
    | cons x l ih =>
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.sum_cons]
        rw [ih]
        ring
  rw [hsum]
  ring

lemma altSum_sorted_nonneg {xs : List ℝ}
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) (hsorted : xs.Pairwise (· ≥ ·)) :
    0 ≤ altSum xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [altSum]
  | singleton x => simpa [altSum] using hnonneg x (by simp)
  | cons_cons x y xs ih =>
      rw [List.pairwise_cons, List.pairwise_cons] at hsorted
      have hxy : y ≤ x := hsorted.1 y (by simp)
      have hnonneg' : ∀ z ∈ xs, 0 ≤ z := by
        intro z hz
        exact hnonneg z (by simp [hz])
      have hih := ih hnonneg' hsorted.2.2
      simp only [altSum]
      linarith

lemma firstPlayerShare_ge_half {xs : List ℝ}
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) : xs.sum / 2 ≤ firstPlayerShare xs := by
  rw [firstPlayerShare_eq]
  have hsorted : (xs.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
    List.pairwise_mergeSort' (· ≥ ·) xs
  have hnonneg' : ∀ x ∈ xs.mergeSort (· ≥ ·), 0 ≤ x := by
    intro x hx
    exact hnonneg x ((List.mergeSort_perm xs (· ≥ ·)).mem_iff.mp hx)
  have halt := altSum_sorted_nonneg hnonneg' hsorted
  linarith

lemma altSum_le_sum_of_nonneg : ∀ xs : List ℝ,
    (∀ x ∈ xs, 0 ≤ x) → altSum xs ≤ xs.sum := by
  intro xs hnonneg
  induction xs using List.twoStepInduction with
  | nil => simp [altSum]
  | singleton x => simp [altSum]
  | cons_cons x y xs ih =>
      have hy : 0 ≤ y := hnonneg y (by simp)
      have hnonneg' : ∀ z ∈ xs, 0 ≤ z := by
        intro z hz
        exact hnonneg z (by simp [hz])
      have hih := ih hnonneg'
      simp only [altSum, List.sum_cons]
      linarith

lemma firstPlayerShare_le_sum {xs : List ℝ}
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) : firstPlayerShare xs ≤ xs.sum := by
  rw [firstPlayerShare_eq]
  have hnonneg' : ∀ x ∈ xs.mergeSort (· ≥ ·), 0 ≤ x := by
    intro x hx
    exact hnonneg x ((List.mergeSort_perm xs (· ≥ ·)).mem_iff.mp hx)
  have halt := altSum_le_sum_of_nonneg _ hnonneg'
  rw [List.Perm.sum_eq (List.mergeSort_perm xs (· ≥ ·))] at halt
  linarith

lemma L_bounds {A B : Finset ℝ}
    (hAB : (↑(A ∪ B) : Set ℝ) ⊆ Set.Ioo 0 1) :
    (1 : ℝ) / 2 ≤ L A B ∧ L A B ≤ 1 := by
  have hnonneg := pieceLengths_nonneg hAB
  constructor
  · rw [L]
    have h := firstPlayerShare_ge_half hnonneg
    rw [pieceLengths_sum] at h
    exact h
  · rw [L]
    calc
      firstPlayerShare (pieceLengths (A ∪ B)) ≤ (pieceLengths (A ∪ B)).sum :=
        firstPlayerShare_le_sum hnonneg
      _ = 1 := pieceLengths_sum _

lemma L_bounds_of_admissible {n : ℕ} {A B : Finset ℝ}
    (hA : AdmissibleMark n A) (hB : AdmissibleMark n B) :
    (1 : ℝ) / 2 ≤ L A B ∧ L A B ≤ 1 := by
  apply L_bounds
  intro x hx
  rw [Finset.mem_coe, Finset.mem_union] at hx
  exact hx.elim (fun hxA => hA.1 hxA) (fun hxB => hB.1 hxB)

lemma admissible_empty (n : ℕ) : AdmissibleMark n ∅ := by
  constructor <;> simp

lemma L_empty_empty : L ∅ ∅ = 1 := by
  norm_num [L, firstPlayerShare, pieceLengths]

lemma admissibleSubtypeNonempty (n : ℕ) :
    Nonempty {A : Finset ℝ // AdmissibleMark n A} :=
  ⟨⟨∅, admissible_empty n⟩⟩

lemma responseSubtypeNonempty (n : ℕ)
    (A : {A : Finset ℝ // AdmissibleMark n A}) :
    Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
  ⟨⟨∅, admissible_empty n, by simp⟩⟩

lemma V_ge_half (n : ℕ) : (1 : ℝ) / 2 ≤ V n := by
  let A0 : {A : Finset ℝ // AdmissibleMark n A} := ⟨∅, admissible_empty n⟩
  have hBddAbove : BddAbove (Set.range fun A : {A : Finset ℝ // AdmissibleMark n A} =>
      ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨A, rfl⟩
    let B0 : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨∅, admissible_empty n, by simp⟩
    have hBddBelow : BddBelow (Set.range fun B :
        {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1) := by
      refine ⟨(1 : ℝ) / 2, ?_⟩
      rintro _ ⟨B, rfl⟩
      exact (L_bounds_of_admissible A.2 B.2.1).1
    exact (ciInf_le hBddBelow B0).trans (L_bounds_of_admissible A.2 B0.2.1).2
  apply (le_ciSup hBddAbove A0).trans'
  letI := responseSubtypeNonempty n A0
  apply le_ciInf
  intro B
  exact (L_bounds_of_admissible A0.2 B.2.1).1

lemma V_le_one (n : ℕ) : V n ≤ 1 := by
  unfold V
  letI := admissibleSubtypeNonempty n
  apply ciSup_le
  intro A
  let B0 : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
    ⟨∅, admissible_empty n, by simp⟩
  have hBddBelow : BddBelow (Set.range fun B :
      {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1) := by
    refine ⟨(1 : ℝ) / 2, ?_⟩
    rintro _ ⟨B, rfl⟩
    exact (L_bounds_of_admissible A.2 B.2.1).1
  exact (ciInf_le hBddBelow B0).trans (L_bounds_of_admissible A.2 B0.2.1).2

lemma V_zero : V 0 = 1 := by
  apply le_antisymm (V_le_one 0)
  let A0 : {A : Finset ℝ // AdmissibleMark 0 A} := ⟨∅, admissible_empty 0⟩
  have hBddAbove : BddAbove (Set.range fun A : {A : Finset ℝ // AdmissibleMark 0 A} =>
      ⨅ B : {B : Finset ℝ // AdmissibleMark 0 B ∧ Disjoint A.1 B}, L A.1 B.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨A, rfl⟩
    let B0 : {B : Finset ℝ // AdmissibleMark 0 B ∧ Disjoint A.1 B} :=
      ⟨∅, admissible_empty 0, by simp⟩
    have hBddBelow : BddBelow (Set.range fun B :
        {B : Finset ℝ // AdmissibleMark 0 B ∧ Disjoint A.1 B} => L A.1 B.1) := by
      refine ⟨(1 : ℝ) / 2, ?_⟩
      rintro _ ⟨B, rfl⟩
      exact (L_bounds_of_admissible A.2 B.2.1).1
    exact (ciInf_le hBddBelow B0).trans (L_bounds_of_admissible A.2 B0.2.1).2
  apply (le_ciSup hBddAbove A0).trans'
  letI := responseSubtypeNonempty 0 A0
  apply le_ciInf
  intro B
  have hBempty : B.1 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp B.2.1.2)
  have hAempty : A0.1 = ∅ := rfl
  rw [hBempty, hAempty, L_empty_empty]


lemma one_le_abs_intCast {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  exact_mod_cast Int.one_le_abs hz

/-- Scaling the integral lower bound gives the desired `δ` lower bound. -/
lemma delta_le_abs_mul_intCast {δ : ℝ} (hδ : 0 ≤ δ) {z : ℤ} (hz : z ≠ 0) :
    δ ≤ |δ * (z : ℝ)| := by
  rw [abs_mul, abs_of_nonneg hδ]
  nlinarith [one_le_abs_intCast hz]

/-- A finite signed sum of natural powers of two is an integer. -/
def signedPowSum {m : ℕ} (color : Fin m → Bool) : ℤ :=
  ∑ i : Fin m, if color i then (2 : ℤ) ^ (i : ℕ) else -((2 : ℤ) ^ (i : ℕ))

/-- Key powers-of-two fact: a signed sum using every exponent exactly once cannot vanish. -/
lemma signedPowSum_ne_zero {m : ℕ} (hm : 0 < m) (color : Fin m → Bool) :
    signedPowSum color ≠ 0 := by
  cases m with
  | zero => simp at hm
  | succ m =>
      have htail :
          (2 : ℤ) ∣ ∑ i : Fin m,
            if color i.succ then (2 : ℤ) ^ (i.succ : ℕ)
            else -((2 : ℤ) ^ (i.succ : ℕ)) := by
        apply Finset.dvd_sum
        intro i _
        have hp : (2 : ℤ) ∣ (2 : ℤ) ^ (i.succ : ℕ) :=
          dvd_pow_self 2 (Nat.succ_ne_zero i)
        split
        · exact hp
        · exact dvd_neg.mpr hp
      have hmod : signedPowSum color % 2 = 1 := by
        rw [signedPowSum, Fin.sum_univ_succ]
        have htailmod := Int.dvd_iff_emod_eq_zero.mp htail
        rw [Int.add_emod, htailmod]
        cases color 0 <;> simp
      intro hzero
      rw [hzero] at hmod
      norm_num at hmod

lemma delta_le_abs_signedPowSum {m : ℕ} (hm : 0 < m) (color : Fin m → Bool)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ≤ |δ * (signedPowSum color : ℝ)| := by
  exact delta_le_abs_mul_intCast hδ (signedPowSum_ne_zero hm color)

/-- Signed powers on an arbitrary finite set of labels, as needed for one connected component. -/
def signedPowFinset (s : Finset ℕ) (color : ℕ → Bool) : ℤ :=
  ∑ i ∈ s, if color i then (2 : ℤ) ^ i else -((2 : ℤ) ^ i)

/-- A nonempty signed sum of distinct powers of two cannot vanish. The least exponent occurs once;
all other terms are divisible by the next power of two. -/
lemma signedPowFinset_ne_zero {s : Finset ℕ} (hs : s.Nonempty) (color : ℕ → Bool) :
    signedPowFinset s color ≠ 0 := by
  let k := s.min' hs
  have hk : k ∈ s := s.min'_mem hs
  have hdiv : (2 : ℤ) ^ (k + 1) ∣
      ∑ i ∈ s.erase k, if color i then (2 : ℤ) ^ i else -((2 : ℤ) ^ i) := by
    apply Finset.dvd_sum
    intro i hi
    have hki : k + 1 ≤ i := by
      have := Finset.min'_lt_of_mem_erase_min' s hs hi
      omega
    have hp : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ i := pow_dvd_pow 2 hki
    split
    · exact hp
    · exact dvd_neg.mpr hp
  intro hzero
  have hsplit :
      (∑ i ∈ s.erase k, if color i then (2 : ℤ) ^ i else -((2 : ℤ) ^ i)) +
        (if color k then (2 : ℤ) ^ k else -((2 : ℤ) ^ k)) = 0 := by
    rw [Finset.sum_erase_add s _ hk]
    exact hzero
  have htermDiv : (2 : ℤ) ^ (k + 1) ∣
      (if color k then (2 : ℤ) ^ k else -((2 : ℤ) ^ k)) := by
    have hEq : (if color k then (2 : ℤ) ^ k else -((2 : ℤ) ^ k)) =
        -(∑ i ∈ s.erase k, if color i then (2 : ℤ) ^ i else -((2 : ℤ) ^ i)) := by
      linarith
    rw [hEq]
    exact dvd_neg.mpr hdiv
  have hpowDiv : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ k := by
    split at htermDiv
    · exact htermDiv
    · exact dvd_neg.mp htermDiv
  have hfactor : (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
  rw [hfactor] at hpowDiv
  have hcancel : (2 : ℤ) ∣ 1 := by
    exact (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ k ≠ 0)).mp (by simpa using hpowDiv)
  norm_num at hcancel

lemma delta_le_abs_signedPowFinset {s : Finset ℕ} (hs : s.Nonempty)
    (color : ℕ → Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ≤ |δ * (signedPowFinset s color : ℝ)| := by
  exact delta_le_abs_mul_intCast hδ (signedPowFinset_ne_zero hs color)


/-- Pure pigeonhole core of the component-counting argument. If all components used at least as
many edges as vertices, the global edge count could not be smaller than the vertex count. -/
lemma exists_component_edge_lt_vertex {C : Type*} [Fintype C]
    (edges vertices : C → ℕ)
    (hglobal : (∑ c : C, edges c) < ∑ c : C, vertices c) :
    ∃ c, edges c < vertices c := by
  by_contra h
  have hall : ∀ c, vertices c ≤ edges c := by
    intro c
    by_contra hc
    apply h
    exact ⟨c, by omega⟩
  exact (not_le_of_gt hglobal) (Finset.sum_le_sum fun c _ => hall c)

/-- In a connected simple component, having fewer edges than vertices forces the exact tree count. -/
lemma connected_component_isTree_of_edge_lt_vertex {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (hconn : G.Connected)
    (hcard : Fintype.card G.edgeSet < Fintype.card V) : G.IsTree := by
  apply (G.isTree_iff_connected_and_card).2
  refine ⟨hconn, ?_⟩
  have hlower := hconn.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hE : Nat.card G.edgeSet = Fintype.card G.edgeSet := Nat.card_eq_fintype_card
  rw [hV, hE] at hlower ⊢
  omega

/-- Every connected simple graph has a spanning tree. This is useful after discarding parallel
copies of pair edges; connectivity and the two-coloring constraint are unchanged. -/
lemma connected_simple_graph_has_spanning_tree {V : Type*} [Finite V]
    (G : SimpleGraph V) (hG : G.Connected) : ∃ T ≤ G, T.IsTree := by
  exact hG.exists_isTree_le

lemma tree_has_two_coloring {V : Type*} (G : SimpleGraph V) (hG : G.IsTree) :
    G.Colorable 2 := hG.colorable_two

/-- A signed sum of base weights is controlled by an `L¹` budget of edge discrepancies. This
packages the final triangle-inequality step independently of graph representation choices. -/
lemma signed_vertex_sum_le_edge_budget {V E : Type*} [Fintype V] [Fintype E]
    (weight : V → ℝ) (color : V → Bool) (edgeError : E → ℝ)
    (balance : (∑ v : V, if color v then weight v else -weight v) = ∑ e : E, edgeError e)
    (budget : ∀ e, |edgeError e| ≤ edgeError e) :
    |∑ v : V, if color v then weight v else -weight v| ≤ ∑ e : E, edgeError e := by
  rw [balance]
  calc
    |∑ e : E, edgeError e| ≤ ∑ e : E, |edgeError e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : E, edgeError e := Finset.sum_le_sum fun e _ => budget e

/-- Combined arithmetic endpoint of the graph argument: once a tree component supplies a coloring
whose vertex-weight balance is represented by pair discrepancies, that component costs at least
`δ` in the global alternating-sum budget. -/
lemma delta_le_edge_budget_of_signedPow_balance {m : ℕ} (hm : 0 < m)
    (color : Fin m → Bool) {δ : ℝ} (hδ : 0 ≤ δ) {E : Type*} [Fintype E]
    (edgeError : E → ℝ)
    (balance : δ * (signedPowSum color : ℝ) = ∑ e : E, edgeError e)
    (budget : ∀ e, |edgeError e| ≤ edgeError e) :
    δ ≤ ∑ e : E, edgeError e := by
  apply (delta_le_abs_signedPowSum hm color hδ).trans
  rw [balance]
  calc
    |∑ e : E, edgeError e| ≤ ∑ e : E, |edgeError e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : E, edgeError e := Finset.sum_le_sum fun e _ => budget e


/-! ### Generic lower-bound theorem -/

/-- The sorted fragment list, in descending order. -/
def sortedFragments (blocks : List (List ℝ)) : List ℝ :=
  blocks.flatten.mergeSort (· ≥ ·)

/-- A fragment in the sorted list is positive when it lies at an even index and negative when it
lies at an odd index. -/
def sortedSign {blocks : List (List ℝ)} (i : Fin (sortedFragments blocks).length) : ℝ :=
  if Even (i : ℕ) then 1 else -1

/-- The alternating sum is the signed finite sum over positions. -/
lemma altSum_eq_sum_sortedSign (xs : List ℝ) :
    altSum xs = ∑ i : Fin xs.length, (if Even (i : ℕ) then 1 else -1) * xs.get i := by
  induction xs with
  | nil => simp [altSum]
  | cons x xs ih =>
      rw [altSum, ih]
      change x - (∑ i : Fin xs.length,
        (if Even (i : ℕ) then 1 else -1) * xs.get i) =
        ∑ i : Fin (xs.length + 1),
          (if Even (i : ℕ) then 1 else -1) * (x :: xs).get i
      rw [Fin.sum_univ_succ]
      simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
        List.getElem_cons_succ]
      simp only [show Even 0 by norm_num, if_true, one_mul]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rcases Nat.even_or_odd (i : ℕ) with hi | hi
      · simp [hi, hi.add_one]
      · have hn : ¬ Even (i : ℕ) := Nat.not_even_iff_odd.mpr hi
        have he : Even ((i : ℕ) + 1) := hi.add_one
        split <;> simp_all

/-- The list model of a refinement: exactly `m` blocks, nonnegative fragments, geometric block
sums, and fewer than twice as many fragments as blocks. -/
structure GeometricRefinement (δ : ℝ) (m : ℕ) where
  blocks : List (List ℝ)
  blocks_length : blocks.length = m
  nonneg : ∀ x ∈ blocks.flatten, 0 ≤ x
  block_sum : ∀ i : Fin m, (blocks.get (Fin.cast blocks_length.symm i)).sum = δ * (2 : ℝ) ^ (i : ℕ)
  fragment_count : blocks.flatten.length ≤ 2 * m - 1

namespace GeometricRefinement

variable {δ : ℝ} {m : ℕ} (R : GeometricRefinement δ m)

abbrev SortedIndex := Fin (sortedFragments R.blocks).length

structure Occurrence (R : GeometricRefinement δ m) where
  block : Fin m
  offset : Fin (R.blocks.get (Fin.cast R.blocks_length.symm block)).length
  deriving DecidableEq, Fintype

namespace Occurrence

/-- The value of a labelled fragment occurrence. -/
def value (p : R.Occurrence) : ℝ :=
  (R.blocks.get (Fin.cast R.blocks_length.symm p.block)).get p.offset

end Occurrence

/-- The canonical list of all labelled occurrences. -/
noncomputable def occurrenceList : List R.Occurrence :=
  (List.ofFn fun i : Fin m =>
    List.ofFn fun j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length =>
      (⟨i, j⟩ : R.Occurrence)).flatten

lemma occurrenceList_nodup : R.occurrenceList.Nodup := by
  unfold occurrenceList
  rw [List.nodup_flatten]
  constructor
  · intro l hl
    simp only [List.mem_ofFn] at hl
    rcases hl with ⟨i, rfl⟩
    exact List.nodup_ofFn.mpr fun a b h => by
      have hoff := congrArg (fun p : R.Occurrence => (p.offset : ℕ)) h
      apply Fin.eq_of_val_eq
      exact hoff
  · rw [List.pairwise_ofFn]
    intro i j hij
    rw [List.disjoint_left]
    intro p hpi hpj
    simp only [List.mem_ofFn] at hpi hpj
    rcases hpi with ⟨a, rfl⟩
    rcases hpj with ⟨b, h⟩
    exact (Fin.ne_of_lt hij) (congrArg Occurrence.block h).symm

lemma occurrence_mem (p : R.Occurrence) : p ∈ R.occurrenceList := by
  rcases p with ⟨i, j⟩
  simp [occurrenceList]

lemma map_occurrence_values :
    R.occurrenceList.map (fun p : R.Occurrence => p.value) = R.blocks.flatten := by
  unfold occurrenceList
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_ofFn]
  apply List.ext_getElem
  · simp [R.blocks_length]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn, Function.comp_apply, List.map_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      rw [List.getElem_ofFn]
      rfl

lemma occurrenceList_length :
    R.occurrenceList.length = R.blocks.flatten.length := by
  simpa using congrArg List.length R.map_occurrence_values

/-- The merge-sort permutation, oriented from sorted positions back to flattened source
positions. Equal fragment values are disambiguated by `List.Perm.idxBij`. -/
def sortedFragments_perm_flatten :
    (sortedFragments R.blocks).Perm R.blocks.flatten := by
  exact R.blocks.flatten.mergeSort_perm (· ≥ ·)

/-- The index bijection supplied by the sorting permutation. -/
noncomputable def sortedIndexEquivFlatten :
    Fin (sortedFragments R.blocks).length ≃ Fin R.blocks.flatten.length :=
  Equiv.ofBijective R.sortedFragments_perm_flatten.idxBij
    ⟨R.sortedFragments_perm_flatten.idxBij_injective,
      R.sortedFragments_perm_flatten.idxBij_surjective⟩

/-- Flattened positions are canonically equivalent to their labelled occurrences. -/
noncomputable def flattenIndexEquivOccurrence :
    Fin R.blocks.flatten.length ≃ R.Occurrence :=
  (finCongr R.occurrenceList_length.symm).trans
    (R.occurrenceList_nodup.getEquivOfForallMemList _ R.occurrence_mem)

/-- Sorted positions are labelled by transporting them through `List.Perm.idxBij` and then
reading the source occurrence. -/
noncomputable def positionEquivOccurrence :
    Fin (sortedFragments R.blocks).length ≃ R.Occurrence :=
  R.sortedIndexEquivFlatten.trans R.flattenIndexEquivOccurrence

/-- Each sorted position is labelled by its original block. Equal values are disambiguated by
sorting labelled occurrences rather than the values themselves. -/
noncomputable def label (p : R.SortedIndex) : Fin m :=
  (R.positionEquivOccurrence p).block

/-- The flattened source list contains the value of each occurrence at the matching canonical
position. -/
lemma get_flatten_eq_occurrence (j : Fin R.blocks.flatten.length) :
    R.blocks.flatten.get j = (R.flattenIndexEquivOccurrence j).value := by
  let k : Fin R.occurrenceList.length := Fin.cast R.occurrenceList_length.symm j
  have hmap := congrArg (fun l : List ℝ => l[(j : ℕ)]?) R.map_occurrence_values
  dsimp only at hmap
  have hklt : (j : ℕ) < R.occurrenceList.length := by
    rw [R.occurrenceList_length]
    exact j.isLt
  rw [List.getElem?_map, List.getElem?_eq_getElem hklt,
    List.getElem?_eq_getElem j.isLt] at hmap
  simpa only [Option.map_some, Option.some.injEq] using hmap.symm

/-- Sorted positions carry the value of the source occurrence selected by `idxBij`. -/
lemma get_sorted_eq_occurrence (p : R.SortedIndex) :
    (sortedFragments R.blocks).get p = (R.positionEquivOccurrence p).value := by
  have hsort := R.sortedFragments_perm_flatten.getElem_idxBij_eq_getElem p
  have hsource := R.get_flatten_eq_occurrence (R.sortedIndexEquivFlatten p)
  exact hsort.symm.trans hsource


/-- Every block label occurs, since its positive geometric sum forces a positive-length block. -/
lemma block_nonempty (hδ : 0 < δ) (i : Fin m) :
    (R.blocks.get (Fin.cast R.blocks_length.symm i)).length > 0 := by
  by_contra h
  have hz : (R.blocks.get (Fin.cast R.blocks_length.symm i)).length = 0 := by omega
  have hs : (R.blocks.get (Fin.cast R.blocks_length.symm i)).sum = 0 := by
    rw [List.length_eq_zero_iff.mp hz]
    simp
  rw [R.block_sum i] at hs
  have hp : 0 < δ * (2 : ℝ) ^ (i : ℕ) := mul_pos hδ (by positivity)
  linarith

/-- The sorted-position labels are onto: every geometric base block owns at least one fragment. -/
lemma label_surjective (hδ : 0 < δ) : Function.Surjective R.label := by
  intro i
  let p : R.Occurrence :=
    ⟨i, ⟨0, R.block_nonempty hδ i⟩⟩
  let r : R.SortedIndex := R.positionEquivOccurrence.symm p
  refine ⟨r, ?_⟩
  unfold label
  rw [Equiv.apply_symm_apply]

/-- A finite label map whose domain has size at most `2m-1` is the combinatorial core of the
fragment problem. -/
lemma label_domain_lt_twice (hm : 0 < m) : (sortedFragments R.blocks).length < 2 * m := by
  have hlen : (sortedFragments R.blocks).length = R.blocks.flatten.length := by
    simp [sortedFragments]
  rw [hlen]
  calc
    R.blocks.flatten.length ≤ 2 * m - 1 := R.fragment_count
    _ < 2 * m := by omega

/-- The adjacent sorted pairs that cross between distinct base blocks. -/
abbrev CrossPair := {q : Fin ((sortedFragments R.blocks).length / 2) //
  R.label ⟨2 * (q : ℕ), by omega⟩ ≠ R.label ⟨2 * (q : ℕ) + 1, by omega⟩}

/-- The two endpoint labels of a crossing pair. -/
def crossPairEnds (q : R.CrossPair) : Sym2 (Fin m) :=
  s(R.label ⟨2 * (q.1 : ℕ), by omega⟩,
    R.label ⟨2 * (q.1 : ℕ) + 1, by omega⟩)

/-- The simple graph underlying the crossing-pair multigraph. -/
def pairGraph (R : GeometricRefinement δ m) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ ∃ q : Fin ((sortedFragments R.blocks).length / 2),
    R.label ⟨2 * (q : ℕ), by omega⟩ = i ∧
    R.label ⟨2 * (q : ℕ) + 1, by omega⟩ = j ∨
    R.label ⟨2 * (q : ℕ), by omega⟩ = j ∧
    R.label ⟨2 * (q : ℕ) + 1, by omega⟩ = i
  symm i j h := ⟨h.1.symm, by
    rcases h.2 with ⟨q, hq | hq⟩
    · exact ⟨q, Or.inr hq⟩
    · exact ⟨q, Or.inl hq⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Pure finite-map component counting. Pair the domain consecutively, build a graph on labels
from the crossing pairs, and some component has fewer crossing pairs than vertices. -/
lemma finite_labels_sparse_component {n m : ℕ} (label : Fin n → Fin m)
    (hcount : n < 2 * m) :
    let G : SimpleGraph (Fin m) := {
      Adj := fun i j => i ≠ j ∧ ∃ q : Fin (n / 2),
        label ⟨2 * (q : ℕ), by omega⟩ = i ∧ label ⟨2 * (q : ℕ) + 1, by omega⟩ = j ∨
        label ⟨2 * (q : ℕ), by omega⟩ = j ∧ label ⟨2 * (q : ℕ) + 1, by omega⟩ = i
      symm := by
        intro i j h
        rcases h with ⟨hne, q, hq | hq⟩
        · exact ⟨hne.symm, q, Or.inr hq⟩
        · exact ⟨hne.symm, q, Or.inl hq⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
    ∃ C : G.ConnectedComponent,
      {q : Fin (n / 2) |
        G.connectedComponentMk (label ⟨2 * (q : ℕ), by omega⟩) = C}.ncard < C.supp.ncard := by
  dsimp only
  let G : SimpleGraph (Fin m) := {
    Adj := fun i j => i ≠ j ∧ ∃ q : Fin (n / 2),
      label ⟨2 * (q : ℕ), by omega⟩ = i ∧ label ⟨2 * (q : ℕ) + 1, by omega⟩ = j ∨
      label ⟨2 * (q : ℕ), by omega⟩ = j ∧ label ⟨2 * (q : ℕ) + 1, by omega⟩ = i
    symm := by
      intro i j h
      rcases h with ⟨hne, q, hq | hq⟩
      · exact ⟨hne.symm, q, Or.inr hq⟩
      · exact ⟨hne.symm, q, Or.inl hq⟩
    loopless := ⟨fun i h => h.1 rfl⟩ }
  change ∃ C : G.ConnectedComponent, _
  classical
  let first : Fin (n / 2) → Fin m := fun q => label ⟨2 * (q : ℕ), by omega⟩
  let second : Fin (n / 2) → Fin m := fun q => label ⟨2 * (q : ℕ) + 1, by omega⟩
  let comp : Fin m → G.ConnectedComponent := G.connectedComponentMk
  let edges : G.ConnectedComponent → ℕ := fun C =>
    (Finset.univ.filter fun q : Fin (n / 2) => comp (first q) = C).card
  let vertices : G.ConnectedComponent → ℕ := fun C => C.supp.toFinset.card
  have hedge : (∑ C, edges C) = n / 2 := by
    calc
      (∑ C, edges C) = (Finset.univ : Finset (Fin (n / 2))).card := by
        rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
          (f := fun q : Fin (n / 2) => comp (first q))
          (by intro q hq; exact Finset.mem_univ _)]
      _ = n / 2 := Fintype.card_fin _
  have hvert : (∑ C, vertices C) = m := by
    simp only [vertices]
    rw [← Finset.card_biUnion (s := Finset.univ)
      (t := fun C : G.ConnectedComponent => C.supp.toFinset)]
    · rw [show (Finset.univ.biUnion fun C : G.ConnectedComponent => C.supp.toFinset) =
          (Finset.univ : Finset (Fin m)) by
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
        exact ⟨fun _ => trivial, fun _ => ⟨G.connectedComponentMk v,
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩]
      simp
    · intro C _ D _ hCD
      exact Set.disjoint_toFinset.mpr
        (SimpleGraph.pairwise_disjoint_supp_connectedComponent G hCD)
  have hsparse : ∃ C, edges C < vertices C := by
    apply exists_component_edge_lt_vertex edges vertices
    rw [hvert]
    have hhalf : n / 2 < m := by omega
    omega
  rcases hsparse with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  have hset : {q : Fin (n / 2) |
        G.connectedComponentMk (label ⟨2 * (q : ℕ), by omega⟩) = C}.toFinset =
      Finset.univ.filter fun q : Fin (n / 2) => comp (first q) = C := by
    ext q
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [Set.ncard_eq_toFinset_card', hset]
  rw [show C.supp.ncard = C.supp.toFinset.card by exact Set.ncard_eq_toFinset_card' C.supp]
  exact hC

/-- The key combinatorial estimate: some connected component of the pair graph has fewer
occurrence-pairs than vertices. -/
lemma exists_sparse_component (hm : 0 < m) :
    ∃ C : R.pairGraph.ConnectedComponent,
      {q : Fin ((sortedFragments R.blocks).length / 2) |
        R.pairGraph.connectedComponentMk (R.label ⟨2 * (q : ℕ), by omega⟩) = C}.ncard < C.supp.ncard := by
  simpa only [pairGraph] using
    (finite_labels_sparse_component R.label (R.label_domain_lt_twice hm))

/-- The sorted labelled-occurrence representation is a duplicate-free enumeration. -/
lemma occurrenceModel (R : GeometricRefinement δ m) :
    ∃ occ : List R.Occurrence,
      occ.Nodup ∧ (∀ p : R.Occurrence, p ∈ occ) ∧
      occ.map (fun p : R.Occurrence => p.value) = R.blocks.flatten := by
  refine ⟨R.occurrenceList, R.occurrenceList_nodup, R.occurrence_mem, R.map_occurrence_values⟩

/-- A finite sigma-type equivalence for occurrence labels. -/
noncomputable def occurrenceEquivSigma : R.Occurrence ≃
    Σ i : Fin m, Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length where
  toFun p := ⟨p.block, p.offset⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Reindexing any sign assignment on blocks over the sorted labelled occurrences recovers the
geometric signed power sum. -/
lemma signed_block_sum (R : GeometricRefinement δ m) (color : Fin m → Bool) :
    (∑ p : R.SortedIndex,
      if color (R.label p) then (sortedFragments R.blocks).get p
      else -(sortedFragments R.blocks).get p) =
      δ * (signedPowSum color : ℝ) := by
  classical
  let e : R.SortedIndex ≃ R.Occurrence := R.positionEquivOccurrence
  have hleft : (∑ p : R.SortedIndex,
      if color (R.label p) then (sortedFragments R.blocks).get p
      else -(sortedFragments R.blocks).get p) =
      ∑ p : R.Occurrence, if color p.block then p.value else -p.value := by
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro p _
    have he : e p = R.positionEquivOccurrence p := rfl
    rw [he, ← R.get_sorted_eq_occurrence p]
    rfl
  rw [hleft]
  rw [show (∑ p : R.Occurrence, if color p.block then p.value else -p.value) =
      ∑ p : Σ i : Fin m, Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
        if color p.1 then (R.blocks.get (Fin.cast R.blocks_length.symm p.1)).get p.2
        else -(R.blocks.get (Fin.cast R.blocks_length.symm p.1)).get p.2 by
    rw [← Equiv.sum_comp R.occurrenceEquivSigma]
    rfl]
  rw [Fintype.sum_sigma]
  have hinner : ∀ i : Fin m,
      (∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
        if color i then (R.blocks.get (Fin.cast R.blocks_length.symm i)).get j
        else -(R.blocks.get (Fin.cast R.blocks_length.symm i)).get j) =
      if color i then δ * (2 : ℝ) ^ (i : ℕ) else -(δ * (2 : ℝ) ^ (i : ℕ)) := by
    intro i
    split
    · rw [← List.sum_ofFn, List.ofFn_get, R.block_sum i]
    · calc
        (∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
            -(R.blocks.get (Fin.cast R.blocks_length.symm i)).get j) =
            -(∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
              (R.blocks.get (Fin.cast R.blocks_length.symm i)).get j) := by
              simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
                (Finset.sum_neg_distrib
                  (s := Finset.univ)
                  (f := fun j : Fin (R.blocks.get
                    (Fin.cast R.blocks_length.symm i)).length =>
                    (R.blocks.get (Fin.cast R.blocks_length.symm i)).get j))
        _ = -(δ * (2 : ℝ) ^ (i : ℕ)) := by
          congr 1
          rw [← List.sum_ofFn, List.ofFn_get, R.block_sum i]
  simp only
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  unfold signedPowSum
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> ring

/-- The endpoint base weights inherit the color sign attached to each block. -/
def signedBaseWeight (_R : GeometricRefinement δ m) (color : Fin m → Bool) (i : Fin m) : ℝ :=
  if color i then δ * (2 : ℝ) ^ (i : ℕ) else -(δ * (2 : ℝ) ^ (i : ℕ))

lemma signed_block_sum_finset (R : GeometricRefinement δ m)
    (s : Finset (Fin m)) (color : Fin m → Bool) :
    (∑ i ∈ s, if color i then δ * (2 : ℝ) ^ (i : ℕ)
      else -(δ * (2 : ℝ) ^ (i : ℕ))) =
    ∑ i ∈ s, R.signedBaseWeight color i := by
  rfl

/-- A signed sum over a nonempty set of distinct `Fin` exponents is nonzero. -/
def signedPowFin {m : ℕ} (s : Finset (Fin m)) (color : Fin m → Bool) : ℤ :=
  ∑ i ∈ s, if color i then (2 : ℤ) ^ (i : ℕ) else -((2 : ℤ) ^ (i : ℕ))

lemma signedPowFin_ne_zero {m : ℕ} {s : Finset (Fin m)} (hs : s.Nonempty)
    (color : Fin m → Bool) : signedPowFin s color ≠ 0 := by
  let k := s.min' hs
  have hk : k ∈ s := s.min'_mem hs
  have hdiv : (2 : ℤ) ^ ((k : ℕ) + 1) ∣
      ∑ i ∈ s.erase k,
        if color i then (2 : ℤ) ^ (i : ℕ) else -((2 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i hi
    have hki : (k : ℕ) + 1 ≤ (i : ℕ) := by
      have := Finset.min'_lt_of_mem_erase_min' s hs hi
      omega
    have hp : (2 : ℤ) ^ ((k : ℕ) + 1) ∣ (2 : ℤ) ^ (i : ℕ) := pow_dvd_pow 2 hki
    split
    · exact hp
    · exact dvd_neg.mpr hp
  intro hzero
  have hsplit :
      (∑ i ∈ s.erase k,
        if color i then (2 : ℤ) ^ (i : ℕ) else -((2 : ℤ) ^ (i : ℕ))) +
        (if color k then (2 : ℤ) ^ (k : ℕ) else -((2 : ℤ) ^ (k : ℕ))) = 0 := by
    rw [Finset.sum_erase_add s _ hk]
    exact hzero
  have htermDiv : (2 : ℤ) ^ ((k : ℕ) + 1) ∣
      (if color k then (2 : ℤ) ^ (k : ℕ) else -((2 : ℤ) ^ (k : ℕ))) := by
    have hEq : (if color k then (2 : ℤ) ^ (k : ℕ) else -((2 : ℤ) ^ (k : ℕ))) =
        -(∑ i ∈ s.erase k,
          if color i then (2 : ℤ) ^ (i : ℕ) else -((2 : ℤ) ^ (i : ℕ))) := by
      linarith
    rw [hEq]
    exact dvd_neg.mpr hdiv
  have hpowDiv : (2 : ℤ) ^ ((k : ℕ) + 1) ∣ (2 : ℤ) ^ (k : ℕ) := by
    split at htermDiv
    · exact htermDiv
    · exact dvd_neg.mp htermDiv
  rw [pow_succ] at hpowDiv
  have hcancel : (2 : ℤ) ∣ 1 := by
    exact (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ (k : ℕ) ≠ 0)).mp
      (by simpa using hpowDiv)
  norm_num at hcancel

lemma delta_le_abs_signedPowFin {m : ℕ} {s : Finset (Fin m)} (hs : s.Nonempty)
    (color : Fin m → Bool) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ≤ |δ * (signedPowFin s color : ℝ)| := by
  exact delta_le_abs_mul_intCast hδ (signedPowFin_ne_zero hs color)

/-- Pairwise opposite (or absent) coefficients control a weighted sum by the alternating sum. -/
lemma abs_weighted_sum_le_altSum : ∀ (xs : List ℝ)
    (coeff : Fin xs.length → ℝ),
    xs.Pairwise (· ≥ ·) →
    (∀ x ∈ xs, 0 ≤ x) →
    (∀ i, coeff i = -1 ∨ coeff i = 0 ∨ coeff i = 1) →
    (∀ q : Fin (xs.length / 2),
      (coeff ⟨2 * (q : ℕ), by omega⟩ = 0 ∧
        coeff ⟨2 * (q : ℕ) + 1, by omega⟩ = 0) ∨
      (coeff ⟨2 * (q : ℕ), by omega⟩ = 1 ∧
        coeff ⟨2 * (q : ℕ) + 1, by omega⟩ = -1) ∨
      (coeff ⟨2 * (q : ℕ), by omega⟩ = -1 ∧
        coeff ⟨2 * (q : ℕ) + 1, by omega⟩ = 1)) →
    |∑ i : Fin xs.length, coeff i * xs.get i| ≤ altSum xs := by
  intro xs
  induction xs using List.twoStepInduction with
  | nil => intro coeff _ _ _ _; simp [altSum]
  | singleton x =>
      intro coeff _ hx hc _
      have hc0 := hc ⟨0, by simp⟩
      have hsum : (∑ i : Fin [x].length, coeff i * [x].get i) = coeff ⟨0, by simp⟩ * x := by
        rw [show (Finset.univ : Finset (Fin [x].length)) = {⟨0, by simp⟩} by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro i _
          exact Fin.eq_of_val_eq (by simp at i ⊢)]
        simp
      rw [hsum]
      rcases hc0 with h | h | h
      · rw [h]
        simp only [neg_mul, one_mul]
        rw [abs_neg, abs_of_nonneg (hx x (by simp))]
        simp [altSum]
      · rw [h]
        simp only [zero_mul, abs_zero]
        simp [altSum, hx x (by simp)]
      · rw [h]
        simp only [one_mul]
        rw [abs_of_nonneg (hx x (by simp))]
        simp [altSum]
  | cons_cons x y xs ih =>
      intro coeff hsort hnonneg hc hpairs
      let tailCoeff : Fin xs.length → ℝ := fun i => coeff ⟨(i : ℕ) + 2, by simp⟩
      have htailSort : xs.Pairwise (· ≥ ·) := by simpa using hsort.tail.tail
      have htailNonneg : ∀ z ∈ xs, 0 ≤ z := by
        intro z hz
        exact hnonneg z (by simp [hz])
      have htailCoeff : ∀ i, tailCoeff i = -1 ∨ tailCoeff i = 0 ∨ tailCoeff i = 1 := by
        intro i
        exact hc ⟨(i : ℕ) + 2, by simp⟩
      have htailPairs : ∀ q : Fin (xs.length / 2),
          (tailCoeff ⟨2 * (q : ℕ), by omega⟩ = 0 ∧
            tailCoeff ⟨2 * (q : ℕ) + 1, by omega⟩ = 0) ∨
          (tailCoeff ⟨2 * (q : ℕ), by omega⟩ = 1 ∧
            tailCoeff ⟨2 * (q : ℕ) + 1, by omega⟩ = -1) ∨
          (tailCoeff ⟨2 * (q : ℕ), by omega⟩ = -1 ∧
            tailCoeff ⟨2 * (q : ℕ) + 1, by omega⟩ = 1) := by
        intro q
        simpa [tailCoeff, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hpairs ⟨(q : ℕ) + 1, by simp; omega⟩
      have htail := ih tailCoeff htailSort htailNonneg htailCoeff htailPairs
      have hxy : y ≤ x := hsort.rel_get_of_lt (a := ⟨0, by simp⟩) (b := ⟨1, by simp⟩)
        (by simp)
      have hpair0 := hpairs ⟨0, by simp⟩
      have hc0 : coeff ⟨0, by simp⟩ = 0 ∧ coeff ⟨1, by simp⟩ = 0 ∨
          coeff ⟨0, by simp⟩ = 1 ∧ coeff ⟨1, by simp⟩ = -1 ∨
          coeff ⟨0, by simp⟩ = -1 ∧ coeff ⟨1, by simp⟩ = 1 := by
        simpa only [Fin.zero_eta, Nat.cast_zero, mul_zero, zero_add] using hpair0
      have hpair : |coeff ⟨0, by simp⟩ * x + coeff ⟨1, by simp⟩ * y| ≤ x - y := by
        rcases hc0 with h | h | h
        · rw [h.1, h.2]
          simp
          linarith
        · rw [h.1, h.2]
          simp only [one_mul, neg_mul]
          change |x - y| ≤ x - y
          rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
        · rw [h.1, h.2]
          rw [show (-1 : ℝ) * x + 1 * y = -(x - y) by ring, abs_neg,
            abs_of_nonneg (sub_nonneg.mpr hxy)]
      have hsum1 : (∑ i : Fin (x :: y :: xs).length, coeff i * (x :: y :: xs).get i) =
          coeff ⟨0, by simp⟩ * x +
            ∑ i : Fin (y :: xs).length,
              coeff ⟨(i : ℕ) + 1, by simp; omega⟩ * (y :: xs).get i := by
        simpa only [List.length_cons, List.get_cons_zero, List.get_cons_succ] using
          (Fin.sum_univ_succ (f := fun i : Fin (x :: y :: xs).length =>
            coeff i * (x :: y :: xs).get i))
      have hsum2 : (∑ i : Fin (y :: xs).length,
              coeff ⟨(i : ℕ) + 1, by simp; omega⟩ * (y :: xs).get i) =
          coeff ⟨1, by simp⟩ * y +
            ∑ i : Fin xs.length, tailCoeff i * xs.get i := by
        simpa only [List.length_cons, List.get_cons_zero, List.get_cons_succ, tailCoeff,
          Nat.add_assoc] using
          (Fin.sum_univ_succ (f := fun i : Fin (y :: xs).length =>
            coeff ⟨(i : ℕ) + 1, by simp; omega⟩ * (y :: xs).get i))
      have hsum : (∑ i : Fin (x :: y :: xs).length, coeff i * (x :: y :: xs).get i) =
          (coeff ⟨0, by simp⟩ * x + coeff ⟨1, by simp⟩ * y) +
            ∑ i : Fin xs.length, tailCoeff i * xs.get i := by
        rw [hsum1, hsum2]
        ring
      rw [hsum]
      calc
        _ ≤ |coeff ⟨0, by simp⟩ * x + coeff ⟨1, by simp⟩ * y| +
            |∑ i : Fin xs.length, tailCoeff i * xs.get i| := abs_add_le _ _
        _ ≤ (x - y) + altSum xs := add_le_add hpair htail
        _ = altSum (x :: y :: xs) := by simp [altSum]; ring

/-- Reindexing a signed component of block labels over sorted occurrences recovers its signed
geometric base-weight sum. -/
lemma signed_block_sum_component (R : GeometricRefinement δ m) (s : Finset (Fin m))
    (color : Fin m → Bool) :
    (∑ p : R.SortedIndex,
      if R.label p ∈ s then
        if color (R.label p) then (sortedFragments R.blocks).get p
        else -(sortedFragments R.blocks).get p
      else 0) = δ * (signedPowFin s color : ℝ) := by
  classical
  let e : R.SortedIndex ≃ R.Occurrence := R.positionEquivOccurrence
  have hleft : (∑ p : R.SortedIndex,
      if R.label p ∈ s then
        if color (R.label p) then (sortedFragments R.blocks).get p
        else -(sortedFragments R.blocks).get p
      else 0) =
      ∑ p : R.Occurrence,
        if p.block ∈ s then if color p.block then p.value else -p.value else 0 := by
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro p _
    have he : e p = R.positionEquivOccurrence p := rfl
    rw [he, ← R.get_sorted_eq_occurrence p]
    rfl
  rw [hleft]
  rw [show (∑ p : R.Occurrence,
      if p.block ∈ s then if color p.block then p.value else -p.value else 0) =
      ∑ p : Σ i : Fin m, Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
        if p.1 ∈ s then
          if color p.1 then (R.blocks.get (Fin.cast R.blocks_length.symm p.1)).get p.2
          else -(R.blocks.get (Fin.cast R.blocks_length.symm p.1)).get p.2
        else 0 by
    rw [← Equiv.sum_comp R.occurrenceEquivSigma]
    rfl]
  rw [Fintype.sum_sigma]
  have hinner : ∀ i : Fin m,
      (∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
        if i ∈ s then
          if color i then (R.blocks.get (Fin.cast R.blocks_length.symm i)).get j
          else -(R.blocks.get (Fin.cast R.blocks_length.symm i)).get j
        else 0) =
      if i ∈ s then
        if color i then δ * (2 : ℝ) ^ (i : ℕ) else -(δ * (2 : ℝ) ^ (i : ℕ))
      else 0 := by
    intro i
    by_cases hi : i ∈ s
    · simp only [hi, if_true]
      by_cases hc : color i
      · simp only [hc, if_true]
        rw [← List.sum_ofFn, List.ofFn_get, R.block_sum i]
      · simp only [hc]
        change (∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
          -(R.blocks.get (Fin.cast R.blocks_length.symm i)).get j) =
          -(δ * (2 : ℝ) ^ (i : ℕ))
        calc
          (∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
              -(R.blocks.get (Fin.cast R.blocks_length.symm i)).get j) =
              -(∑ j : Fin (R.blocks.get (Fin.cast R.blocks_length.symm i)).length,
                (R.blocks.get (Fin.cast R.blocks_length.symm i)).get j) :=
                (Finset.sum_neg_distrib (s := Finset.univ)
                  (f := fun j : Fin (R.blocks.get
                    (Fin.cast R.blocks_length.symm i)).length =>
                    (R.blocks.get (Fin.cast R.blocks_length.symm i)).get j))
          _ = -(δ * (2 : ℝ) ^ (i : ℕ)) := by
            rw [← List.sum_ofFn, List.ofFn_get, R.block_sum i]
    · simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  unfold signedPowFin
  push_cast
  calc
    (∑ i : Fin m,
        if i ∈ s then
          if color i then δ * (2 : ℝ) ^ (i : ℕ) else -(δ * (2 : ℝ) ^ (i : ℕ))
        else 0) =
        ∑ i ∈ s,
          (if color i then δ * (2 : ℝ) ^ (i : ℕ) else -(δ * (2 : ℝ) ^ (i : ℕ))) := by
        rw [Finset.sum_ite_mem]
        simp
    _ = δ * ∑ i ∈ s,
          (if color i then (2 : ℝ) ^ (i : ℕ) else -((2 : ℝ) ^ (i : ℕ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          split <;> ring

/-- The signed fragment sum supported on one pair-graph component. -/
noncomputable def componentSignedSum (R : GeometricRefinement δ m)
    (C : R.pairGraph.ConnectedComponent) (color : Fin m → Bool) : ℝ := by
  classical
  exact ∑ p : R.SortedIndex,
    if R.pairGraph.connectedComponentMk (R.label p) = C then
      if color (R.label p) then (sortedFragments R.blocks).get p
      else -(sortedFragments R.blocks).get p
    else 0

/-- The final graph-to-analysis bridge. All adjacent pairs, including loops and repeated
pairs, are counted in `P`.  The strict multi-edge/vertex inequality, together with connectivity,
forces the underlying simple component to have exactly `V-1` edges; consequently `P` has no loops
or repetitions and is itself the edge set of a tree.  Its bipartition supplies the signs. -/
lemma balancing_coloring_from_sparse_component (R : GeometricRefinement δ m) (_hm : 0 < m)
    (C : R.pairGraph.ConnectedComponent)
    (hC : {q : Fin ((sortedFragments R.blocks).length / 2) |
      R.pairGraph.connectedComponentMk (R.label ⟨2 * (q : ℕ), by omega⟩) = C}.ncard <
      C.supp.ncard) :
    ∃ color : Fin m → Bool,
      |componentSignedSum R C color| ≤ altSum (sortedFragments R.blocks) := by
  classical
  let xs := sortedFragments R.blocks
  let n := xs.length
  let Q := Fin ((sortedFragments R.blocks).length / 2)
  let first : Q → Fin m := fun q => R.label ⟨2 * (q : ℕ), by omega⟩
  let second : Q → Fin m := fun q => R.label ⟨2 * (q : ℕ) + 1, by omega⟩
  let pairComponent : Q → R.pairGraph.ConnectedComponent := fun q =>
    R.pairGraph.connectedComponentMk (first q)
  let P : Finset Q := Finset.univ.filter fun q => pairComponent q = C
  have hP : P.card < Fintype.card C.supp := by
    rw [show Fintype.card C.supp = C.supp.ncard by
      exact (Nat.card_coe_set_eq C.supp).trans Nat.card_eq_fintype_card |>.symm]
    simpa [P, pairComponent, first, n, xs, Set.ncard_eq_toFinset_card'] using hC
  have hsecond_comp (q : Q) :
      R.pairGraph.connectedComponentMk (second q) = pairComponent q := by
    by_cases hloop : first q = second q
    · simp [hloop, pairComponent]
    · have hadj : R.pairGraph.Adj (first q) (second q) := by
        refine ⟨hloop, ⟨q, Or.inl ⟨rfl, rfl⟩⟩⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hfirst_mem (q : Q) (hq : q ∈ P) : first q ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp hq).2
  have hsecond_mem (q : Q) (hq : q ∈ P) : second q ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hsecond_comp]
    exact (Finset.mem_filter.mp hq).2
  let CrossP := {q : P // first q.1 ≠ second q.1}
  let H := C.toSimpleGraph
  have hHconn : H.Connected := C.connected_toSimpleGraph
  let crossEdge : CrossP → H.edgeSet := fun q =>
    ⟨s(⟨first q.1.1, hfirst_mem q.1.1 q.1.2⟩,
        ⟨second q.1.1, hsecond_mem q.1.1 q.1.2⟩), by
      change H.Adj ⟨first q.1.1, hfirst_mem q.1.1 q.1.2⟩
        ⟨second q.1.1, hsecond_mem q.1.1 q.1.2⟩
      apply (C.toSimpleGraph_adj _ _).2
      exact ⟨q.2, ⟨q.1.1, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
  have hedge_surj : Function.Surjective crossEdge := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadjH : H.Adj u v := he
      have hadjG : R.pairGraph.Adj u.1 v.1 := hadjH
      rcases hadjG.2 with ⟨q, hq | hq⟩
      · have hcomp : pairComponent q = C := by
          change R.pairGraph.connectedComponentMk (first q) = C
          rw [show first q = u.1 from hq.1]
          exact u.2
        let qp : P := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp⟩⟩
        have hne : first q ≠ second q := by
          intro heq
          apply hadjG.1
          rw [← hq.1, ← hq.2]
          exact heq
        let qc : CrossP := ⟨qp, hne⟩
        refine ⟨qc, Subtype.ext ?_⟩
        change s(⟨first q, _⟩, ⟨second q, _⟩) = s(u, v)
        rw [Sym2.eq_iff]
        exact Or.inl ⟨Subtype.ext hq.1, Subtype.ext hq.2⟩
      · have hcomp : pairComponent q = C := by
          change R.pairGraph.connectedComponentMk (first q) = C
          rw [show first q = v.1 from hq.1]
          exact v.2
        let qp : P := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp⟩⟩
        have hne : first q ≠ second q := by
          intro heq
          apply hadjG.1
          rw [← hq.2, ← hq.1]
          exact heq.symm
        let qc : CrossP := ⟨qp, hne⟩
        refine ⟨qc, Subtype.ext ?_⟩
        change s(⟨first q, _⟩, ⟨second q, _⟩) = s(u, v)
        rw [Sym2.eq_iff]
        exact Or.inr ⟨Subtype.ext hq.1, Subtype.ext hq.2⟩
  have hedge_le_cross : Fintype.card H.edgeSet ≤ Fintype.card CrossP :=
    Fintype.card_le_of_surjective crossEdge hedge_surj
  have hcross_le : Fintype.card CrossP ≤ P.card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hP' : P.card < Fintype.card C := by
    have hcardC : Fintype.card C = Fintype.card C.supp := by
      apply Fintype.card_congr
      exact Equiv.setCongr rfl
    rw [hcardC]
    exact hP
  have hedge_le : Fintype.card H.edgeSet ≤ P.card := hedge_le_cross.trans hcross_le
  have htree : H.IsTree := by
    apply connected_component_isTree_of_edge_lt_vertex H hHconn
    exact lt_of_le_of_lt hedge_le hP'
  have hedge_card : Fintype.card H.edgeSet = P.card := by
    have hlower := hHconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hlower
    omega
  have hcross_card : Fintype.card CrossP = P.card := by omega
  have hcross_surj : Function.Surjective (fun q : CrossP => q.1) := by
    have hbij : Function.Bijective (fun q : CrossP => q.1) := by
      apply (Fintype.bijective_iff_injective_and_card _).2
      refine ⟨Subtype.val_injective, ?_⟩
      calc
        Fintype.card CrossP = P.card := hcross_card
        _ = Fintype.card P := by rw [Fintype.card_coe]
    exact hbij.2
  have hnonloop (q : Q) (hq : q ∈ P) : first q ≠ second q := by
    obtain ⟨qc, hqc⟩ := hcross_surj (⟨q, hq⟩ : P)
    have hval : qc.1.1 = q := congrArg Subtype.val hqc
    simpa only [hval] using qc.2
  let pairEdge : P → H.edgeSet := fun q =>
    ⟨s(⟨first q.1, hfirst_mem q.1 q.2⟩, ⟨second q.1, hsecond_mem q.1 q.2⟩), by
      change H.Adj ⟨first q.1, hfirst_mem q.1 q.2⟩
        ⟨second q.1, hsecond_mem q.1 q.2⟩
      apply (C.toSimpleGraph_adj _ _).2
      exact ⟨hnonloop q.1 q.2, ⟨q.1, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
  have hedge_surj' : Function.Surjective pairEdge := by
    intro e
    obtain ⟨qc, hqc⟩ := hedge_surj e
    refine ⟨qc.1, ?_⟩
    exact hqc
  have hedge_bij : Function.Bijective pairEdge := by
    apply (Fintype.bijective_iff_surjective_and_card _).2
    exact ⟨hedge_surj', by simp [hedge_card]⟩
  let coloring : H.Coloring (Fin 2) := htree.coloringTwo
  let color : Fin m → Bool := fun i => decide (∃ hi : R.pairGraph.connectedComponentMk i = C,
    coloring ⟨i, hi⟩ = 0)
  have hpair_opposite (q : Q) (hq : q ∈ P) : color (first q) ≠ color (second q) := by
    have hadjH : H.Adj ⟨first q, hfirst_mem q hq⟩ ⟨second q, hsecond_mem q hq⟩ := by
      apply (C.toSimpleGraph_adj _ _).2
      exact ⟨hnonloop q hq, ⟨q, Or.inl ⟨rfl, rfl⟩⟩⟩
    have hcneq := coloring.map_rel hadjH
    have hcolor_eq (i : Fin m) (hi : R.pairGraph.connectedComponentMk i = C) :
        color i = decide (coloring ⟨i, hi⟩ = 0) := by
      simp only [color]
      congr 1
      apply propext
      constructor
      · rintro ⟨hj, hc⟩
        have hsub : (⟨i, hj⟩ : C) = ⟨i, hi⟩ := Subtype.ext rfl
        simpa [hsub] using hc
      · intro hc
        exact ⟨hi, hc⟩
    rw [hcolor_eq (first q) (hfirst_mem q hq),
      hcolor_eq (second q) (hsecond_mem q hq)]
    have hfin2 (a b : Fin 2) (hab : a ≠ b) : decide (a = 0) ≠ decide (b = 0) := by
      fin_cases a <;> fin_cases b <;> simp_all
    exact hfin2 _ _ hcneq
  have hpair_membership (q : Q) : q ∈ P ↔ first q ∈ C.supp := by
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, pairComponent,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
  let coeff : R.SortedIndex → ℝ := fun p =>
    if R.pairGraph.connectedComponentMk (R.label p) = C then
      if color (R.label p) then 1 else -1 else 0
  have hcoeff : ∀ p, coeff p = -1 ∨ coeff p = 0 ∨ coeff p = 1 := by
    intro p
    by_cases hp : R.pairGraph.connectedComponentMk (R.label p) = C
    · by_cases hc : color (R.label p) <;> simp [coeff, hp, hc]
    · simp [coeff, hp]
  have hcoeff_pairs : ∀ q : Fin ((sortedFragments R.blocks).length / 2),
      (coeff ⟨2 * (q : ℕ), by omega⟩ = 0 ∧
        coeff ⟨2 * (q : ℕ) + 1, by omega⟩ = 0) ∨
      (coeff ⟨2 * (q : ℕ), by omega⟩ = 1 ∧
        coeff ⟨2 * (q : ℕ) + 1, by omega⟩ = -1) ∨
      (coeff ⟨2 * (q : ℕ), by omega⟩ = -1 ∧
        coeff ⟨2 * (q : ℕ) + 1, by omega⟩ = 1) := by
    intro q
    by_cases hq : q ∈ P
    · have hf := hfirst_mem q hq
      have hs := hsecond_mem q hq
      have hop := hpair_opposite q hq
      cases h1 : color (first q) <;> cases h2 : color (second q)
      · exact False.elim (hop (by simp [h1, h2]))
      · have hfcomp : R.pairGraph.connectedComponentMk (first q) = C := hf
        have hscomp : R.pairGraph.connectedComponentMk (second q) = C := hs
        exact Or.inr (Or.inr ⟨by simp [coeff, first, hfcomp, h1],
          by simp [coeff, second, hscomp, h2]⟩)
      · have hfcomp : R.pairGraph.connectedComponentMk (first q) = C := hf
        have hscomp : R.pairGraph.connectedComponentMk (second q) = C := hs
        exact Or.inr (Or.inl ⟨by simp [coeff, first, hfcomp, h1],
          by simp [coeff, second, hscomp, h2]⟩)
      · exact False.elim (hop (by simp [h1, h2]))
    · have hf : first q ∉ C.supp := by
        intro hf
        exact hq ((hpair_membership q).2 hf)
      have hs : second q ∉ C.supp := by
        intro hs
        have hcomp : pairComponent q = C := by
          rw [← hsecond_comp q]
          exact hs
        exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp⟩)
      have hfcomp : R.pairGraph.connectedComponentMk (first q) ≠ C := hf
      have hscomp : R.pairGraph.connectedComponentMk (second q) ≠ C := hs
      exact Or.inl ⟨by simp [coeff, first, hfcomp], by
        simp [coeff, second, hscomp]⟩
  have hweighted : |∑ p : R.SortedIndex, coeff p * (sortedFragments R.blocks).get p| ≤
      altSum (sortedFragments R.blocks) := by
    apply abs_weighted_sum_le_altSum (sortedFragments R.blocks) coeff
    · exact List.pairwise_mergeSort' (· ≥ ·) R.blocks.flatten
    · intro x hx
      apply R.nonneg x
      exact (R.blocks.flatten.mergeSort_perm (· ≥ ·)).mem_iff.mp hx
    · exact hcoeff
    · exact hcoeff_pairs
  refine ⟨color, ?_⟩
  have hsum : (∑ p : R.SortedIndex,
      if R.pairGraph.connectedComponentMk (R.label p) = C then
        if color (R.label p) then (sortedFragments R.blocks).get p
        else -(sortedFragments R.blocks).get p
      else 0) =
      ∑ p : R.SortedIndex, coeff p * (sortedFragments R.blocks).get p := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : R.pairGraph.connectedComponentMk (R.label p) = C
    · simp [coeff, hp]
    · simp [coeff, hp]
  unfold componentSignedSum
  calc
    |∑ p : R.SortedIndex,
        if R.pairGraph.connectedComponentMk (R.label p) = C then
          if color (R.label p) then (sortedFragments R.blocks).get p
          else -(sortedFragments R.blocks).get p
        else 0| =
        |∑ p : R.SortedIndex, coeff p * (sortedFragments R.blocks).get p| := by
          rw [hsum]
    _ ≤ altSum (sortedFragments R.blocks) := hweighted


/-- Generic geometric-fragment lower bound. -/
theorem altSum_sortedFragments_ge_delta (hm : 0 < m) (hδ : 0 ≤ δ) :
    δ ≤ altSum (sortedFragments R.blocks) := by
  by_cases hzero : δ = 0
  · have hz : δ ≤ 0 := le_of_eq hzero
    apply hz.trans
    apply altSum_sorted_nonneg
    · intro x hx
      apply R.nonneg x
      exact (R.blocks.flatten.mergeSort_perm (· ≥ ·)).mem_iff.mp hx
    · exact List.pairwise_mergeSort' (· ≥ ·) R.blocks.flatten
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
    obtain ⟨C, hC⟩ := R.exists_sparse_component hm
    obtain ⟨color, hbalance⟩ := R.balancing_coloring_from_sparse_component hm C hC
    have hbalance' :
        δ * (signedPowFin C.supp.toFinset color : ℝ) = componentSignedSum R C color := by
      rw [← R.signed_block_sum_component C.supp.toFinset color]
      unfold componentSignedSum
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : R.pairGraph.connectedComponentMk (R.label p) = C
      · simp [hp]
      · have hpmem : R.label p ∉ C.supp := hp
        simp [hp, hpmem]
    rw [← hbalance'] at hbalance
    have hnonempty : C.supp.toFinset.Nonempty := by
      simpa only [Set.toFinset_nonempty] using C.nonempty_supp
    exact (delta_le_abs_signedPowFin hnonempty color hδ).trans hbalance

end GeometricRefinement


/-!
The next lemmas isolate the generic combinatorics used by the sharp upper
response.  They deliberately do not depend on the game definitions.
-/

/-- Adjacent points in a finite subset of `[0,1]` have a gap no larger than
`1 / (card - 1)`. -/
lemma sorted_gap_exists (S : Finset ℝ) (hcard : 2 ≤ S.card)
    (hzero : 0 ∈ S) (hone : 1 ∈ S) (hI : ∀ x ∈ S, x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x y : ℝ, x ∈ S ∧ y ∈ S ∧ x < y ∧
      y - x ≤ 1 / (S.card - 1) := by
  let s : List ℝ := S.sort (· ≤ ·)
  have hlen : s.length = S.card := by simp [s]
  have hpair : s.Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hne : s ≠ [] := by
    intro hs
    have : s.length = 0 := by simp [hs]
    omega
  have hhead : s.head hne = 0 := by
    have h0mem : 0 ∈ s := (Finset.mem_sort _).mpr hzero
    have hhmem : s.head hne ∈ S := (Finset.mem_sort _).mp (List.head_mem hne)
    have hh0 : 0 ≤ s.head hne := (hI _ hhmem).1
    rcases List.mem_iff_getElem.mp h0mem with ⟨i, hi, heq⟩
    have h0 : 0 < s.length := List.length_pos_iff.mpr hne
    have hle0 : s[0] ≤ s[i] := by
      by_cases hiz : i = 0
      · subst i
        exact le_rfl
      · exact (List.pairwise_iff_getElem.mp hpair) 0 i h0 hi
          (Nat.pos_of_ne_zero hiz)
    rw [← List.head_eq_getElem hne, heq] at hle0
    linarith
  have hlast : s.getLast hne = 1 := by
    have h1mem : 1 ∈ s := (Finset.mem_sort _).mpr hone
    have hlmem : s.getLast hne ∈ S := (Finset.mem_sort _).mp (List.getLast_mem hne)
    have hl1 : s.getLast hne ≤ 1 := (hI _ hlmem).2
    rcases List.mem_iff_getElem.mp h1mem with ⟨i, hi, heq⟩
    have hlastidx : s.length - 1 < s.length := by omega
    have hltle : i ≤ s.length - 1 := by omega
    have hle : s[i] ≤ s[s.length - 1] := by
      rcases hltle.eq_or_lt with hidx | hlt
      · exact hidx ▸ le_rfl
      · exact (List.pairwise_iff_getElem.mp hpair) i (s.length - 1) hi hlastidx hlt
    have hget : s.getLast hne = s[s.length - 1] := List.getLast_eq_getElem hne
    have hle' : (1 : ℝ) ≤ s.getLast hne := by
      rw [hget]
      rw [heq] at hle
      exact hle
    linarith
  let gaps : List ℝ := List.zipWith (fun x y : ℝ => y - x) s s.tail
  have hglen : gaps.length = S.card - 1 := by
    rw [List.length_zipWith, List.length_tail, hlen]
    omega
  have hgsum : gaps.sum = 1 := by
    have htel : gaps.sum = s.getLastD 0 - s.getD 0 0 :=
      zipWith_sub_sum s s.tail rfl (by simp)
    rw [htel]
    have h0 : 0 < s.length := by omega
    rw [List.getD_eq_getElem s 0 h0]
    rw [← List.head_eq_getElem hne, hhead]
    have hgetlastD : s.getLastD 0 = s.getLast hne := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
      rfl
    rw [hgetlastD, hlast]
    norm_num
  have hgapne : gaps ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hglen]
    omega
  obtain ⟨d, hdmem, hdle⟩ := List.exists_le_of_sum_le hgapne (fun x => x)
      (fun _ => (1 : ℝ) / gaps.length) (by
        have hlen0 : (gaps.length : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (List.length_pos_iff.mpr hgapne))
        have hconst :
            (List.map (fun _ : ℝ => (1 : ℝ) / gaps.length) gaps).sum = 1 := by
          rw [show List.map (fun _ : ℝ => (1 : ℝ) / gaps.length) gaps =
              List.replicate gaps.length ((1 : ℝ) / gaps.length) by exact List.map_const]
          rw [List.sum_replicate]
          simp only [nsmul_eq_mul]
          field_simp
        have hidmap : (List.map (fun x : ℝ => x) gaps).sum = gaps.sum := by
          congr 1
          induction gaps with
          | nil => rfl
          | cons x xs ih => simp [ih]
        rw [hidmap, hgsum, hconst])
  rcases List.mem_iff_getElem.mp hdmem with ⟨i, hi, hid⟩
  have his : i < s.length := by
    rw [hglen] at hi
    rw [hlen]
    omega
  have hitail : i < s.tail.length := by
    rw [List.length_tail, hlen]
    rw [hglen] at hi
    omega
  refine ⟨s[i], s[i + 1], ?_, ?_, ?_, ?_⟩
  · exact (Finset.mem_sort _).mp (List.getElem_mem his)
  · have hi1 : i + 1 < s.length := by omega
    exact (Finset.mem_sort _).mp (List.getElem_mem hi1)
  · have hle : s[i] ≤ s[i + 1] :=
      (List.pairwise_iff_getElem.mp hpair) i (i + 1) his (by omega) (by omega)
    have hne' : s[i] ≠ s[i + 1] := by
      intro heq
      have hnd := Finset.sort_nodup S (· ≤ ·)
      have := (List.getElem_inj hnd).mp heq
      omega
    exact lt_of_le_of_ne hle hne'
  · have hzip : gaps[i] = s[i + 1] - s[i] := by
      rw [List.getElem_zipWith]
      rw [List.getElem_tail hitail]
    rw [← hzip, hid]
    rw [hglen] at hdle
    have hcast : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 :=
      Nat.cast_pred (by omega)
    rw [hcast] at hdle
    exact hdle

lemma fin_sum_all_eq_list_sum (l : List ℝ) :
    (∑ i : Fin l.length, l[i]) = l.sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum List.ofFn_getElem

lemma finset_sum_sdiff_cancel {m : ℕ} (w : Fin m → ℝ)
    (R T : Finset (Fin m)) :
    (∑ i ∈ T \ R, w i) - ∑ i ∈ R \ T, w i =
      (∑ i ∈ T, w i) - ∑ i ∈ R, w i := by
  have hTi : (∑ i ∈ T, w i) =
      (∑ i ∈ T \ R, w i) + ∑ i ∈ T ∩ R, w i := by
    rw [← Finset.sum_union (s₁ := T \ R) (s₂ := T ∩ R)]
    · rw [Finset.sdiff_union_inter]
    · rw [Finset.disjoint_left]
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hi').2
  have hRi : (∑ i ∈ R, w i) =
      (∑ i ∈ R \ T, w i) + ∑ i ∈ R ∩ T, w i := by
    rw [← Finset.sum_union (s₁ := R \ T) (s₂ := R ∩ T)]
    · rw [Finset.sdiff_union_inter]
    · rw [Finset.disjoint_left]
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hi').2
  rw [Finset.inter_comm T R] at hTi
  linarith

/-- Among subset sums of positive weights summing to one, two subsets have
nearby sums.  Cancelling their intersection gives nonempty disjoint residual
families with the same bound.  Coincident subset sums are handled separately,
so no injectivity assumption is hidden. -/
lemma subset_sum_close {l : List ℝ}
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    ∃ P Q : Finset (Fin l.length), P ∩ Q = ∅ ∧ P ∪ Q ≠ ∅ ∧
      |(∑ i ∈ P, l[i]) - ∑ i ∈ Q, l[i]| ≤
        1 / ((2 : ℝ) ^ l.length - 1) := by
  let U : Finset (Fin l.length) := Finset.univ
  let f : Finset (Fin l.length) → ℝ := fun P => ∑ i ∈ P, l[i]
  let sums : Finset ℝ := U.powerset.image f
  have hzero : 0 ∈ sums := by
    refine Finset.mem_image.mpr ⟨∅, ?_, by simp [f]⟩
    simp [U]
  have hone : 1 ∈ sums := by
    refine Finset.mem_image.mpr ⟨U, ?_, ?_⟩
    · simp [U]
    · change (∑ i : Fin l.length, l[i]) = 1
      exact (fin_sum_all_eq_list_sum l).trans hsum
  have hI : ∀ x ∈ sums, x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨P, hP, rfl⟩
    have hPU : P ⊆ U := Finset.mem_powerset.mp hP
    constructor
    · exact Finset.sum_nonneg fun i _ => (hpos _ (List.getElem_mem i.2)).le
    · calc
        (∑ i ∈ P, l[i]) ≤ ∑ i ∈ U, l[i] :=
          Finset.sum_le_sum_of_subset_of_nonneg hPU
            (fun i _ _ => (hpos _ (List.getElem_mem i.2)).le)
        _ = 1 := by
          change (∑ i : Fin l.length, l[i]) = 1
          exact (fin_sum_all_eq_list_sum l).trans hsum
  have hcard : 2 ≤ sums.card := by
    have hne : (0 : ℝ) ≠ 1 := by norm_num
    exact (Finset.one_lt_card).mpr ⟨0, hzero, 1, hone, hne⟩
  by_cases hinj : Set.InjOn f (↑U.powerset : Set (Finset (Fin l.length)))
  · have hsums_card : sums.card = 2 ^ l.length := by
      calc
        sums.card = U.powerset.card := Finset.card_image_of_injOn hinj
        _ = 2 ^ l.length := by simp [U]
    obtain ⟨a, b, ha, hb, hab, hgap⟩ := sorted_gap_exists sums hcard hzero hone hI
    rcases Finset.mem_image.mp ha with ⟨R, hR, hRa⟩
    rcases Finset.mem_image.mp hb with ⟨T, hT, hTb⟩
    let P := T \ R
    let Q := R \ T
    refine ⟨P, Q, ?_, ?_, ?_⟩
    · apply Finset.not_nonempty_iff_eq_empty.mp
      intro h
      rcases h with ⟨i, hi⟩
      have hiP : i ∈ P := (Finset.mem_inter.mp hi).1
      have hiQ : i ∈ Q := (Finset.mem_inter.mp hi).2
      exact (Finset.mem_sdiff.mp hiP).2 (Finset.mem_sdiff.mp hiQ).1
    · intro hempty
      have hPempty : P = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro h
        rcases h with ⟨i, hi⟩
        have : i ∈ P ∪ Q := Finset.mem_union_left Q hi
        rw [hempty] at this
        simp at this
      have hQempty : Q = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro h
        rcases h with ⟨i, hi⟩
        have : i ∈ P ∪ Q := Finset.mem_union_right P hi
        rw [hempty] at this
        simp at this
      have hRT : R = T := by
        apply Finset.Subset.antisymm
        · intro i hiR
          by_contra hiT
          have : i ∈ Q := Finset.mem_sdiff.mpr ⟨hiR, hiT⟩
          rw [hQempty] at this
          simp at this
        · intro i hiT
          by_contra hiR
          have : i ∈ P := Finset.mem_sdiff.mpr ⟨hiT, hiR⟩
          rw [hPempty] at this
          simp at this
      subst T
      rw [hRa] at hTb
      exact hab.ne hTb
    · have hcancel : (∑ i ∈ P, l[i]) - ∑ i ∈ Q, l[i] = b - a := by
        dsimp [P, Q]
        calc
          (∑ i ∈ T \ R, l[i]) - ∑ i ∈ R \ T, l[i] =
              (∑ i ∈ T, l[i]) - ∑ i ∈ R, l[i] := finset_sum_sdiff_cancel _ R T
          _ = f T - f R := rfl
          _ = b - a := by rw [hRa, hTb]
      rw [hcancel, abs_of_pos (sub_pos.mpr hab)]
      rw [hsums_card] at hgap
      convert hgap using 1 <;> norm_num
  · have hcollide :
        ∃ R ∈ U.powerset, ∃ T ∈ U.powerset, R ≠ T ∧ f R = f T := by
      simp only [Set.InjOn] at hinj
      push Not at hinj
      rcases hinj with ⟨R, hR, T, hT, heq, hne⟩
      exact ⟨R, hR, T, hT, hne, heq⟩
    rcases hcollide with ⟨R, hR, T, hT, hRT, heq⟩
    let P := T \ R
    let Q := R \ T
    refine ⟨P, Q, ?_, ?_, ?_⟩
    · apply Finset.not_nonempty_iff_eq_empty.mp
      intro h
      rcases h with ⟨i, hi⟩
      have hiP : i ∈ P := (Finset.mem_inter.mp hi).1
      have hiQ : i ∈ Q := (Finset.mem_inter.mp hi).2
      exact (Finset.mem_sdiff.mp hiP).2 (Finset.mem_sdiff.mp hiQ).1
    · intro hempty
      apply hRT
      apply Finset.Subset.antisymm
      · intro i hiR
        by_contra hiT
        have hiQ : i ∈ Q := Finset.mem_sdiff.mpr ⟨hiR, hiT⟩
        have hiU : i ∈ P ∪ Q := Finset.mem_union_right P hiQ
        rw [hempty] at hiU
        simp at hiU
      · intro i hiT
        by_contra hiR
        have hiP : i ∈ P := Finset.mem_sdiff.mpr ⟨hiT, hiR⟩
        have hiU : i ∈ P ∪ Q := Finset.mem_union_left Q hiP
        rw [hempty] at hiU
        simp at hiU
    · have hcancel : (∑ i ∈ P, l[i]) - ∑ i ∈ Q, l[i] = f T - f R := by
        dsimp [P, Q]
        calc
          (∑ i ∈ T \ R, l[i]) - ∑ i ∈ R \ T, l[i] =
              (∑ i ∈ T, l[i]) - ∑ i ∈ R, l[i] := finset_sum_sdiff_cancel _ R T
          _ = f T - f R := rfl
      rw [hcancel, ← heq]
      have hlpos : 0 < l.length := by
        by_contra h
        have hlzero : l.length = 0 := by omega
        have : l = [] := List.length_eq_zero_iff.mp hlzero
        subst l
        simp at hsum
      have hden : (0 : ℝ) < (2 : ℝ) ^ l.length - 1 := by
        have hpow : (1 : ℝ) < 2 ^ l.length := one_lt_pow₀ (by norm_num) hlpos.ne'
        linarith
      simpa using (one_div_pos.mpr hden).le

/-- Inserting one residual into a sorted multiset of duplicate pairs leaves
exactly that residual as the alternating sum. -/
lemma altSum_orderedInsert_duplicate_list (x : ℝ) : ∀ s : List ℝ,
    s.Pairwise (· ≥ ·) →
    altSum (List.orderedInsert (· ≥ ·) x
      (s.flatMap fun y => [y / 2, y / 2])) = x := by
  intro s hs
  induction s with
  | nil => simp [altSum]
  | cons y s ih =>
    rw [List.pairwise_cons] at hs
    by_cases hxy : x ≥ y / 2
    · rw [List.flatMap_cons]
      simp only [List.cons_append, List.nil_append]
      rw [List.orderedInsert_cons, if_pos hxy]
      have hz := altSum_duplicate_each_sorted s hs.2
      simp only [altSum]
      linarith
    · rw [List.flatMap_cons]
      simp only [List.cons_append, List.nil_append]
      rw [List.orderedInsert_cons, if_neg hxy,
        List.orderedInsert_cons, if_neg hxy]
      simp only [altSum]
      rw [ih hs.2]
      ring

lemma residual_response_alt (l : List ℝ) (r : ℝ) :
    altSum (((l.flatMap fun y => [y / 2, y / 2]) ++ [r]).mergeSort (· ≥ ·)) = r := by
  let s := l.mergeSort (· ≥ ·)
  have hs : s.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) l
  let ds := s.flatMap fun y => [y / 2, y / 2]
  have hds : ds.Pairwise (· ≥ ·) := pairwise_duplicate_each_sorted hs
  have hperm : ds.Perm (l.flatMap fun y => [y / 2, y / 2]) :=
    (List.mergeSort_perm l (· ≥ ·)).flatMap (fun _ _ => List.Perm.refl _)
  have heq : ((l.flatMap fun y => [y / 2, y / 2]) ++ [r]).mergeSort (· ≥ ·) =
      List.orderedInsert (· ≥ ·) r ds := by
    apply List.Perm.eq_of_pairwise'
      (List.pairwise_mergeSort' (· ≥ ·) _)
      (hds.orderedInsert r)
    exact (List.mergeSort_perm _ _).trans
      (List.perm_append_comm.trans ((List.Perm.cons r hperm.symm).trans
        (List.perm_orderedInsert (· ≥ ·) r ds).symm))
  rw [heq]
  exact altSum_orderedInsert_duplicate_list r s hs

/-- A fragment carries its mass, its input-block owner, and its colour. -/
structure OwnedFragment where
  mass : ℝ
  owner : ℕ
  red : Bool

/-- A matched mass records the common mass and its two original owners. -/
structure MatchedPair where
  mass : ℝ
  owner₁ : ℕ
  owner₂ : ℕ

structure MatchingState where
  active : List OwnedFragment
  pairs : List MatchedPair

/-- Read all represented fragments as owner/mass pairs. -/
def ownedPieces (st : MatchingState) : List (ℕ × ℝ) :=
  (st.pairs.flatMap fun p => [(p.owner₁, p.mass), (p.owner₂, p.mass)]) ++
    (st.active.map fun x => (x.owner, x.mass))

/-- The contribution assigned to owner `i`. -/
def ownerTotal (i : ℕ) (st : MatchingState) : ℝ :=
  ((st.pairs.filter (fun p => p.owner₁ = i)).map MatchedPair.mass).sum +
  ((st.pairs.filter (fun p => p.owner₂ = i)).map MatchedPair.mass).sum +
  ((st.active.filter (fun x => x.owner = i)).map OwnedFragment.mass).sum

/-- The signed mass of the still-active components. -/
def signedMass (s : List OwnedFragment) : ℝ :=
  (s.map fun x => if x.red then x.mass else -x.mass).sum

lemma signedMass_cons (x : OwnedFragment) (s : List OwnedFragment) :
    signedMass (x :: s) = (if x.red then x.mass else -x.mass) + signedMass s := by
  rfl

def activeMass (s : List OwnedFragment) : ℝ :=
  (s.map OwnedFragment.mass).sum

lemma activeMass_perm {s t : List OwnedFragment} (h : s.Perm t) :
    activeMass s = activeMass t := by
  unfold activeMass
  exact (h.map OwnedFragment.mass).sum_eq

lemma signedMass_perm {s t : List OwnedFragment} (h : s.Perm t) :
    signedMass s = signedMass t := by
  unfold signedMass
  exact (h.map (fun x => if x.red then x.mass else -x.mass)).sum_eq

lemma ownerTotal_active_perm {s t : List OwnedFragment} (pairs : List MatchedPair)
    (h : s.Perm t) (i : ℕ) :
    ownerTotal i ⟨s, pairs⟩ = ownerTotal i ⟨t, pairs⟩ := by
  unfold ownerTotal
  rw [((h.filter (fun x => x.owner = i)).map OwnedFragment.mass).sum_eq]

lemma signedMass_eq_activeMass_of_all_red (s : List OwnedFragment)
    (hred : ∀ x ∈ s, x.red = true) : signedMass s = activeMass s := by
  unfold signedMass activeMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  rw [hred x hx]
  rfl

lemma signedMass_eq_neg_activeMass_of_all_blue (s : List OwnedFragment)
    (hblue : ∀ x ∈ s, x.red = false) : signedMass s = -activeMass s := by
  induction s with
  | nil => simp [signedMass, activeMass]
  | cons x xs ih =>
      have hx := hblue x (by simp)
      have hxs : ∀ y ∈ xs, y.red = false := by
        intro y hy
        exact hblue y (by simp [hy])
      rw [signedMass_cons, ih hxs]
      simp [activeMass, hx]
      ring

lemma abs_signedMass_eq_activeMass_of_same_color {x : OwnedFragment}
    {xs : List OwnedFragment} (hcolor : ∀ y ∈ xs, y.red = x.red)
    (hpos : 0 < x.mass) (hxs : ∀ y ∈ xs, 0 < y.mass) :
    |signedMass (x :: xs)| = activeMass (x :: xs) := by
  have hnonneg : 0 ≤ activeMass (x :: xs) := by
    unfold activeMass
    apply List.sum_nonneg
    intro z hz
    rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hpos.le
    · exact (hxs y hy).le
  cases hx : x.red
  · have hblue : ∀ y ∈ x :: xs, y.red = false := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact (hcolor y hy).trans hx
    rw [signedMass_eq_neg_activeMass_of_all_blue _ hblue, abs_neg,
      abs_of_nonneg hnonneg]
  · have hred : ∀ y ∈ x :: xs, y.red = true := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact (hcolor y hy).trans hx
    rw [signedMass_eq_activeMass_of_all_red _ hred, abs_of_nonneg hnonneg]

/-- Insert one completed matched mass into the state, leaving the positive
remainder (if any) as a single active component. -/
def reducePair (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) : MatchingState :=
  if hxy : x.mass = y.mass then
    ⟨xs, ⟨x.mass, x.owner, y.owner⟩ :: pairs⟩
  else if hlt : x.mass < y.mass then
    ⟨{ y with mass := y.mass - x.mass } :: xs,
      ⟨x.mass, x.owner, y.owner⟩ :: pairs⟩
  else
    ⟨{ x with mass := x.mass - y.mass } :: xs,
      ⟨y.mass, x.owner, y.owner⟩ :: pairs⟩

lemma reducePair_stateMass (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) :
    2 * ((reducePair x y xs pairs).pairs.map MatchedPair.mass).sum +
      ((reducePair x y xs pairs).active.map OwnedFragment.mass).sum =
    2 * (pairs.map MatchedPair.mass).sum +
      ((x :: y :: xs).map OwnedFragment.mass).sum := by
  unfold reducePair
  split_ifs <;> simp_all <;> linarith

lemma reducePair_active_length (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) :
    (reducePair x y xs pairs).active.length ≤ (x :: y :: xs).length - 1 := by
  unfold reducePair
  split_ifs <;> simp_all <;> omega

lemma reducePair_pairs_length (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) :
    (reducePair x y xs pairs).pairs.length = pairs.length + 1 := by
  unfold reducePair
  split_ifs <;> simp_all <;> omega

lemma reducePair_ownerTotal (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) (i : ℕ) :
    ownerTotal i (reducePair x y xs pairs) =
      ownerTotal i ⟨x :: y :: xs, pairs⟩ := by
  unfold reducePair ownerTotal
  split_ifs with hxy hlt <;> simp_all <;>
    by_cases hxi : x.owner = i <;> by_cases hyi : y.owner = i <;>
      simp_all <;> linarith

lemma reducePair_signedMass (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) (hcolor : x.red ≠ y.red) :
    signedMass (reducePair x y xs pairs).active = signedMass (x :: y :: xs) := by
  unfold reducePair signedMass
  cases hx : x.red <;> cases hy : y.red <;> simp_all
  · split_ifs <;> simp_all <;> linarith
  · split_ifs <;> simp_all <;> linarith

lemma reducePair_active_pos (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) (hx : 0 < x.mass) (hy : 0 < y.mass)
    (hxs : ∀ z ∈ xs, 0 < z.mass) :
    ∀ z ∈ (reducePair x y xs pairs).active, 0 < z.mass := by
  unfold reducePair
  split_ifs with hxy hlt
  · exact hxs
  · intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp only; linarith
    · exact hxs z hz
  · intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp only
      have : y.mass < x.mass := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxy)
      linarith
    · exact hxs z hz

lemma reducePair_pair_pos (x y : OwnedFragment) (xs : List OwnedFragment)
    (pairs : List MatchedPair) (hx : 0 < x.mass) (hy : 0 < y.mass)
    (hpairs : ∀ p ∈ pairs, 0 < p.mass) :
    ∀ p ∈ (reducePair x y xs pairs).pairs, 0 < p.mass := by
  unfold reducePair
  split_ifs with hxy hlt
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simpa [hxy] using hy
    · exact hpairs p hp
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hx
    · exact hpairs p hp
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hy
    · exact hpairs p hp

/-- Abstract invariants of the greedy matching/difference construction.
`initial` is the list of coloured input masses; `out` has at most one residual.
Every pairing contributes one equal fragment to each of its two owners. -/
def RefinementCertificate (initial : List OwnedFragment) : Prop :=
  ∃ out : MatchingState,
    out.active.length ≤ 1 ∧
    (∀ x ∈ out.active, 0 < x.mass) ∧
    (∀ p ∈ out.pairs, 0 < p.mass) ∧
    (∀ i, ownerTotal i out = ownerTotal i ⟨initial, []⟩) ∧
    (2 * (out.pairs.map MatchedPair.mass).sum +
      (out.active.map OwnedFragment.mass).sum =
      (initial.map OwnedFragment.mass).sum) ∧
    out.active.length + 2 * out.pairs.length ≤ 2 * initial.length - 1

private lemma matching_induction : ∀ initial : List OwnedFragment,
    initial ≠ [] → (∀ x ∈ initial, 0 < x.mass) →
    RefinementCertificate initial := by
  intro initial
  induction hn : initial.length using Nat.strongRecOn generalizing initial with
  | ind n ih =>
      intro hne hpos
      cases initial with
      | nil => contradiction
      | cons x tail =>
        cases tail with
        | nil =>
          refine ⟨⟨[x], []⟩, by simp, ?_, by simp, ?_, by simp⟩
          · intro z hz
            simpa using hpos z hz
          · intro i
            simp [ownerTotal]
        | cons y xs =>
          let st := reducePair x y xs []
          have hx : 0 < x.mass := hpos x (by simp)
          have hy : 0 < y.mass := hpos y (by simp)
          have hxs : ∀ z ∈ xs, 0 < z.mass := by
            intro z hz
            exact hpos z (by simp [hz])
          have hstpos : ∀ z ∈ st.active, 0 < z.mass :=
            reducePair_active_pos x y xs [] hx hy hxs
          by_cases hstnil : st.active = []
          · refine ⟨st, by simp [hstnil], hstpos,
              reducePair_pair_pos x y xs [] hx hy (by simp), ?_, ?_, ?_⟩
            · intro i
              exact reducePair_ownerTotal x y xs [] i
            · simpa [st] using reducePair_stateMass x y xs []
            · rw [hstnil]
              have hp := reducePair_pairs_length x y xs []
              simp only [st, List.length_nil, Nat.zero_add, List.length_cons] at hp ⊢
              omega
          · have hlt : st.active.length < n := by
              have hh := reducePair_active_length x y xs []
              dsimp only [st]
              simp only [List.length_cons] at hh hn
              omega
            obtain ⟨out, houtlen, houtpos, houtpairpos, houtowner,
                houtmass, houtbudget⟩ := ih st.active.length hlt st.active rfl hstnil hstpos
            let final : MatchingState := ⟨out.active, out.pairs ++ st.pairs⟩
            refine ⟨final, houtlen, houtpos, ?_, ?_, ?_, ?_⟩
            · intro p hp
              rw [show final.pairs = out.pairs ++ st.pairs by rfl, List.mem_append] at hp
              rcases hp with hp | hp
              · exact houtpairpos p hp
              · exact reducePair_pair_pos x y xs [] hx hy (by simp) p hp
            · intro i
              unfold final
              simp only [ownerTotal, List.filter_append, List.map_append, List.sum_append]
              have ho := houtowner i
              unfold ownerTotal at ho
              simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at ho
              have hr := reducePair_ownerTotal x y xs [] i
              unfold ownerTotal at hr
              dsimp only [st] at hr
              linarith
            · have hr := reducePair_stateMass x y xs []
              change 2 * ((out.pairs ++ st.pairs).map MatchedPair.mass).sum +
                (out.active.map OwnedFragment.mass).sum = _
              rw [List.map_append, List.sum_append]
              dsimp only [st] at houtmass hr
              simp only [List.map_nil, List.sum_nil, mul_zero, zero_add] at houtmass hr
              linarith
            · have hp : st.pairs.length = 1 := by
                simpa [st] using reducePair_pairs_length x y xs []
              have ha : st.active.length ≤ xs.length + 1 := by
                have h := reducePair_active_length x y xs []
                simpa [st] using h
              change out.active.length + 2 * (out.pairs ++ st.pairs).length ≤
                2 * (x :: y :: xs).length - 1
              simp only [List.length_append, List.length_cons]
              omega

/-- The greedy matching/difference construction used below. -/
lemma greedy_refinement_certificate (initial : List OwnedFragment)
    (hne : initial ≠ []) (hpos : ∀ x ∈ initial, 0 < x.mass) :
    RefinementCertificate initial :=
  matching_induction initial hne hpos

/-- Build the ordered block list from a matching state. -/
def blocksOfState (m : ℕ) (st : MatchingState) : List (List ℝ) :=
  List.ofFn fun i : Fin m =>
    ((st.pairs.filter (fun p => p.owner₁ = (i : ℕ))).map MatchedPair.mass) ++
    ((st.pairs.filter (fun p => p.owner₂ = (i : ℕ))).map MatchedPair.mass) ++
    ((st.active.filter (fun x => x.owner = (i : ℕ))).map OwnedFragment.mass)

lemma blocksOfState_length (m : ℕ) (st : MatchingState) :
    (blocksOfState m st).length = m := by
  simp [blocksOfState]

lemma blocksOfState_sum (m : ℕ) (st : MatchingState) (i : Fin m) :
    ((blocksOfState m st)[i]'(by rw [blocksOfState_length]; exact i.2)).sum =
      ownerTotal i st := by
  simp [blocksOfState, ownerTotal, add_assoc]

lemma owner_filter_sum_ofFn {n : ℕ} (f : Fin n → ℝ) (c : Fin n → Bool) :
    ∀ (i : Fin n),
    (((List.ofFn (fun j : Fin n =>
      (⟨f j, j, c j⟩ : OwnedFragment))).filter
        (fun x => x.owner = (i : ℕ))).map OwnedFragment.mass).sum = f i := by
  intro i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [List.ofFn_succ]
          simp only [Fin.val_zero]
          rw [List.filter_cons_of_pos (by simp)]
          simp only [List.map_cons, List.sum_cons]
          have hzero :
              (((List.ofFn (fun j : Fin n =>
                (⟨f j.succ, j.succ, c j.succ⟩ : OwnedFragment))).filter
                  (fun x => x.owner = 0)).map OwnedFragment.mass).sum = 0 := by
            apply List.sum_eq_zero
            intro z hz
            rcases List.mem_map.mp hz with ⟨q, hq, rfl⟩
            rcases List.mem_filter.mp hq with ⟨hqmem, hqowner⟩
            rcases List.mem_ofFn.mp hqmem with ⟨j, rfl⟩
            simp at hqowner
          simpa using hzero
      | succ i =>
          rw [List.ofFn_succ]
          simp only [Fin.val_zero, Fin.val_succ]
          rw [List.filter_cons_of_neg (by simp)]
          have hih := ih (fun j => f j.succ) (fun j => c j.succ) i
          let shift : OwnedFragment → OwnedFragment := fun q =>
            { q with owner := q.owner + 1 }
          have hmap :
              List.ofFn (fun j : Fin n =>
                (⟨f j.succ, j.succ, c j.succ⟩ : OwnedFragment)) =
              (List.ofFn (fun j : Fin n =>
                (⟨f j.succ, j, c j.succ⟩ : OwnedFragment))).map shift := by
            apply List.ext_get
            · simp
            · intro k hk hk'
              simp [shift]
          change
            (((List.ofFn (fun j : Fin n =>
              (⟨f j.succ, j.succ, c j.succ⟩ : OwnedFragment))).filter
                (fun x => x.owner = ((i.succ : Fin (n + 1)) : ℕ))).map
                  OwnedFragment.mass).sum = f i.succ
          rw [hmap, List.filter_map]
          simpa [shift, Function.comp_def, Nat.add_left_cancel_iff] using hih

lemma initial_owner_total {l : List ℝ} (P : Finset (Fin l.length)) :
    ∀ (i : Fin l.length),
    ownerTotal i ⟨List.ofFn (fun j : Fin l.length =>
      (⟨l[j], j, j ∈ P⟩ : OwnedFragment)), []⟩ = l[i] := by
  intro i
  unfold ownerTotal
  simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add]
  exact owner_filter_sum_ofFn (fun j : Fin l.length => l[j]) (fun j => j ∈ P) i


lemma blocksOfState_pos {m : ℕ} {st : MatchingState}
    (ha : ∀ x ∈ st.active, 0 < x.mass)
    (hp : ∀ p ∈ st.pairs, 0 < p.mass) :
    ∀ b ∈ blocksOfState m st, ∀ x ∈ b, 0 < x := by
  intro b hb x hx
  rcases List.mem_ofFn.mp hb with ⟨i, rfl⟩
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · rcases List.mem_map.mp hx with ⟨p, hp', hpx⟩
      rw [← hpx]
      exact hp p (List.mem_filter.mp hp').1
    · rcases List.mem_map.mp hx with ⟨p, hp', hpx⟩
      rw [← hpx]
      exact hp p (List.mem_filter.mp hp').1
  · rcases List.mem_map.mp hx with ⟨a, ha', hax⟩
    rw [← hax]
    exact ha a (List.mem_filter.mp ha').1

private lemma flatten_owner_partition {m : ℕ} (pieces : List (ℕ × ℝ))
    (howner : ∀ q ∈ pieces, q.1 < m) :
    (List.ofFn fun i : Fin m =>
      ((pieces.filter (fun q => q.1 = (i : ℕ))).map Prod.snd)).flatten.Perm
      (pieces.map Prod.snd) := by
  induction m generalizing pieces with
  | zero =>
      have : pieces = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro q hq
        exact Nat.not_lt_zero q.1 (howner q hq)
      simp [this]
  | succ m ih =>
      rw [List.ofFn_succ, List.flatten_cons]
      let first := pieces.filter (fun q => q.1 = 0)
      let rest := pieces.filter (fun q => !(q.1 = 0))
      let predPieces := rest.map fun q => (q.1 - 1, q.2)
      have hpred : ∀ q ∈ predPieces, q.1 < m := by
        intro q hq
        rcases List.mem_map.mp hq with ⟨z, hz, rfl⟩
        have hzowner := howner z (List.mem_filter.mp hz).1
        have hz0 : z.1 ≠ 0 := by
          have hzbool := (List.mem_filter.mp hz).2
          simpa using hzbool
        simp only
        omega
      have hih := ih predPieces hpred
      have htail :
          (List.ofFn fun i : Fin m =>
            ((pieces.filter (fun q => q.1 = (i.succ : ℕ))).map Prod.snd)).flatten.Perm
          (rest.map Prod.snd) := by
        unfold predPieces rest at hih
        simp only [List.filter_map, List.map_map, Function.comp_def] at hih
        have hfilter : ∀ (i : Fin m),
            (List.filter (fun x => x.1 - 1 = (i : ℕ))
              (List.filter (fun q => !(q.1 = 0)) pieces)).map Prod.snd =
            (pieces.filter (fun q => q.1 = (i.succ : ℕ))).map Prod.snd := by
          intro i
          congr 1
          rw [List.filter_filter]
          apply List.filter_congr
          intro q hq
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨hsub, hne⟩
            have hpos : 0 < q.1 := Nat.pos_of_ne_zero (by
              simpa using hne)
            have hs : q.1 = (i : ℕ) + 1 := by omega
            simpa using hs
          · intro heq
            have hs : q.1 = (i : ℕ) + 1 := by simpa using heq
            constructor
            · omega
            · have hz : q.1 ≠ 0 := by omega
              simp [hz]
        have hfn : (List.ofFn fun i : Fin m =>
            ((List.filter (fun x => x.1 - 1 = (i : ℕ))
              (List.filter (fun q => !(q.1 = 0)) pieces)).map Prod.snd)) =
            List.ofFn fun i : Fin m =>
              ((pieces.filter (fun q => q.1 = (i.succ : ℕ))).map Prod.snd) := by
          apply congrArg List.ofFn
          funext i
          exact hfilter i
        rw [hfn] at hih
        exact hih.trans (by
          unfold rest
          rfl)
      have hsplit : (first ++ rest).Perm pieces := by
        unfold first rest
        exact List.filter_append_perm (fun q => q.1 = 0) pieces
      simpa [first, rest] using
        (List.Perm.append_left (first.map Prod.snd) htail).trans (by
          simpa only [List.map_append] using hsplit.map Prod.snd)

lemma blocksOfState_flatten_perm {m : ℕ} {st : MatchingState}
    (hpairs₁ : ∀ p ∈ st.pairs, p.owner₁ < m)
    (hpairs₂ : ∀ p ∈ st.pairs, p.owner₂ < m)
    (hactive : ∀ x ∈ st.active, x.owner < m) :
    (blocksOfState m st).flatten.Perm ((ownedPieces st).map Prod.snd) := by
  let pieces : List (ℕ × ℝ) := ownedPieces st
  have howner : ∀ q ∈ pieces, q.1 < m := by
    intro q hq
    unfold pieces ownedPieces at hq
    rw [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases List.mem_flatMap.mp hq with ⟨p, hp, hqp⟩
      rcases List.mem_cons.mp hqp with hqp | hqp
      · rw [hqp]
        exact hpairs₁ p hp
      · rw [List.mem_singleton] at hqp
        rw [hqp]
        exact hpairs₂ p hp
    · rcases List.mem_map.mp hq with ⟨a, ha, rfl⟩
      exact hactive a ha
  have hpartition := flatten_owner_partition pieces howner
  have hblockLists : List.Forall₂ List.Perm (blocksOfState m st)
      (List.ofFn fun i : Fin m =>
        ((pieces.filter (fun q => q.1 = (i : ℕ))).map Prod.snd)) := by
    rw [List.forall₂_iff_get]
    constructor
    · simp [blocksOfState]
    · intro k hk hk'
      simp only [List.get_eq_getElem, blocksOfState, List.getElem_ofFn]
      let i : Fin m := ⟨k, by simpa [blocksOfState] using hk⟩
      change (((st.pairs.filter (fun p => p.owner₁ = (i : ℕ))).map MatchedPair.mass) ++
          ((st.pairs.filter (fun p => p.owner₂ = (i : ℕ))).map MatchedPair.mass) ++
          ((st.active.filter (fun x => x.owner = (i : ℕ))).map OwnedFragment.mass)).Perm
        ((pieces.filter (fun q => q.1 = (i : ℕ))).map Prod.snd)
      have hpermPairs :
          (((st.pairs.filter (fun p => p.owner₁ = (i : ℕ))).map MatchedPair.mass) ++
           ((st.pairs.filter (fun p => p.owner₂ = (i : ℕ))).map MatchedPair.mass)).Perm
          (((st.pairs.flatMap fun p : MatchedPair =>
            [(p.owner₁, p.mass), (p.owner₂, p.mass)]).filter
            (fun q => q.1 = (i : ℕ))).map Prod.snd) := by
        induction st.pairs with
        | nil => simp
        | cons p ps ih =>
            simp only [List.filter_cons, List.map_cons, List.flatMap_cons,
              List.filter_append, List.map_append]
            by_cases h1 : p.owner₁ = i <;> by_cases h2 : p.owner₂ = i
            · simp [h1, h2]
              exact List.perm_middle.trans (List.Perm.cons p.mass ih)
            · simp_all
            · simp_all
              exact List.perm_middle.trans (List.Perm.cons p.mass ih)
            · simp_all
      have hactiveEq :
          ((st.active.filter (fun x => x.owner = (i : ℕ))).map OwnedFragment.mass) =
          (((st.active.map fun x => (x.owner, x.mass)).filter
            (fun q => q.1 = (i : ℕ))).map Prod.snd) := by
        induction st.active with
        | nil => simp
        | cons a as ih =>
            simp only [List.map_cons, List.filter_cons]
            by_cases ha : a.owner = i <;> simp_all
      unfold pieces ownedPieces
      simp only [List.filter_append, List.map_append]
      exact hpermPairs.append (List.Perm.of_eq hactiveEq)
  exact (List.Perm.flatten_congr hblockLists).trans hpartition


/-- Owner indices in any certified state stay in range. -/
lemma certificate_owners_lt {initial : List OwnedFragment} {out : MatchingState}
    (hownerInitial : ∀ x ∈ initial, x.owner < initial.length)
    (houtpos : ∀ x ∈ out.active, 0 < x.mass)
    (hpairpos : ∀ p ∈ out.pairs, 0 < p.mass)
    (htotal : ∀ i, ownerTotal i out = ownerTotal i ⟨initial, []⟩) :
    (∀ p ∈ out.pairs, p.owner₁ < initial.length) ∧
    (∀ p ∈ out.pairs, p.owner₂ < initial.length) ∧
    (∀ x ∈ out.active, x.owner < initial.length) := by
  have initial_zero (i : ℕ) (hi : initial.length ≤ i) :
      ownerTotal i ⟨initial, []⟩ = 0 := by
    unfold ownerTotal
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add]
    have hempty : initial.filter (fun x => x.owner = i) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      rcases List.mem_filter.mp hx with ⟨hxin, hxeq⟩
      have heq : x.owner = i := of_decide_eq_true hxeq
      have hxlt := hownerInitial x hxin
      omega
    rw [hempty]
    simp
  have first : ∀ p ∈ out.pairs, p.owner₁ < initial.length := by
    intro p hp
    by_contra h
    have hz := initial_zero p.owner₁ (by omega)
    have heq := htotal p.owner₁
    have hnonneg₂ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₂ = p.owner₁)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hnonnega : 0 ≤
        ((out.active.filter (fun x => x.owner = p.owner₁)).map OwnedFragment.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨x, hx, rfl⟩
      exact (houtpos x (List.mem_filter.mp hx).1).le
    have hp_le : p.mass ≤
        ((out.pairs.filter (fun q => q.owner₁ = p.owner₁)).map MatchedPair.mass).sum := by
      apply List.single_le_sum
      · intro z hzmem
        rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
        exact (hpairpos q (List.mem_filter.mp hq).1).le
      · apply List.mem_map.mpr
        exact ⟨p, List.mem_filter.mpr ⟨hp, by simp⟩, rfl⟩
    simp only [ownerTotal, List.filter_nil, List.map_nil, List.sum_nil, zero_add] at hz
    unfold ownerTotal at heq
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at heq
    rw [hz] at heq
    linarith [hpairpos p hp]
  have second : ∀ p ∈ out.pairs, p.owner₂ < initial.length := by
    intro p hp
    by_contra h
    have hz := initial_zero p.owner₂ (by omega)
    have heq := htotal p.owner₂
    have hnonneg₁ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₁ = p.owner₂)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hnonnega : 0 ≤
        ((out.active.filter (fun x => x.owner = p.owner₂)).map OwnedFragment.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨x, hx, rfl⟩
      exact (houtpos x (List.mem_filter.mp hx).1).le
    have hp_le : p.mass ≤
        ((out.pairs.filter (fun q => q.owner₂ = p.owner₂)).map MatchedPair.mass).sum := by
      apply List.single_le_sum
      · intro z hzmem
        rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
        exact (hpairpos q (List.mem_filter.mp hq).1).le
      · apply List.mem_map.mpr
        exact ⟨p, List.mem_filter.mpr ⟨hp, by simp⟩, rfl⟩
    simp only [ownerTotal, List.filter_nil, List.map_nil, List.sum_nil, zero_add] at hz
    unfold ownerTotal at heq
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at heq
    rw [hz] at heq
    linarith [hpairpos p hp]
  have third : ∀ x ∈ out.active, x.owner < initial.length := by
    intro x hx
    by_contra h
    have hz := initial_zero x.owner (by omega)
    have heq := htotal x.owner
    have hnonneg₁ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₁ = x.owner)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hnonneg₂ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₂ = x.owner)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hx_le : x.mass ≤
        ((out.active.filter (fun a => a.owner = x.owner)).map OwnedFragment.mass).sum := by
      apply List.single_le_sum
      · intro z hzmem
        rcases List.mem_map.mp hzmem with ⟨a, ha, rfl⟩
        exact (houtpos a (List.mem_filter.mp ha).1).le
      · apply List.mem_map.mpr
        exact ⟨x, List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
    simp only [ownerTotal, List.filter_nil, List.map_nil, List.sum_nil, zero_add] at hz
    unfold ownerTotal at heq
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at heq
    rw [hz] at heq
    linarith [houtpos x hx]
  exact ⟨first, second, third⟩
/-- A finite positive list of total mass one admits ordered refinement blocks,
one per input, using at most `2m-1` positive fragments.  Its flattened
multiset consists of duplicate pairs and, unless it is zero, one nonnegative
residual. -/
theorem finite_list_response_weak {l : List ℝ} {m : ℕ}
    (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x)
    (hsum : l.sum = 1) (hlen : l.length = m) :
    ∃ blocks : List (List ℝ), ∃ paired : List ℝ, ∃ r : ℝ,
      ∃ hblocks : blocks.length = m,
      (∀ i : Fin m, (blocks[i]'(by simpa [hblocks] using i.2)).sum =
        l[i]'(by simpa [hlen] using i.2)) ∧
      (∀ b ∈ blocks, ∀ x ∈ b, 0 < x) ∧
      blocks.flatten.length ≤ 2 * m - 1 ∧
      blocks.flatten.Perm
        ((paired.flatMap fun x => [x, x]) ++ if r = 0 then [] else [r]) ∧
      0 ≤ r ∧ r ≤ 1 := by
  have hm : 0 < m := by
    rw [← hlen]
    exact List.length_pos_iff.mpr hne
  let initial : List OwnedFragment := List.ofFn fun i : Fin l.length =>
    ⟨l[i], i, false⟩
  have hinitialne : initial ≠ [] := by
    rw [List.ne_nil_iff_length_pos]
    simp [initial, hm, hlen]
  have hinitialpos : ∀ x ∈ initial, 0 < x.mass := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact hpos l[i] (List.getElem_mem i.2)
  obtain ⟨out, houtlen, houtpos, hpairpos, houtowner,
      houtmass, houtbudget⟩ :=
    greedy_refinement_certificate initial hinitialne hinitialpos
  have hownerInitial : ∀ x ∈ initial, x.owner < initial.length := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    simp [initial]
  obtain ⟨hown₁, hown₂, howna⟩ :=
    certificate_owners_lt hownerInitial houtpos hpairpos houtowner
  have hown₁m : ∀ p ∈ out.pairs, p.owner₁ < m := by
    simpa [initial, hlen] using hown₁
  have hown₂m : ∀ p ∈ out.pairs, p.owner₂ < m := by
    simpa [initial, hlen] using hown₂
  have hownam : ∀ x ∈ out.active, x.owner < m := by
    simpa [initial, hlen] using howna
  let blocks := blocksOfState m out
  let paired := out.pairs.map MatchedPair.mass
  let r := (out.active.map OwnedFragment.mass).sum
  have hblocklen : blocks.length = m := blocksOfState_length m out
  have hblocksum : ∀ i : Fin m,
      (blocks[i]'(by simpa [hblocklen] using i.2)).sum =
        l[i]'(by simpa [hlen] using i.2) := by
    intro i
    unfold blocks
    rw [blocksOfState_sum]
    rw [houtowner]
    have hi : (i : ℕ) < l.length := by simpa [hlen] using i.2
    exact initial_owner_total ∅ ⟨i, hi⟩
  have hblockpos : ∀ b ∈ blocks, ∀ x ∈ b, 0 < x :=
    blocksOfState_pos houtpos hpairpos
  have hperm0 := blocksOfState_flatten_perm hown₁m hown₂m hownam
  have hblockbudget : blocks.flatten.length ≤ 2 * m - 1 := by
    unfold blocks
    rw [hperm0.length_eq]
    unfold ownedPieces
    simp only [List.map_append, List.length_append, List.length_map]
    have hpairslen :
        (out.pairs.flatMap fun p => [(p.owner₁, p.mass), (p.owner₂, p.mass)]).length =
        2 * out.pairs.length := by
      induction out.pairs with
      | nil => simp
      | cons p ps ih => simp [ih, Nat.mul_succ]
    rw [hpairslen]
    simpa [initial, hlen, Nat.add_comm] using houtbudget
  have hshape : blocks.flatten.Perm
      ((paired.flatMap fun x => [x, x]) ++ if r = 0 then [] else [r]) := by
    have hperm := hperm0
    unfold blocks
    unfold ownedPieces at hperm
    unfold paired r
    simp only [List.map_append, List.map_flatMap, Function.comp_def] at hperm
    have hpairsmap :
        ((out.pairs.flatMap fun p => [(p.owner₁, p.mass), (p.owner₂, p.mass)]).map
          Prod.snd) =
        (out.pairs.map MatchedPair.mass).flatMap (fun x => [x, x]) := by
      induction out.pairs with
      | nil => simp
      | cons p ps ih => simp [ih]
    change blocks.flatten.Perm _
    have hpairsmap' :
        (out.pairs.flatMap fun p => ([(p.owner₁, p.mass), (p.owner₂, p.mass)].map
          Prod.snd)) =
        (out.pairs.map MatchedPair.mass).flatMap (fun x => [x, x]) := by
      simp [List.flatMap_map, Function.comp_def]
    rw [hpairsmap'] at hperm
    cases ha : out.active with
    | nil => simpa [ha] using hperm
    | cons a as =>
        have hasnil : as = [] := by
          have h := houtlen
          rw [ha] at h
          simp only [List.length_cons] at h
          exact List.length_eq_zero_iff.mp (by omega)
        subst as
        have hapos := houtpos a (by rw [ha]; simp)
        simp [ha, hapos.ne'] at hperm ⊢
        exact hperm
  have hrnonneg : 0 ≤ r := by
    unfold r
    apply List.sum_nonneg
    intro z hz
    rcases List.mem_map.mp hz with ⟨a, ha, rfl⟩
    exact (houtpos a ha).le
  have hrleone : r ≤ 1 := by
    have hinitmass : (initial.map OwnedFragment.mass).sum = 1 := by
      have hmap : initial.map OwnedFragment.mass = l := by
        apply List.ext_get
        · simp [initial]
        · intro k hk hk'
          simp [initial]
      rw [hmap, hsum]
    rw [hinitmass] at houtmass
    have hpnonneg : 0 ≤ (out.pairs.map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hz
      rcases List.mem_map.mp hz with ⟨p, hp, rfl⟩
      exact (hpairpos p hp).le
    unfold r
    linarith
  refine ⟨blocks, paired, r, hblocklen, hblocksum, hblockpos,
    hblockbudget, hshape, hrnonneg, ?_⟩
  exact hrleone

/-- The bookkeeping identity behind the sharp responder: overlay the `p` and
`q` selected intervals with `p+q-1` cuts, then bisect every unused interval. -/
lemma critical_response_cut_budget (n p q : ℕ)
    (hpq : p + q ≤ n + 1) (hnonempty : 0 < p + q) :
    (p + q - 1) + ((n + 1) - (p + q)) = n := by
  omega

/-- Abstract combinatorial endpoint of the critical response construction. -/
lemma sharp_upper_response_core (n : ℕ) (l paired : List ℝ) (r : ℝ)
    (hshape : paired.Perm ((l.flatMap fun x => [x / 2, x / 2]) ++ [r]))
    (hr : |r| ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1)) :
    |altSum (paired.mergeSort (· ≥ ·))| ≤
      1 / ((2 : ℝ) ^ (n + 1) - 1) := by
  have heq : paired.mergeSort (· ≥ ·) =
      ((l.flatMap fun x => [x / 2, x / 2]) ++ [r]).mergeSort (· ≥ ·) := by
    apply List.Perm.eq_of_pairwise'
      (List.pairwise_mergeSort' (· ≥ ·) _)
      (List.pairwise_mergeSort' (· ≥ ·) _)
    exact (List.mergeSort_perm _ _).trans
      (hshape.trans (List.mergeSort_perm _ _).symm)
  rw [heq, residual_response_alt]
  exact hr

/-!
The sharp abstract response.  Unlike `matching_induction`, the matching below
keeps the two colours in separate lists, so every completed pair is formed
from opposite colours.
-/

/-- All active fragments have one colour. -/
def Monochromatic (s : List OwnedFragment) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x.red = y.red

/-- The invariants supplied by matching a red list against a blue list. -/
def OppositeMatchingCertificate (reds blues : List OwnedFragment) : Prop :=
  ∃ out : MatchingState,
    (∀ x ∈ out.active, 0 < x.mass) ∧
    (∀ p ∈ out.pairs, 0 < p.mass) ∧
    Monochromatic out.active ∧
    (∀ i, ownerTotal i out = ownerTotal i ⟨reds ++ blues, []⟩) ∧
    signedMass out.active = signedMass (reds ++ blues) ∧
    out.active.length + out.pairs.length ≤ reds.length + blues.length ∧
    (reds ++ blues ≠ [] → out.pairs.length < reds.length + blues.length)

private lemma opposite_matching_induction : ∀ reds blues : List OwnedFragment,
    (∀ x ∈ reds, x.red = true) →
    (∀ x ∈ blues, x.red = false) →
    (∀ x ∈ reds, 0 < x.mass) →
    (∀ x ∈ blues, 0 < x.mass) →
    OppositeMatchingCertificate reds blues := by
  intro reds blues
  induction hn : reds.length + blues.length using Nat.strongRecOn generalizing reds blues with
  | ind n ih =>
      intro hred hblue hredpos hbluepos
      cases reds with
      | nil =>
          refine ⟨⟨blues, []⟩, hbluepos, by simp, ?_, by simp [ownerTotal], by simp,
            by simp, ?_⟩
          · intro x hx y hy
            exact (hblue x hx).trans (hblue y hy).symm
          · intro hne
            simpa using List.length_pos_iff.mpr hne
      | cons x xs =>
          cases blues with
          | nil =>
              refine ⟨⟨x :: xs, []⟩, hredpos, by simp, ?_, by simp [ownerTotal], by simp,
                by simp, ?_⟩
              · intro a ha b hb
                exact (hred a ha).trans (hred b hb).symm
              · intro _
                simp
          | cons y ys =>
              have hxred : x.red = true := hred x (by simp)
              have hyblue : y.red = false := hblue y (by simp)
              have hxpos : 0 < x.mass := hredpos x (by simp)
              have hypos : 0 < y.mass := hbluepos y (by simp)
              have hxsred : ∀ z ∈ xs, z.red = true := by
                intro z hz
                exact hred z (by simp [hz])
              have hysblue : ∀ z ∈ ys, z.red = false := by
                intro z hz
                exact hblue z (by simp [hz])
              have hxspos : ∀ z ∈ xs, 0 < z.mass := by
                intro z hz
                exact hredpos z (by simp [hz])
              have hyspos : ∀ z ∈ ys, 0 < z.mass := by
                intro z hz
                exact hbluepos z (by simp [hz])
              by_cases heq : x.mass = y.mass
              · have hlt : xs.length + ys.length < n := by
                  simp only [List.length_cons] at hn
                  omega
                obtain ⟨out, haPos, hpPos, hmono, howner, hsigned, hcount, hpairslt⟩ :=
                  ih (xs.length + ys.length) hlt xs ys rfl hxsred hysblue hxspos hyspos
                let p : MatchedPair := ⟨x.mass, x.owner, y.owner⟩
                let final : MatchingState := ⟨out.active, p :: out.pairs⟩
                refine ⟨final, haPos, ?_, hmono, ?_, ?_, ?_, ?_⟩
                · intro q hq
                  rcases List.mem_cons.mp hq with rfl | hq
                  · exact hxpos
                  · exact hpPos q hq
                · intro i
                  have ho := howner i
                  change ownerTotal i ⟨out.active, p :: out.pairs⟩ =
                    ownerTotal i ⟨(x :: xs) ++ (y :: ys), []⟩
                  unfold ownerTotal at ho ⊢
                  dsimp [p]
                  by_cases hxi : x.owner = i <;> by_cases hyi : y.owner = i <;>
                    simp_all [List.filter_append, List.map_append, List.sum_append] <;> linarith
                · have hs := hsigned
                  change signedMass out.active = signedMass ((x :: xs) ++ (y :: ys))
                  unfold signedMass at hs ⊢
                  simp [hxred, hyblue] at hs ⊢
                  linarith
                · unfold final
                  simp only [List.length_cons]
                  simp only [List.length_cons] at hn
                  omega
                · intro _
                  unfold final
                  simp only [List.length_cons]
                  simp only [List.length_cons] at hn
                  omega
              · by_cases hxy : x.mass < y.mass
                · let y' : OwnedFragment := { y with mass := y.mass - x.mass }
                  have hy'blue : y'.red = false := by simp [y', hyblue]
                  have hy'pos : 0 < y'.mass := by simp [y']; linarith
                  have hlt : xs.length + (y' :: ys).length < n := by
                    simp only [List.length_cons] at hn ⊢
                    omega
                  obtain ⟨out, haPos, hpPos, hmono, howner, hsigned, hcount, hpairslt⟩ :=
                    ih (xs.length + (y' :: ys).length) hlt xs (y' :: ys) rfl
                      hxsred (by
                        intro z hz
                        rcases List.mem_cons.mp hz with rfl | hz
                        · exact hy'blue
                        · exact hysblue z hz)
                      hxspos (by
                        intro z hz
                        rcases List.mem_cons.mp hz with rfl | hz
                        · exact hy'pos
                        · exact hyspos z hz)
                  let p : MatchedPair := ⟨x.mass, x.owner, y.owner⟩
                  let final : MatchingState := ⟨out.active, p :: out.pairs⟩
                  refine ⟨final, haPos, ?_, hmono, ?_, ?_, ?_, ?_⟩
                  · intro q hq
                    rcases List.mem_cons.mp hq with rfl | hq
                    · exact hxpos
                    · exact hpPos q hq
                  · intro i
                    have ho := howner i
                    change ownerTotal i ⟨out.active, p :: out.pairs⟩ =
                      ownerTotal i ⟨(x :: xs) ++ (y :: ys), []⟩
                    unfold ownerTotal at ho ⊢
                    dsimp [p]
                    by_cases hxi : x.owner = i <;> by_cases hyi : y.owner = i <;>
                      simp_all [List.filter_append, List.map_append, List.sum_append, y'] <;>
                        linarith
                  · have hs := hsigned
                    change signedMass out.active = signedMass ((x :: xs) ++ (y :: ys))
                    unfold signedMass at hs ⊢
                    simp [hxred, hyblue, y', hy'blue] at hs ⊢
                    linarith
                  · unfold final
                    simp only [List.length_cons]
                    simp only [List.length_cons] at hn
                    omega
                  · intro _
                    unfold final
                    simp only [List.length_cons]
                    have hpair := hpairslt (by simp)
                    simp only [List.length_cons] at hn hpair
                    omega
                · have hyx : y.mass < x.mass := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm heq)
                  let x' : OwnedFragment := { x with mass := x.mass - y.mass }
                  have hx'red : x'.red = true := by simp [x', hxred]
                  have hx'pos : 0 < x'.mass := by simp [x']; linarith
                  have hlt : (x' :: xs).length + ys.length < n := by
                    simp only [List.length_cons] at hn ⊢
                    omega
                  obtain ⟨out, haPos, hpPos, hmono, howner, hsigned, hcount, hpairslt⟩ :=
                    ih ((x' :: xs).length + ys.length) hlt (x' :: xs) ys rfl
                      (by
                        intro z hz
                        rcases List.mem_cons.mp hz with rfl | hz
                        · exact hx'red
                        · exact hxsred z hz)
                      hysblue
                      (by
                        intro z hz
                        rcases List.mem_cons.mp hz with rfl | hz
                        · exact hx'pos
                        · exact hxspos z hz)
                      hyspos
                  let p : MatchedPair := ⟨y.mass, x.owner, y.owner⟩
                  let final : MatchingState := ⟨out.active, p :: out.pairs⟩
                  refine ⟨final, haPos, ?_, hmono, ?_, ?_, ?_, ?_⟩
                  · intro q hq
                    rcases List.mem_cons.mp hq with rfl | hq
                    · exact hypos
                    · exact hpPos q hq
                  · intro i
                    have ho := howner i
                    change ownerTotal i ⟨out.active, p :: out.pairs⟩ =
                      ownerTotal i ⟨(x :: xs) ++ (y :: ys), []⟩
                    unfold ownerTotal at ho ⊢
                    dsimp [p]
                    by_cases hxi : x.owner = i <;> by_cases hyi : y.owner = i <;>
                      simp_all [List.filter_append, List.map_append, List.sum_append, x'] <;>
                        linarith
                  · have hs := hsigned
                    change signedMass out.active = signedMass ((x :: xs) ++ (y :: ys))
                    unfold signedMass at hs ⊢
                    simp [hxred, hyblue, x', hx'red] at hs ⊢
                    linarith
                  · unfold final
                    simp only [List.length_cons]
                    simp only [List.length_cons] at hn
                    omega
                  · intro _
                    unfold final
                    simp only [List.length_cons]
                    have hpair := hpairslt (by simp)
                    simp only [List.length_cons] at hn hpair
                    omega

/-- Greedily match only opposite-coloured fragments. -/
lemma opposite_matching_certificate (reds blues : List OwnedFragment)
    (hred : ∀ x ∈ reds, x.red = true)
    (hblue : ∀ x ∈ blues, x.red = false)
    (hredpos : ∀ x ∈ reds, 0 < x.mass)
    (hbluepos : ∀ x ∈ blues, 0 < x.mass) :
    OppositeMatchingCertificate reds blues :=
  opposite_matching_induction reds blues hred hblue hredpos hbluepos

/-- Selected inputs, in owner order, carrying one fixed colour. -/
def selectedFragments {l : List ℝ} (S : Finset (Fin l.length)) (red : Bool) :
    List OwnedFragment :=
  S.toList.map fun i : Fin l.length => ⟨l[i], i, red⟩

lemma selectedFragments_color {l : List ℝ} (S : Finset (Fin l.length)) (red : Bool) :
    ∀ x ∈ selectedFragments S red, x.red = red := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  rfl

lemma selectedFragments_pos {l : List ℝ} (S : Finset (Fin l.length)) (red : Bool)
    (hpos : ∀ x ∈ l, 0 < x) :
    ∀ x ∈ selectedFragments S red, 0 < x.mass := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  exact hpos l[i] (List.getElem_mem i.2)

private lemma selectedFragments_ownerTotal_aux {l : List ℝ} (red : Bool)
    (xs : List (Fin l.length)) (hnodup : xs.Nodup) (i : Fin l.length) :
    ownerTotal i ⟨xs.map (fun j : Fin l.length => ⟨l[j], j, red⟩), []⟩ =
      if i ∈ xs then l[i] else 0 := by
  induction xs with
  | nil => simp [ownerTotal]
  | cons j js ih =>
      rw [List.nodup_cons] at hnodup
      unfold ownerTotal at ih ⊢
      simp only [List.map_cons, List.filter_nil, List.map_nil, List.sum_nil,
        List.filter_cons, List.sum_cons, zero_add] at ih ⊢
      by_cases hji : j = i
      · subst j
        have ht := ih hnodup.2
        have htail :
            (List.map OwnedFragment.mass
              (List.filter (fun x => x.owner = (i : ℕ))
                (js.map fun j : Fin l.length => (⟨l[j], j, red⟩ : OwnedFragment)))).sum = 0 := by
          simpa [hnodup.1] using ht
        simp only [List.mem_cons, true_or, if_true]
        simpa using htail
      · have hval : (j : ℕ) ≠ (i : ℕ) := by
          intro h
          exact hji (Fin.ext h)
        have hij : i ≠ j := Ne.symm hji
        have ht := ih hnodup.2
        simp only [List.mem_cons, hij, false_or]
        simpa [hval] using ht

lemma selectedFragments_ownerTotal {l : List ℝ} (S : Finset (Fin l.length))
    (red : Bool) (i : Fin l.length) :
    ownerTotal i ⟨selectedFragments S red, []⟩ = if i ∈ S then l[i] else 0 := by
  simpa [selectedFragments] using
    selectedFragments_ownerTotal_aux red S.toList S.nodup_toList i

lemma selectedFragments_length {l : List ℝ} (S : Finset (Fin l.length)) (red : Bool) :
    (selectedFragments S red).length = S.card := by
  simp [selectedFragments]

lemma selectedFragments_owner_bound {l : List ℝ}
    (S : Finset (Fin l.length)) (red : Bool) :
    ∀ x ∈ selectedFragments S red, x.owner < l.length := by
  intro x hx
  unfold selectedFragments at hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  exact i.2

/-- Bisect one fragment, represented as a duplicate matched pair owned twice by
that same input. -/
def bisectedFragment (x : OwnedFragment) : MatchedPair :=
  ⟨x.mass / 2, x.owner, x.owner⟩

/-- Bisect each input outside the selected set. -/
def neutralPairs {l : List ℝ} (S : Finset (Fin l.length)) : List MatchedPair :=
  (selectedFragments (Finset.univ \ S) false).map bisectedFragment

/-- Keep the first unmatched fragment and bisect all other unmatched fragments. -/
def finishSelected (st : MatchingState) : MatchingState :=
  match st.active with
  | [] => st
  | a :: as => ⟨[a], st.pairs ++ as.map bisectedFragment⟩

lemma finishSelected_active_length (st : MatchingState) :
    (finishSelected st).active.length ≤ 1 := by
  cases ha : st.active <;> simp [finishSelected, ha]

lemma finishSelected_active_pos {st : MatchingState}
    (hpos : ∀ x ∈ st.active, 0 < x.mass) :
    ∀ x ∈ (finishSelected st).active, 0 < x.mass := by
  cases ha : st.active with
  | nil => simpa [finishSelected, ha] using hpos
  | cons a as =>
      intro x hx
      simp only [finishSelected, ha, List.mem_singleton] at hx
      subst x
      exact hpos a (by simp [ha])

lemma finishSelected_pair_pos {st : MatchingState}
    (hactive : ∀ x ∈ st.active, 0 < x.mass)
    (hpairs : ∀ p ∈ st.pairs, 0 < p.mass) :
    ∀ p ∈ (finishSelected st).pairs, 0 < p.mass := by
  cases ha : st.active with
  | nil => simpa [finishSelected, ha] using hpairs
  | cons a as =>
      intro p hp
      simp only [finishSelected, ha, List.mem_append] at hp
      rcases hp with hp | hp
      · exact hpairs p hp
      · rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
        exact div_pos (hactive x (by simp [ha, hx])) (by norm_num)

lemma ownerTotal_bisected_map (as : List OwnedFragment) (i : ℕ) :
    ownerTotal i ⟨[], as.map bisectedFragment⟩ =
      ownerTotal i ⟨as, []⟩ := by
  induction as with
  | nil => simp [ownerTotal]
  | cons x xs ih =>
      unfold ownerTotal at ih ⊢
      simp only [List.map_cons, List.filter_nil, List.map_nil, List.sum_nil,
        List.filter_cons, List.sum_cons, zero_add, bisectedFragment] at ih ⊢
      by_cases hxi : x.owner = i <;> simp_all <;> linarith

lemma ownerTotal_finishSelected (st : MatchingState) (i : ℕ) :
    ownerTotal i (finishSelected st) = ownerTotal i st := by
  cases ha : st.active with
  | nil => simp [finishSelected, ha]
  | cons a as =>
      rw [show finishSelected st = ⟨[a], st.pairs ++ as.map bisectedFragment⟩ by
        rw [finishSelected, ha]]
      have hb := ownerTotal_bisected_map as i
      unfold ownerTotal at hb ⊢
      simp only [ha, List.filter_append, List.map_append, List.sum_append,
        List.filter_nil, List.map_nil, List.sum_nil, List.filter_cons,
        List.map_cons, List.sum_cons, zero_add] at hb ⊢
      by_cases hai : a.owner = i <;> simp_all <;> linarith

lemma ownerTotal_active_append (a b : List OwnedFragment) (i : ℕ) :
    ownerTotal i ⟨a ++ b, []⟩ =
      ownerTotal i ⟨a, []⟩ + ownerTotal i ⟨b, []⟩ := by
  simp [ownerTotal, List.filter_append, List.map_append, List.sum_append]

lemma ownerTotal_pairs_append (active : List OwnedFragment)
    (p q : List MatchedPair) (i : ℕ) :
    ownerTotal i ⟨active, p ++ q⟩ =
      ownerTotal i ⟨active, p⟩ + ownerTotal i ⟨[], q⟩ := by
  simp [ownerTotal, List.filter_append, List.map_append, List.sum_append]
  ring

lemma neutralPairs_ownerTotal {l : List ℝ} (S : Finset (Fin l.length))
    (i : Fin l.length) :
    ownerTotal i ⟨[], neutralPairs S⟩ = if i ∈ S then 0 else l[i] := by
  rw [neutralPairs, ownerTotal_bisected_map,
    selectedFragments_ownerTotal (Finset.univ \ S) false i]
  by_cases hi : i ∈ S <;> simp [hi]

lemma signedMass_append (a b : List OwnedFragment) :
    signedMass (a ++ b) = signedMass a + signedMass b := by
  simp [signedMass]

lemma signedMass_selectedFragments_true {l : List ℝ}
    (S : Finset (Fin l.length)) :
    signedMass (selectedFragments S true) = ∑ i ∈ S, l[i] := by
  simp [signedMass, selectedFragments]

lemma signedMass_selectedFragments_false {l : List ℝ}
    (S : Finset (Fin l.length)) :
    signedMass (selectedFragments S false) = -(∑ i ∈ S, l[i]) := by
  simp [signedMass, selectedFragments]

/-- Owner indices stay below an arbitrary ambient bound whenever the initial
owners do and owner totals are preserved. -/
lemma certificate_owners_bound {m : ℕ} {initial : List OwnedFragment}
    {out : MatchingState}
    (hownerInitial : ∀ x ∈ initial, x.owner < m)
    (houtpos : ∀ x ∈ out.active, 0 < x.mass)
    (hpairpos : ∀ p ∈ out.pairs, 0 < p.mass)
    (htotal : ∀ i, ownerTotal i out = ownerTotal i ⟨initial, []⟩) :
    (∀ p ∈ out.pairs, p.owner₁ < m) ∧
    (∀ p ∈ out.pairs, p.owner₂ < m) ∧
    (∀ x ∈ out.active, x.owner < m) := by
  have initial_zero (i : ℕ) (hi : m ≤ i) :
      ownerTotal i ⟨initial, []⟩ = 0 := by
    unfold ownerTotal
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add]
    have hempty : initial.filter (fun x => x.owner = i) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      rcases List.mem_filter.mp hx with ⟨hxin, hxeq⟩
      have heq : x.owner = i := of_decide_eq_true hxeq
      have hxlt := hownerInitial x hxin
      omega
    rw [hempty]
    simp
  have first : ∀ p ∈ out.pairs, p.owner₁ < m := by
    intro p hp
    by_contra h
    have hz := initial_zero p.owner₁ (by omega)
    have heq := htotal p.owner₁
    have hnonneg₂ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₂ = p.owner₁)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hnonnega : 0 ≤
        ((out.active.filter (fun x => x.owner = p.owner₁)).map OwnedFragment.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨x, hx, rfl⟩
      exact (houtpos x (List.mem_filter.mp hx).1).le
    have hp_le : p.mass ≤
        ((out.pairs.filter (fun q => q.owner₁ = p.owner₁)).map MatchedPair.mass).sum := by
      apply List.single_le_sum
      · intro z hzmem
        rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
        exact (hpairpos q (List.mem_filter.mp hq).1).le
      · apply List.mem_map.mpr
        exact ⟨p, List.mem_filter.mpr ⟨hp, by simp⟩, rfl⟩
    simp only [ownerTotal, List.filter_nil, List.map_nil, List.sum_nil, zero_add] at hz
    unfold ownerTotal at heq
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at heq
    rw [hz] at heq
    linarith [hpairpos p hp]
  have second : ∀ p ∈ out.pairs, p.owner₂ < m := by
    intro p hp
    by_contra h
    have hz := initial_zero p.owner₂ (by omega)
    have heq := htotal p.owner₂
    have hnonneg₁ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₁ = p.owner₂)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hnonnega : 0 ≤
        ((out.active.filter (fun x => x.owner = p.owner₂)).map OwnedFragment.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨x, hx, rfl⟩
      exact (houtpos x (List.mem_filter.mp hx).1).le
    have hp_le : p.mass ≤
        ((out.pairs.filter (fun q => q.owner₂ = p.owner₂)).map MatchedPair.mass).sum := by
      apply List.single_le_sum
      · intro z hzmem
        rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
        exact (hpairpos q (List.mem_filter.mp hq).1).le
      · apply List.mem_map.mpr
        exact ⟨p, List.mem_filter.mpr ⟨hp, by simp⟩, rfl⟩
    simp only [ownerTotal, List.filter_nil, List.map_nil, List.sum_nil, zero_add] at hz
    unfold ownerTotal at heq
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at heq
    rw [hz] at heq
    linarith [hpairpos p hp]
  have third : ∀ x ∈ out.active, x.owner < m := by
    intro x hx
    by_contra h
    have hz := initial_zero x.owner (by omega)
    have heq := htotal x.owner
    have hnonneg₁ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₁ = x.owner)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hnonneg₂ : 0 ≤
        ((out.pairs.filter (fun q => q.owner₂ = x.owner)).map MatchedPair.mass).sum := by
      apply List.sum_nonneg
      intro z hzmem
      rcases List.mem_map.mp hzmem with ⟨q, hq, rfl⟩
      exact (hpairpos q (List.mem_filter.mp hq).1).le
    have hx_le : x.mass ≤
        ((out.active.filter (fun a => a.owner = x.owner)).map OwnedFragment.mass).sum := by
      apply List.single_le_sum
      · intro z hzmem
        rcases List.mem_map.mp hzmem with ⟨a, ha, rfl⟩
        exact (houtpos a (List.mem_filter.mp ha).1).le
      · apply List.mem_map.mpr
        exact ⟨x, List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
    simp only [ownerTotal, List.filter_nil, List.map_nil, List.sum_nil, zero_add] at hz
    unfold ownerTotal at heq
    simp only [List.filter_nil, List.map_nil, List.sum_nil, zero_add] at heq
    rw [hz] at heq
    linarith [houtpos x hx]
  exact ⟨first, second, third⟩

lemma finishSelected_owner_bound {m : ℕ} {st : MatchingState}
    (hpairs₁ : ∀ p ∈ st.pairs, p.owner₁ < m)
    (hpairs₂ : ∀ p ∈ st.pairs, p.owner₂ < m)
    (hactive : ∀ x ∈ st.active, x.owner < m) :
    (∀ p ∈ (finishSelected st).pairs, p.owner₁ < m) ∧
    (∀ p ∈ (finishSelected st).pairs, p.owner₂ < m) ∧
    (∀ x ∈ (finishSelected st).active, x.owner < m) := by
  cases ha : st.active with
  | nil => simpa [finishSelected, ha] using And.intro hpairs₁ (And.intro hpairs₂ hactive)
  | cons a as =>
      have haown : a.owner < m := hactive a (by simp [ha])
      have hasown : ∀ x ∈ as, x.owner < m := by
        intro x hx
        exact hactive x (by simp [ha, hx])
      constructor
      · intro p hp
        simp only [finishSelected, ha, List.mem_append] at hp
        rcases hp with hp | hp
        · exact hpairs₁ p hp
        · rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
          exact hasown x hx
      · constructor
        · intro p hp
          simp only [finishSelected, ha, List.mem_append] at hp
          rcases hp with hp | hp
          · exact hpairs₂ p hp
          · rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
            exact hasown x hx
        · intro x hx
          simp only [finishSelected, ha, List.mem_singleton] at hx
          subst x
          exact haown

lemma neutralPairs_pos {l : List ℝ} (S : Finset (Fin l.length))
    (hpos : ∀ x ∈ l, 0 < x) :
    ∀ p ∈ neutralPairs S, 0 < p.mass := by
  intro p hp
  unfold neutralPairs at hp
  rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
  unfold bisectedFragment
  exact div_pos (selectedFragments_pos (Finset.univ \ S) false hpos x hx) (by norm_num)

lemma neutralPairs_owner_bound {l : List ℝ} (S : Finset (Fin l.length)) :
    (∀ p ∈ neutralPairs S, p.owner₁ < l.length) ∧
    (∀ p ∈ neutralPairs S, p.owner₂ < l.length) := by
  constructor <;> intro p hp <;>
    unfold neutralPairs at hp <;>
    rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩ <;>
    exact selectedFragments_owner_bound (Finset.univ \ S) false x hx

lemma neutralPairs_length {l : List ℝ} (S : Finset (Fin l.length)) :
    (neutralPairs S).length = l.length - S.card := by
  rw [neutralPairs, List.length_map, selectedFragments_length]
  rw [Finset.card_sdiff]
  simp

lemma finishSelected_length (st : MatchingState) :
    (finishSelected st).active.length + (finishSelected st).pairs.length =
      st.active.length + st.pairs.length := by
  cases ha : st.active <;> simp [finishSelected, ha, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

lemma activeMass_eq_abs_signedMass_of_monochromatic {s : List OwnedFragment}
    (hmono : Monochromatic s) (hpos : ∀ x ∈ s, 0 < x.mass) :
    activeMass s = |signedMass s| := by
  cases s with
  | nil => simp [activeMass, signedMass]
  | cons x xs =>
      symm
      apply abs_signedMass_eq_activeMass_of_same_color
      · intro y hy
        exact hmono y (by simp [hy]) x (by simp)
      · exact hpos x (by simp)
      · intro y hy
        exact hpos y (by simp [hy])

/-- The opposite-colour matching, followed by bisection of every unmatched
fragment except one, yields duplicate pairs plus one nonnegative residual.
The residual is the total unmatched mass and hence the absolute initial
imbalance. -/
lemma finish_opposite_matching (reds blues : List OwnedFragment)
    (hred : ∀ x ∈ reds, x.red = true)
    (hblue : ∀ x ∈ blues, x.red = false)
    (hredpos : ∀ x ∈ reds, 0 < x.mass)
    (hbluepos : ∀ x ∈ blues, 0 < x.mass) :
    ∃ out : MatchingState,
      out.active.length ≤ 1 ∧
      (∀ x ∈ out.active, 0 < x.mass) ∧
      (∀ p ∈ out.pairs, 0 < p.mass) ∧
      (∀ i, ownerTotal i out = ownerTotal i ⟨reds ++ blues, []⟩) ∧
      (out.active.map OwnedFragment.mass).sum ≤ |signedMass (reds ++ blues)| ∧
      out.active.length + out.pairs.length ≤ reds.length + blues.length ∧
      (reds ++ blues ≠ [] → out.pairs.length < reds.length + blues.length) := by
  obtain ⟨st, hactive, hpairs, hmono, howner, hsigned, hcount, hlt⟩ :=
    opposite_matching_certificate reds blues hred hblue hredpos hbluepos
  let out := finishSelected st
  refine ⟨out, finishSelected_active_length st, finishSelected_active_pos hactive,
    finishSelected_pair_pos hactive hpairs, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ownerTotal_finishSelected st i).trans (howner i)
  · unfold out finishSelected
    cases ha : st.active with
    | nil => simp [ha]
    | cons a as =>
        have hm : activeMass st.active = |signedMass st.active| :=
          activeMass_eq_abs_signedMass_of_monochromatic hmono hactive
        have hm' : a.mass + (as.map OwnedFragment.mass).sum =
            |signedMass st.active| := by
          rw [← hm]
          simp [activeMass, ha]
        rw [← hsigned]
        have hnonneg : 0 ≤ (as.map OwnedFragment.mass).sum := by
          apply List.sum_nonneg
          intro z hz
          rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
          exact (hactive x (by simp [ha, hx])).le
        have hm'' : a.mass + (as.map OwnedFragment.mass).sum =
            |signedMass (reds ++ blues)| := by
          rw [← hsigned]
          exact hm'
        simp only [ha, List.map_singleton, List.sum_singleton]
        have htarget : a.mass ≤ |signedMass st.active| := by
          linarith [hm']
        simpa only [ha] using htarget
  · rw [show out = finishSelected st by rfl, finishSelected_length]
    exact hcount
  · intro hne
    unfold out
    cases ha : st.active with
    | nil =>
        simpa [finishSelected, ha] using hlt hne
    | cons a as =>
        simp only [finishSelected, ha, List.length_append, List.length_map]
        have hc := hcount
        rw [ha] at hc
        simp only [List.length_cons] at hc
        omega

/-- Add the bisections of all neutral inputs to a finished selected state. -/
def addNeutralPairs {l : List ℝ} (S : Finset (Fin l.length))
    (st : MatchingState) : MatchingState :=
  ⟨st.active, st.pairs ++ neutralPairs S⟩

lemma addNeutralPairs_pair_pos {l : List ℝ} {S : Finset (Fin l.length)}
    {st : MatchingState} (hst : ∀ p ∈ st.pairs, 0 < p.mass)
    (hpos : ∀ x ∈ l, 0 < x) :
    ∀ p ∈ (addNeutralPairs S st).pairs, 0 < p.mass := by
  intro p hp
  simp only [addNeutralPairs, List.mem_append] at hp
  exact hp.elim (hst p) (neutralPairs_pos S hpos p)

lemma addNeutralPairs_ownerTotal {l : List ℝ} (S : Finset (Fin l.length))
    (st : MatchingState) (i : Fin l.length) :
    ownerTotal i (addNeutralPairs S st) =
      ownerTotal i st + if i ∈ S then 0 else l[i] := by
  unfold addNeutralPairs
  rw [ownerTotal_pairs_append]
  exact congrArg (ownerTotal i st + ·) (neutralPairs_ownerTotal S i)

lemma addNeutralPairs_length {l : List ℝ} (S : Finset (Fin l.length))
    (st : MatchingState) :
    (addNeutralPairs S st).active.length + (addNeutralPairs S st).pairs.length =
      st.active.length + st.pairs.length + (l.length - S.card) := by
  simp [addNeutralPairs, neutralPairs_length, Nat.add_assoc]

lemma addNeutralPairs_owner_bound {l : List ℝ} {S : Finset (Fin l.length)}
    {st : MatchingState}
    (hpairs₁ : ∀ p ∈ st.pairs, p.owner₁ < l.length)
    (hpairs₂ : ∀ p ∈ st.pairs, p.owner₂ < l.length)
    (hactive : ∀ x ∈ st.active, x.owner < l.length) :
    (∀ p ∈ (addNeutralPairs S st).pairs, p.owner₁ < l.length) ∧
    (∀ p ∈ (addNeutralPairs S st).pairs, p.owner₂ < l.length) ∧
    (∀ x ∈ (addNeutralPairs S st).active, x.owner < l.length) := by
  obtain ⟨hn₁, hn₂⟩ := neutralPairs_owner_bound S
  constructor
  · intro p hp
    simp only [addNeutralPairs, List.mem_append] at hp
    exact hp.elim (hpairs₁ p) (hn₁ p)
  · constructor
    · intro p hp
      simp only [addNeutralPairs, List.mem_append] at hp
      exact hp.elim (hpairs₂ p) (hn₂ p)
    · exact hactive

lemma selectedUnion_ownerTotal {l : List ℝ}
    (P Q : Finset (Fin l.length)) (hdisj : Disjoint P Q)
    (i : Fin l.length) :
    ownerTotal i ⟨selectedFragments P true ++ selectedFragments Q false, []⟩ =
      if i ∈ P ∪ Q then l[i] else 0 := by
  rw [ownerTotal_active_append, selectedFragments_ownerTotal,
    selectedFragments_ownerTotal]
  have hnotboth : ¬(i ∈ P ∧ i ∈ Q) := by
    intro h
    exact Finset.disjoint_left.mp hdisj h.1 h.2
  by_cases hiP : i ∈ P <;> by_cases hiQ : i ∈ Q <;> simp_all

theorem finite_list_response_sharp {l : List ℝ} {m : ℕ}
    (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x)
    (hsum : l.sum = 1) (hlen : l.length = m) :
    ∃ blocks : List (List ℝ), ∃ paired : List ℝ, ∃ r : ℝ,
      ∃ hblocks : blocks.length = m,
      (∀ i : Fin m, (blocks[i]'(by simpa [hblocks] using i.2)).sum =
        l[i]'(by simpa [hlen] using i.2)) ∧
      (∀ b ∈ blocks, ∀ x ∈ b, 0 < x) ∧
      blocks.flatten.length ≤ 2 * m - 1 ∧
      blocks.flatten.Perm
        ((paired.flatMap fun x => [x, x]) ++ if r = 0 then [] else [r]) ∧
      0 ≤ r ∧ r ≤ 1 / ((2 : ℝ) ^ m - 1) := by
  have hm : 0 < m := by
    rw [← hlen]
    exact List.length_pos_iff.mpr hne
  obtain ⟨P, Q, hPQ, hnonempty, himbalance⟩ := subset_sum_close hpos hsum
  have hdisj : Disjoint P Q := Finset.disjoint_iff_inter_eq_empty.mpr hPQ
  let reds := selectedFragments P true
  let blues := selectedFragments Q false
  have hred : ∀ x ∈ reds, x.red = true := selectedFragments_color P true
  have hblue : ∀ x ∈ blues, x.red = false := selectedFragments_color Q false
  have hredpos : ∀ x ∈ reds, 0 < x.mass := selectedFragments_pos P true hpos
  have hbluepos : ∀ x ∈ blues, 0 < x.mass := selectedFragments_pos Q false hpos
  obtain ⟨selected, hsellen, hselactivepos, hselpairpos, hselowner,
      hselresidual, hselcount, hselpairlt⟩ :=
    finish_opposite_matching reds blues hred hblue hredpos hbluepos
  let selectedSet := P ∪ Q
  let out := addNeutralPairs selectedSet selected
  let blocks := blocksOfState m out
  let paired := out.pairs.map MatchedPair.mass
  let r := (out.active.map OwnedFragment.mass).sum
  have hselectedne : reds ++ blues ≠ [] := by
    rw [List.ne_nil_iff_length_pos]
    simp only [List.length_append, reds, blues, selectedFragments_length]
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnonempty)
  have hinitialowner : ∀ x ∈ reds ++ blues, x.owner < l.length := by
    intro x hx
    rw [List.mem_append] at hx
    exact hx.elim (selectedFragments_owner_bound P true x)
      (selectedFragments_owner_bound Q false x)
  obtain ⟨hselown₁, hselown₂, hselowna⟩ :=
    certificate_owners_bound hinitialowner hselactivepos hselpairpos hselowner
  obtain ⟨houtown₁, houtown₂, houtowna⟩ :=
    addNeutralPairs_owner_bound hselown₁ hselown₂ hselowna
  have houtpairpos : ∀ p ∈ out.pairs, 0 < p.mass :=
    addNeutralPairs_pair_pos hselpairpos hpos
  have houtactivepos : ∀ x ∈ out.active, 0 < x.mass := by
    simpa [out, addNeutralPairs] using hselactivepos
  have hblocklen : blocks.length = m := blocksOfState_length m out
  have houtowner : ∀ i : Fin l.length, ownerTotal i out = l[i] := by
    intro i
    rw [show out = addNeutralPairs selectedSet selected by rfl,
      addNeutralPairs_ownerTotal, hselowner]
    rw [selectedUnion_ownerTotal P Q hdisj]
    unfold selectedSet at *
    by_cases hi : i ∈ P ∪ Q <;> simp [hi]
  have hblocksum : ∀ i : Fin m,
      (blocks[i]'(by simpa [hblocklen] using i.2)).sum =
        l[i]'(by simpa [hlen] using i.2) := by
    intro i
    unfold blocks
    rw [blocksOfState_sum]
    let j : Fin l.length := ⟨i, by simpa [hlen] using i.2⟩
    exact houtowner j
  have hblockpos : ∀ b ∈ blocks, ∀ x ∈ b, 0 < x :=
    blocksOfState_pos houtactivepos houtpairpos
  have hperm0 : blocks.flatten.Perm ((ownedPieces out).map Prod.snd) := by
    apply blocksOfState_flatten_perm
    · simpa [hlen] using houtown₁
    · simpa [hlen] using houtown₂
    · simpa [hlen] using houtowna
  have hactivecases : out.active = [] ∨ ∃ a, out.active = [a] := by
    have h : out.active.length ≤ 1 := by
      simpa [out, addNeutralPairs] using hsellen
    cases ha : out.active with
    | nil => exact Or.inl rfl
    | cons a as =>
        right
        have has : as = [] := by
          rw [ha] at h
          simp only [List.length_cons] at h
          exact List.length_eq_zero_iff.mp (by omega)
        subst as
        exact ⟨a, rfl⟩
  have hshape : blocks.flatten.Perm
      ((paired.flatMap fun x => [x, x]) ++ if r = 0 then [] else [r]) := by
    have hperm := hperm0
    unfold ownedPieces at hperm
    unfold paired r
    simp only [List.map_append, List.map_flatMap] at hperm
    have hpairsmap :
        (out.pairs.flatMap fun p => ([(p.owner₁, p.mass), (p.owner₂, p.mass)].map
          Prod.snd)) =
        (out.pairs.map MatchedPair.mass).flatMap (fun x => [x, x]) := by
      simp [List.flatMap_map]
    rw [hpairsmap] at hperm
    rcases hactivecases with ha | ⟨a, ha⟩
    · simpa [ha] using hperm
    · have hapos : 0 < a.mass := houtactivepos a (by simp [ha])
      simpa [ha, hapos.ne'] using hperm
  have hblockbudget : blocks.flatten.length ≤ 2 * m - 1 := by
    rw [hshape.length_eq]
    by_cases hr0 : r = 0
    · simp only [hr0, if_true, List.append_nil]
      have hpairslen :
          (paired.flatMap fun x => [x, x]).length = 2 * paired.length := by
        induction paired with
        | nil => simp
        | cons p ps ih => simp [ih, Nat.mul_succ]
      rw [hpairslen]
      have hselcard : reds.length + blues.length = selectedSet.card := by
        simp only [reds, blues, selectedFragments_length, selectedSet]
        rw [Finset.card_union_of_disjoint hdisj]
      have hcardle : selectedSet.card ≤ l.length := by
        rw [show selectedSet = P ∪ Q by rfl]
        exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
      have hselectedbound :
          selected.active.length + selected.pairs.length ≤ selectedSet.card := by
        rw [← hselcard]
        exact hselcount
      have hpairselected : selected.pairs.length < selectedSet.card := by
        rw [← hselcard]
        exact hselpairlt hselectedne
      have hpairlen : paired.length =
          selected.pairs.length + (l.length - selectedSet.card) := by
        simp [paired, out, addNeutralPairs, neutralPairs_length]
      rw [hpairlen, ← hlen]
      omega
    · simp only [hr0, if_false, List.length_append, List.length_singleton,
        List.length_flatMap]
      have hpairslen :
          (paired.map fun _ => 2).sum = 2 * paired.length := by
        simp [two_mul, Nat.mul_comm]
      change (paired.map fun _ => 2).sum + 1 ≤ 2 * m - 1
      rw [hpairslen]
      have hselcard : reds.length + blues.length = selectedSet.card := by
        simp only [reds, blues, selectedFragments_length, selectedSet]
        rw [Finset.card_union_of_disjoint hdisj]
      have hcardle : selectedSet.card ≤ l.length := by
        rw [show selectedSet = P ∪ Q by rfl]
        exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
      have hselectedbound :
          selected.active.length + selected.pairs.length ≤ selectedSet.card := by
        rw [← hselcard]
        exact hselcount
      have hpairlen : paired.length =
          selected.pairs.length + (l.length - selectedSet.card) := by
        simp [paired, out, addNeutralPairs, neutralPairs_length]
      have hactiveone : selected.active.length = 1 := by
        have hrselactive : r = (selected.active.map OwnedFragment.mass).sum := rfl
        cases ha : selected.active with
        | nil =>
            have : r = 0 := by simp [r, out, addNeutralPairs, ha]
            exact (hr0 this).elim
        | cons a as =>
            have hlenas : as = [] := by
              rw [ha] at hsellen
              simp only [List.length_cons] at hsellen
              exact List.length_eq_zero_iff.mp (by omega)
            simp [ha, hlenas]
      rw [hpairlen, ← hlen]
      omega
  have hrnonneg : 0 ≤ r := by
    unfold r
    apply List.sum_nonneg
    intro z hz
    rcases List.mem_map.mp hz with ⟨a, ha, rfl⟩
    exact (houtactivepos a ha).le
  have hrbound : r ≤ 1 / ((2 : ℝ) ^ m - 1) := by
    have hsigned : signedMass (reds ++ blues) =
        (∑ i ∈ P, l[i]) - ∑ i ∈ Q, l[i] := by
      rw [signedMass_append]
      change signedMass reds + signedMass blues = _
      rw [show reds = selectedFragments P true by rfl,
        show blues = selectedFragments Q false by rfl,
        signedMass_selectedFragments_true, signedMass_selectedFragments_false]
      ring
    have hrsel : r ≤ |signedMass (reds ++ blues)| := by
      unfold r out addNeutralPairs
      exact hselresidual
    rw [hsigned] at hrsel
    have himbalance' : |(∑ i ∈ P, l[i]) - ∑ i ∈ Q, l[i]| ≤
        1 / ((2 : ℝ) ^ m - 1) := by
      simpa only [hlen] using himbalance
    exact hrsel.trans himbalance'
  refine ⟨blocks, paired, r, hblocklen, hblocksum, hblockpos,
    hblockbudget, hshape, hrnonneg, hrbound⟩


/-- All prefix points, including the initial point `0` and the total sum. -/
def prefixPoints (f : List ℝ) : List ℝ :=
  f.scanl (· + ·) 0

/-- The proper, nonempty prefix sums of `f`, excluding its total sum. -/
def interiorPrefixSums (f : List ℝ) : List ℝ :=
  (prefixPoints f).dropLast.tail

/-- All marks obtained from proper, nonempty prefix sums of `f`. -/
def allMarks (f : List ℝ) : Finset ℝ :=
  (interiorPrefixSums f).toFinset

/-- The marks not already present in `A`. -/
def completionMarks (A : Finset ℝ) (f : List ℝ) : Finset ℝ :=
  allMarks f \ A


lemma zipWith_adjacent_sub_pos : ∀ (xs : List ℝ), xs.Pairwise (· < ·) →
    ∀ x ∈ List.zipWith (fun a b : ℝ => b - a) xs xs.tail, 0 < x := by
  intro xs hxs x hx
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      cases xs with
      | nil => simp at hx
      | cons b ys =>
          simp only [List.tail_cons, List.zipWith, List.mem_cons] at hx
          rw [List.pairwise_cons] at hxs
          rcases hx with rfl | hx
          · exact sub_pos.mpr (hxs.1 b (by simp))
          · exact ih hxs.2 hx

lemma finset_sort_pairwise_lt (S : Finset ℝ) :
    (S.sort (· ≤ ·)).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hle := S.pairwise_sort (· ≤ ·)
  rw [List.pairwise_iff_getElem] at hle
  exact lt_of_le_of_ne (hle i j hi hj hij) (by
    intro heq
    have hidx := (S.sort_nodup (· ≤ ·)).getElem_inj_iff.mp heq
    omega)

lemma pieceLengths_pos {S : Finset ℝ}
    (hS : (↑S : Set ℝ) ⊆ Set.Ioo 0 1) :
    ∀ x ∈ pieceLengths S, 0 < x := by
  let l : List ℝ := (0 : ℝ) :: S.sort (· ≤ ·) ++ [1]
  have hsorted : l.Pairwise (· < ·) := by
    dsimp [l]
    rw [List.pairwise_cons]
    constructor
    · intro y hy
      simp only [List.mem_append, Finset.mem_sort, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact (hS hy).1
      · norm_num
    · rw [List.pairwise_append]
      refine ⟨finset_sort_pairwise_lt S, by simp, ?_⟩
      intro y hy z hz
      simp only [Finset.mem_sort] at hy
      simp only [List.mem_singleton] at hz
      subst z
      exact (hS hy).2
  intro x hx
  apply zipWith_adjacent_sub_pos l hsorted x
  simpa only [pieceLengths, l] using hx

lemma scanl_add_pairwise_lt {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) (a : ℝ) :
    (f.scanl (· + ·) a).Pairwise (· < ·) := by
  induction f generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.scanl_cons, List.pairwise_cons]
      have htail := ih (fun y hy => hpos y (by simp [hy])) (a + x)
      constructor
      · intro y hy
        cases xs with
        | nil =>
            simp at hy
            subst y
            linarith [hpos x (by simp)]
        | cons z zs =>
            rw [List.scanl_cons] at hy
            rw [List.scanl_cons, List.pairwise_cons] at htail
            rcases List.mem_cons.mp hy with rfl | hy
            · linarith [hpos x (by simp)]
            · linarith [hpos x (by simp), htail.1 y hy]
      · exact htail

lemma prefixPoints_pairwise_lt {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) :
    (prefixPoints f).Pairwise (· < ·) :=
  scanl_add_pairwise_lt hpos 0

lemma interiorPrefixSums_pairwise_lt {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) :
    (interiorPrefixSums f).Pairwise (· < ·) := by
  rw [interiorPrefixSums, List.dropLast_eq_take]
  exact (prefixPoints_pairwise_lt hpos).take.tail

lemma interiorPrefixSums_nodup {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) :
    (interiorPrefixSums f).Nodup :=
  (interiorPrefixSums_pairwise_lt hpos).nodup

/-- Sorting `allMarks f` recovers exactly the interior prefix sums, in order. -/
lemma allMarks_sort {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) :
    (allMarks f).sort (· ≤ ·) = interiorPrefixSums f := by
  apply (List.toFinset_sort (· ≤ ·) (interiorPrefixSums_nodup hpos)).2
  exact (interiorPrefixSums_pairwise_lt hpos).imp le_of_lt

lemma zipWith_sub_scanl (a : ℝ) (f : List ℝ) :
    List.zipWith (fun x y : ℝ => y - x)
      (f.scanl (· + ·) a) (f.scanl (· + ·) a).tail = f := by
  induction f generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.scanl_cons]
      simp only [List.tail_cons]
      have hstep :
          List.zipWith (fun u v : ℝ => v - u)
            (a :: xs.scanl (· + ·) (a + x)) (xs.scanl (· + ·) (a + x)) =
          x :: List.zipWith (fun u v : ℝ => v - u)
            (xs.scanl (· + ·) (a + x)) (xs.scanl (· + ·) (a + x)).tail := by
        cases xs <;> simp
      rw [hstep, ih]

lemma cons_tail_eq_self_of_head {α : Type*} {l : List α} {a : α}
    (hl : l ≠ []) (hhead : l.head hl = a) : a :: l.tail = l := by
  cases l with
  | nil => contradiction
  | cons b bs => simp_all

lemma prefixPoints_eq_boundaries {f : List ℝ} (hsum : f.sum = 1) :
    (0 : ℝ) :: interiorPrefixSums f ++ [1] = prefixPoints f := by
  have hlast : (prefixPoints f).getLast (by simp [prefixPoints]) = 1 := by
    unfold prefixPoints
    rw [List.getLast_scanl, ← List.sum_eq_foldl, hsum]
  have hdecomp := List.dropLast_append_getLast (l := prefixPoints f)
    (by simp [prefixPoints])
  rw [hlast] at hdecomp
  rw [← hdecomp]
  unfold interiorPrefixSums
  congr 1
  have hfne : f ≠ [] := by
    intro hf
    subst f
    simp at hsum
  have hdrop : (prefixPoints f).dropLast ≠ [] := by
    have hlen : (prefixPoints f).dropLast.length = f.length := by
      simp [prefixPoints]
    intro hempty
    rw [hempty] at hlen
    simp at hlen
    exact hfne (List.length_eq_zero_iff.mp hlen.symm)
  have hhead : (prefixPoints f).head (by simp [prefixPoints]) = 0 := by
    unfold prefixPoints
    cases f <;> simp only [List.scanl_nil, List.scanl_cons, List.head_cons]
  apply cons_tail_eq_self_of_head hdrop
  exact (List.head_dropLast hdrop).trans hhead

/-- Cutting at every interior prefix sum recovers the original positive list. -/
lemma pieceLengths_allMarks {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) (hsum : f.sum = 1) :
    pieceLengths (allMarks f) = f := by
  rw [pieceLengths, allMarks_sort hpos]
  rw [prefixPoints_eq_boundaries hsum]
  exact zipWith_sub_scanl 0 f

lemma allMarks_card {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) :
    (allMarks f).card = f.length - 1 := by
  rw [allMarks, List.toFinset_card_of_nodup (interiorPrefixSums_nodup hpos)]
  simp [interiorPrefixSums, prefixPoints]

lemma interior_mem_exists_sum_take {f : List ℝ} {x : ℝ}
    (hx : x ∈ interiorPrefixSums f) :
    ∃ i, 0 < i ∧ i < f.length ∧ x = (f.take i).sum := by
  rw [List.mem_iff_getElem] at hx
  rcases hx with ⟨j, hj, heq⟩
  have hlen : (interiorPrefixSums f).length = f.length - 1 := by
    simp [interiorPrefixSums, prefixPoints]
  have hij : j + 1 < f.length := by
    rw [hlen] at hj
    omega
  refine ⟨j + 1, by omega, hij, ?_⟩
  have hpidx : j + 1 < (prefixPoints f).length := by
    simp [prefixPoints]
    omega
  have heq' : (prefixPoints f)[j + 1] = x := by
    rw [← heq]
    unfold interiorPrefixSums
    rw [List.getElem_tail, List.getElem_dropLast]
  rw [← heq']
  unfold prefixPoints
  rw [List.getElem_scanl, ← List.sum_eq_foldl]

lemma allMarks_in_interval {f : List ℝ}
    (hpos : ∀ x ∈ f, 0 < x) (hsum : f.sum = 1) :
    (↑(allMarks f) : Set ℝ) ⊆ Set.Ioo 0 1 := by
  intro x hx
  rw [Finset.mem_coe, allMarks, List.mem_toFinset] at hx
  rcases interior_mem_exists_sum_take hx with ⟨i, hi0, hif, rfl⟩
  constructor
  · exact List.sum_pos _
      (fun y hy => hpos y (List.take_subset i f hy))
      (by
        rw [ne_eq, List.take_eq_nil_iff, not_or]
        exact ⟨Nat.ne_of_gt hi0, by
          intro hf
          subst f
          simp at hif⟩)
  · have hdropne : f.drop i ≠ [] := by
      rw [ne_eq, List.drop_eq_nil_iff, not_le]
      exact hif
    have hdropPos : 0 < (f.drop i).sum :=
      List.sum_pos _ (fun y hy => hpos y (List.drop_subset i f hy)) hdropne
    rw [← hsum]
    linarith [List.sum_take_add_sum_drop f i]

lemma scanl_add_zipWith_sub (a : ℝ) (l : List ℝ) :
    (List.zipWith (fun x y : ℝ => y - x) (a :: l) l).scanl (· + ·) a = a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b bs ih =>
      rw [List.zipWith, List.scanl_cons]
      have hab : a + (b - a) = b := by ring
      rw [hab, ih]

lemma prefixPoints_pieceLengths (A : Finset ℝ) :
    prefixPoints (pieceLengths A) = (0 : ℝ) :: A.sort (· ≤ ·) ++ [1] := by
  unfold prefixPoints pieceLengths
  exact scanl_add_zipWith_sub 0 (A.sort (· ≤ ·) ++ [1])

lemma allMarks_pieceLengths (A : Finset ℝ) :
    allMarks (pieceLengths A) = A := by
  unfold allMarks interiorPrefixSums
  rw [prefixPoints_pieceLengths]
  change ((0 : ℝ) :: (A.sort (· ≤ ·) ++ [1])).dropLast.tail.toFinset = A
  have hne : A.sort (· ≤ ·) ++ [(1 : ℝ)] ≠ [] := by
    intro h
    have := congrArg List.getLast? h
    simp at this
  rw [List.dropLast_cons_of_ne_nil hne]
  simp

lemma sum_map_sum_take_blocks (blocks : List (List ℝ)) (i : ℕ) :
    ((blocks.map List.sum).take i).sum = ((blocks.take i).flatten).sum := by
  rw [← List.map_take, ← List.sum_flatten]

lemma blockPrefix_is_flatten_prefix (blocks : List (List ℝ)) (i : ℕ) :
    ((blocks.map List.sum).take i).sum =
      (blocks.flatten.take ((blocks.map List.length).take i |>.sum)).sum := by
  rw [sum_map_sum_take_blocks, List.take_sum_flatten]

lemma sum_take_mem_allMarks {f : List ℝ} {i : ℕ}
    (hi0 : 0 < i) (hif : i < f.length) :
    (f.take i).sum ∈ allMarks f := by
  rw [allMarks, List.mem_toFinset, List.mem_iff_getElem]
  have hile : i ≤ f.length := Nat.le_of_lt hif
  have hi1 : i - 1 < (interiorPrefixSums f).length := by
    have hsimp : (interiorPrefixSums f).length = f.length - 1 := by
      simp [interiorPrefixSums, prefixPoints]
    rw [hsimp]
    omega
  refine ⟨i - 1, hi1, ?_⟩
  have hpidx : i < (prefixPoints f).length := by
    simp [prefixPoints]
    exact hile
  have heq : (prefixPoints f)[i] = (f.take i).sum := by
    unfold prefixPoints
    rw [List.getElem_scanl, ← List.sum_eq_foldl]
  have heq' : (interiorPrefixSums f)[i - 1] = (prefixPoints f)[i - 1 + 1] := by
    unfold interiorPrefixSums
    rw [List.getElem_tail, List.getElem_dropLast]
  have hidx : i - 1 + 1 = i := Nat.sub_add_cancel hi0
  calc
    (interiorPrefixSums f)[i - 1] = (prefixPoints f)[i - 1 + 1] := heq'
    _ = (prefixPoints f)[i] := getElem_congr rfl hidx _
    _ = (f.take i).sum := heq

lemma blockBoundary_mem_allMarks {blocks : List (List ℝ)}
    (hblocks : ∀ l ∈ blocks, l ≠ [])
    {i : ℕ} (hi0 : 0 < i) (hib : i < blocks.length) :
    ((blocks.map List.sum).take i).sum ∈ allMarks blocks.flatten := by
  rw [blockPrefix_is_flatten_prefix]
  apply sum_take_mem_allMarks
  · have hfirst : blocks[0] ∈ blocks := List.getElem_mem (by omega)
    have hfirstne := hblocks blocks[0] hfirst
    have hfirstpos : 0 < blocks[0].length := List.ne_nil_iff_length_pos.mp hfirstne
    have hmem : blocks[0].length ∈ (blocks.map List.length).take i := by
      rw [List.mem_iff_getElem]
      refine ⟨0, ?_, ?_⟩
      · simp [List.length_take]
        omega
      · rw [List.getElem_take, List.getElem_map]
    exact lt_of_lt_of_le hfirstpos (List.le_sum_of_mem hmem)
  · rw [List.length_flatten]
    have htail : blocks[i].length ∈ (blocks.map List.length).drop i := by
      rw [List.mem_iff_getElem]
      refine ⟨0, ?_, ?_⟩
      · simp
        omega
      · rw [List.getElem_drop, List.getElem_map]
        simp
    have htailpos : 0 < blocks[i].length :=
      List.ne_nil_iff_length_pos.mp (hblocks blocks[i] (List.getElem_mem hib))
    have hsumtail : 0 < ((blocks.map List.length).drop i).sum :=
      lt_of_lt_of_le htailpos (List.le_sum_of_mem htail)
    have hsum := List.sum_take_add_sum_drop (blocks.map List.length) i
    omega

/-- Ordered nonempty blocks refine every mark of the coarser partition. -/
lemma block_refinement_contains_marks {A : Finset ℝ} {f : List ℝ}
    {blocks : List (List ℝ)}
    (hpieces : pieceLengths A = blocks.map List.sum)
    (hflatten : f = blocks.flatten)
    (hblocks : ∀ l ∈ blocks, l ≠ []) :
    A ⊆ allMarks f := by
  intro x hx
  have hxcoarse : x ∈ allMarks (pieceLengths A) := by
    rw [allMarks_pieceLengths]
    exact hx
  rw [hpieces, allMarks, List.mem_toFinset] at hxcoarse
  rcases interior_mem_exists_sum_take hxcoarse with ⟨i, hi0, hib, hxi⟩
  rw [hflatten, hxi]
  exact blockBoundary_mem_allMarks hblocks hi0 (by simpa using hib)

lemma completionMarks_disjoint {A : Finset ℝ} {f : List ℝ} :
    Disjoint A (completionMarks A f) :=
  Finset.disjoint_sdiff

lemma completionMarks_union {A : Finset ℝ} {f : List ℝ}
    (hA : A ⊆ allMarks f) :
    A ∪ completionMarks A f = allMarks f :=
  Finset.union_sdiff_of_subset hA

lemma completionMarks_card {A : Finset ℝ} {f : List ℝ}
    (hA : A ⊆ allMarks f) (hpos : ∀ x ∈ f, 0 < x) :
    (completionMarks A f).card = f.length - 1 - A.card := by
  unfold completionMarks
  rw [Finset.card_sdiff_of_subset hA, allMarks_card hpos]

lemma completionMarks_admissible {A : Finset ℝ} {f : List ℝ}
    (hA : A ⊆ allMarks f)
    (hpos : ∀ x ∈ f, 0 < x) (hsum : f.sum = 1)
    {n : ℕ} (hcard : f.length - 1 - A.card ≤ n) :
    AdmissibleMark n (completionMarks A f) := by
  constructor
  · intro x hx
    apply allMarks_in_interval hpos hsum
    exact Finset.sdiff_subset hx
  · rw [completionMarks_card hA hpos]
    exact hcard

lemma completionMarks_card_le_self_of_length {A : Finset ℝ} {f : List ℝ}
    (hA : A ⊆ allMarks f) (hpos : ∀ x ∈ f, 0 < x)
    (hlen : f.length ≤ 2 * (A.card + 1) - 1) :
    (completionMarks A f).card ≤ A.card := by
  rw [completionMarks_card hA hpos]
  omega

lemma pieceLengths_refinement_completion {A : Finset ℝ} {f : List ℝ}
    (hA : A ⊆ allMarks f)
    (hpos : ∀ x ∈ f, 0 < x) (hsum : f.sum = 1) :
    pieceLengths (A ∪ completionMarks A f) = f := by
  rw [completionMarks_union hA]
  exact pieceLengths_allMarks hpos hsum

/--
The generic bridge from an ordered block refinement to a legal completion.
No existence of `blocks` is asserted: the blocks and their two structural identities are inputs.
-/
theorem orderedBlocks_completion {n : ℕ} {A : Finset ℝ} {f : List ℝ}
    {blocks : List (List ℝ)}
    (hAadm : AdmissibleMark n A)
    (hpos : ∀ x ∈ f, 0 < x)
    (hpieces : pieceLengths A = blocks.map List.sum)
    (hflatten : f = blocks.flatten)
    (hcard : f.length - 1 - A.card ≤ n) :
    let B := completionMarks A f
    A ⊆ allMarks f ∧
      AdmissibleMark n B ∧
      Disjoint A B ∧
      A ∪ B = allMarks f ∧
      pieceLengths (A ∪ B) = f ∧
      B.card = f.length - 1 - A.card := by
  dsimp
  have hblocks : ∀ l ∈ blocks, l ≠ [] := by
    intro l hl hnil
    have hmem : l.sum ∈ blocks.map List.sum :=
      List.mem_map.mpr ⟨l, hl, rfl⟩
    rw [← hpieces] at hmem
    have hlt := pieceLengths_pos hAadm.1 l.sum hmem
    subst l
    simp at hlt
  have hA : A ⊆ allMarks f :=
    block_refinement_contains_marks hpieces hflatten hblocks
  have hsum : f.sum = 1 := by
    rw [hflatten, List.sum_flatten, ← hpieces]
    exact pieceLengths_sum A
  have hBcard := completionMarks_card hA hpos
  refine ⟨hA, completionMarks_admissible hA hpos hsum hcard,
    completionMarks_disjoint, completionMarks_union hA, ?_, hBcard⟩
  exact pieceLengths_refinement_completion hA hpos hsum

/-- The cardinality hypothesis used in the intended two-player response bound. -/
theorem orderedBlocks_completion_of_length {n : ℕ} {A : Finset ℝ} {f : List ℝ}
    {blocks : List (List ℝ)}
    (hAadm : AdmissibleMark n A)
    (hpos : ∀ x ∈ f, 0 < x)
    (hpieces : pieceLengths A = blocks.map List.sum)
    (hflatten : f = blocks.flatten)
    (hlen : f.length ≤ 2 * (A.card + 1) - 1) :
    let B := completionMarks A f
    A ⊆ allMarks f ∧
      AdmissibleMark n B ∧
      Disjoint A B ∧
      A ∪ B = allMarks f ∧
      pieceLengths (A ∪ B) = f ∧
      B.card = f.length - 1 - A.card := by
  have hAcard : A.card ≤ n := hAadm.2
  apply orderedBlocks_completion hAadm hpos hpieces hflatten
  omega


/-- Sorting a multiset in which every entry occurs in a duplicate pair gives
zero alternating sum. -/
lemma altSum_mergeSort_duplicate_pairs (l : List ℝ) :
    altSum ((l.flatMap fun x => [x, x]).mergeSort (· ≥ ·)) = 0 := by
  let s := l.mergeSort (· ≥ ·)
  have hs : s.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) l
  have hpairwise_aux : ∀ t : List ℝ, t.Pairwise (· ≥ ·) →
      (t.flatMap fun x => [x, x]).Pairwise (· ≥ ·) := by
    intro t ht
    induction t with
    | nil => simp
    | cons x t ih =>
        rw [List.pairwise_cons] at ht
        simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        rw [List.pairwise_cons, List.pairwise_cons]
        constructor
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact le_rfl
          · rcases List.mem_flatMap.mp hy with ⟨z, hz, hy⟩
            rcases List.mem_cons.mp hy with rfl | hy
            · exact ht.1 _ hz
            · rw [List.mem_singleton] at hy
              subst y
              exact ht.1 z hz
        · constructor
          · intro y hy
            rcases List.mem_flatMap.mp hy with ⟨z, hz, hy⟩
            rcases List.mem_cons.mp hy with rfl | hy
            · exact ht.1 _ hz
            · rw [List.mem_singleton] at hy
              subst y
              exact ht.1 z hz
          · exact ih ht.2
  have hpairwise : (s.flatMap fun x => [x, x]).Pairwise (· ≥ ·) :=
    hpairwise_aux s hs
  have hperm : (s.flatMap fun x => [x, x]).Perm (l.flatMap fun x => [x, x]) :=
    (List.mergeSort_perm l (· ≥ ·)).flatMap (fun _ _ => List.Perm.refl _)
  have hsorted : (l.flatMap fun x => [x, x]).mergeSort (· ≥ ·) =
      s.flatMap fun x => [x, x] := by
    apply List.Perm.eq_of_pairwise'
      (List.pairwise_mergeSort' (· ≥ ·) _) hpairwise
    exact (List.mergeSort_perm _ _).trans hperm.symm
  rw [hsorted]
  induction s with
  | nil => simp [altSum]
  | cons x s ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, altSum]
      linarith

/-- Duplicate pairs, together with an optional residual, have alternating sum
exactly equal to that residual after sorting. -/
lemma altSum_of_duplicate_optional_residual {xs paired : List ℝ} {r : ℝ}
    (hshape : xs.Perm
      ((paired.flatMap fun x => [x, x]) ++ if r = 0 then [] else [r])) :
    altSum (xs.mergeSort (· ≥ ·)) = r := by
  by_cases hr : r = 0
  · subst r
    simp only [if_true, List.append_nil] at hshape
    have heq : xs.mergeSort (· ≥ ·) =
        (paired.flatMap fun x => [x, x]).mergeSort (· ≥ ·) := by
      apply List.Perm.eq_of_pairwise'
        (List.pairwise_mergeSort' (· ≥ ·) _)
        (List.pairwise_mergeSort' (· ≥ ·) _)
      exact (List.mergeSort_perm _ _).trans
        (hshape.trans (List.mergeSort_perm _ _).symm)
    rw [heq, altSum_mergeSort_duplicate_pairs]
  · simp only [hr, if_false] at hshape
    have hdoubled :
        ((paired.map fun x : ℝ => 2 * x).flatMap fun y => [y / 2, y / 2]) =
          paired.flatMap fun x => [x, x] := by
      clear hshape
      induction paired with
      | nil => rfl
      | cons x xs ih =>
          rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]
          congr 1
          norm_num
    have heq : xs.mergeSort (· ≥ ·) =
        ((((paired.map fun x : ℝ => 2 * x).flatMap fun y => [y / 2, y / 2]) ++
          [r]).mergeSort (· ≥ ·)) := by
      apply List.Perm.eq_of_pairwise'
        (List.pairwise_mergeSort' (· ≥ ·) _)
        (List.pairwise_mergeSort' (· ≥ ·) _)
      rw [hdoubled]
      exact (List.mergeSort_perm _ _).trans
        (hshape.trans (List.mergeSort_perm _ _).symm)
    rw [heq, residual_response_alt]

/-- The upper-bound half of the game value. -/
lemma V_le_answer (n : ℕ) (hn : 0 < n) : V n ≤ answer n := by
  letI := admissibleSubtypeNonempty n
  have hhalf : (1 : ℝ) / 2 ≤ answer n := by
    unfold answer
    rw [le_div_iff₀ (answer_den_pos n)]
    rw [pow_succ]
    have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    nlinarith
  have hformula :
      ((1 : ℝ) + 1 / ((2 : ℝ) ^ (n + 1) - 1)) / 2 = answer n := by
    unfold answer
    field_simp [ne_of_gt (answer_den_pos n)]
    rw [pow_succ]
    ring
  unfold V
  apply ciSup_le
  intro A
  let l := pieceLengths A.1
  have hlpos : ∀ x ∈ l, 0 < x := pieceLengths_pos A.2.1
  have hlsum : l.sum = 1 := pieceLengths_sum A.1
  have hllen : l.length = A.1.card + 1 := pieceLengths_length A.1
  have hlne : l ≠ [] := by
    rw [List.ne_nil_iff_length_pos, hllen]
    omega
  have hBddBelow : BddBelow (Set.range fun B :
      {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1) := by
    refine ⟨(1 : ℝ) / 2, ?_⟩
    rintro _ ⟨B, rfl⟩
    exact (L_bounds_of_admissible A.2 B.2.1).1
  by_cases hfull : A.1.card = n
  · obtain ⟨blocks, paired, r, hblocks, hblocksum, hblockpos,
        hbudget, hshape, hrnonneg, hrbound⟩ :=
      finite_list_response_sharp (l := l) (m := A.1.card + 1)
        hlne hlpos hlsum hllen
    have hpieces : l = blocks.map List.sum := by
      apply List.ext_get
      · simpa [hllen, hblocks]
      · intro i hi hi'
        simp only [List.get_eq_getElem, List.getElem_map]
        exact (hblocksum ⟨i, by simpa [hllen] using hi⟩).symm
    let f := blocks.flatten
    have hfpos : ∀ x ∈ f, 0 < x := by
      intro x hx
      rcases List.mem_flatten.mp hx with ⟨b, hb, hxb⟩
      exact hblockpos b hb x hxb
    have hcompletion := orderedBlocks_completion_of_length
      (n := n) (A := A.1) (f := f) (blocks := blocks)
      A.2 hfpos hpieces rfl hbudget
    dsimp only at hcompletion
    let B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨completionMarks A.1 f, hcompletion.2.1, hcompletion.2.2.1⟩
    have halt : altSum (f.mergeSort (· ≥ ·)) = r := by
      apply altSum_of_duplicate_optional_residual
      simpa [f] using hshape
    have hrboundn : r ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1) := by
      simpa [hfull] using hrbound
    have hLAB : L A.1 B.1 ≤ answer n := by
      rw [L_eq]
      change (1 + altSum ((pieceLengths
        (A.1 ∪ completionMarks A.1 f)).mergeSort (· ≥ ·))) / 2 ≤ answer n
      rw [hcompletion.2.2.2.2.1, halt]
      rw [← hformula]
      linarith
    exact (ciInf_le hBddBelow B).trans hLAB
  · have hunder : A.1.card < n := lt_of_le_of_ne A.2.2 hfull
    let blocks : List (List ℝ) := l.map fun x => [x / 2, x / 2]
    let f := blocks.flatten
    have hpieces : l = blocks.map List.sum := by
      unfold blocks
      have hmass : ∀ x : ℝ, ([x / 2, x / 2] : List ℝ).sum = x := by
        intro x
        simp only [List.sum_cons, List.sum_nil]
        ring
      induction l with
      | nil => rfl
      | cons x xs ih =>
          rw [List.map_cons, List.map_cons, hmass]
          exact congrArg (List.cons x) ih
    have hfshape : f = l.flatMap fun x => [x / 2, x / 2] := by
      rfl
    have hfpos : ∀ x ∈ f, 0 < x := by
      rw [hfshape]
      intro x hx
      rcases List.mem_flatMap.mp hx with ⟨y, hy, hxy⟩
      rcases List.mem_cons.mp hxy with rfl | hxy
      · exact div_pos (hlpos y hy) (by norm_num)
      · rw [List.mem_singleton] at hxy
        subst x
        exact div_pos (hlpos y hy) (by norm_num)
    have hflen : f.length = 2 * l.length := by
      rw [hfshape]
      induction l with
      | nil => simp
      | cons x xs ih => simp [ih, Nat.mul_succ]
    have hcard : f.length - 1 - A.1.card ≤ n := by
      rw [hflen, hllen]
      omega
    have hcompletion := orderedBlocks_completion
      (n := n) (A := A.1) (f := f) (blocks := blocks)
      A.2 hfpos hpieces rfl hcard
    dsimp only at hcompletion
    let B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨completionMarks A.1 f, hcompletion.2.1, hcompletion.2.2.1⟩
    have halt : altSum (f.mergeSort (· ≥ ·)) = 0 := by
      rw [hfshape]
      have hdup : l.flatMap (fun x => [x / 2, x / 2]) =
          (l.map fun x => x / 2).flatMap (fun x => [x, x]) := by
        induction l with
        | nil => rfl
        | cons x xs ih =>
            simp only [List.flatMap_cons, List.map_cons]
            rw [ih]
      rw [hdup]
      exact altSum_mergeSort_duplicate_pairs (l.map fun x => x / 2)
    have hLAB : L A.1 B.1 ≤ answer n := by
      rw [L_eq]
      change (1 + altSum ((pieceLengths
        (A.1 ∪ completionMarks A.1 f)).mergeSort (· ≥ ·))) / 2 ≤ answer n
      rw [hcompletion.2.2.2.2.1, halt]
      norm_num
      exact hhalf
    exact (ciInf_le hBddBelow B).trans hLAB

/-! ### Geometric strategy and the lower bound -/

/-- The geometric interval weights, from left to right. -/
def geometricWeights (n : ℕ) : List ℝ :=
  (List.range (n + 1)).map fun k =>
    (2 : ℝ) ^ k / ((2 : ℝ) ^ (n + 1) - 1)

/-- Cumulative geometric marks whose adjacent gaps are the powers `1, 2, ..., 2^n`,
normalized to have total length one. -/
def geometricMarks (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun k =>
    (((2 : ℝ) ^ (k + 1) - 1) / ((2 : ℝ) ^ (n + 1) - 1))

lemma geometricMarks_injective (n : ℕ) : Set.InjOn
    (fun k : ℕ => (((2 : ℝ) ^ (k + 1) - 1) / ((2 : ℝ) ^ (n + 1) - 1)))
    (Finset.range n) := by
  intro i hi j hj hij
  have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := ne_of_gt (answer_den_pos n)
  have hnum := congrArg (fun z : ℝ => z * ((2 : ℝ) ^ (n + 1) - 1)) hij
  simp only [div_mul_cancel₀ _ hden] at hnum
  have hpow : (2 : ℝ) ^ (i + 1) = 2 ^ (j + 1) := by linarith
  have : i + 1 = j + 1 := by
    exact (Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ))) (by exact_mod_cast hpow)
  omega

lemma geometricMarks_card (n : ℕ) : (geometricMarks n).card = n := by
  unfold geometricMarks
  rw [Finset.card_image_iff.mpr (geometricMarks_injective n)]
  simp

lemma geometricMarks_in_interval (n : ℕ) :
    (↑(geometricMarks n) : Set ℝ) ⊆ Set.Ioo 0 1 := by
  intro x hx
  rw [Finset.mem_coe, geometricMarks, Finset.mem_image] at hx
  rcases hx with ⟨k, hk, rfl⟩
  have hklt : k < n := Finset.mem_range.mp hk
  have hden := answer_den_pos n
  constructor
  · apply div_pos
    · have : (1 : ℝ) < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
      linarith
    · exact hden
  · rw [div_lt_one hden]
    have : (2 : ℝ) ^ (k + 1) < 2 ^ (n + 1) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith

lemma geometricMarks_admissible (n : ℕ) : AdmissibleMark n (geometricMarks n) := by
  exact ⟨geometricMarks_in_interval n, (geometricMarks_card n).le⟩

lemma geometricMarks_sort (n : ℕ) :
    (geometricMarks n).sort (· ≤ ·) =
      (List.range n).map (fun k =>
        (((2 : ℝ) ^ (k + 1) - 1) / ((2 : ℝ) ^ (n + 1) - 1))) := by
  let f : ℕ → ℝ := fun k =>
    (((2 : ℝ) ^ (k + 1) - 1) / ((2 : ℝ) ^ (n + 1) - 1))
  have hf : StrictMono f := by
    intro i j hij
    dsimp [f]
    apply (div_lt_div_iff_of_pos_right (answer_den_pos n)).2
    have hp : (2 : ℝ) ^ (i + 1) < 2 ^ (j + 1) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have hnodup : ((List.range n).map f).Nodup :=
    List.Nodup.map hf.injective List.nodup_range
  have hpair : ((List.range n).map f).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun hij => (hf hij).le) List.pairwise_lt_range
  have hsort : (((List.range n).map f).toFinset.sort (· ≤ ·)) =
      (List.range n).map f := (List.toFinset_sort (· ≤ ·) hnodup).2 hpair
  simpa [geometricMarks, f] using hsort

/-- Adjacent differences of sampled values are sampled first differences. -/
lemma zipWith_sub_map_range (f : ℕ → ℝ) (N : ℕ) :
    List.zipWith (fun x y : ℝ => y - x)
      ((List.range (N + 1)).map f) ((List.range (N + 1)).map f).tail =
      (List.range N).map (fun k => f (k + 1) - f k) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_zipWith, List.getElem_map,
      List.getElem_tail, List.getElem_range]

lemma pieceLengths_geometricMarks (n : ℕ) :
    pieceLengths (geometricMarks n) = geometricWeights n := by
  let D : ℝ := (2 : ℝ) ^ (n + 1) - 1
  let f : ℕ → ℝ := fun k => ((2 : ℝ) ^ k - 1) / D
  have hsort := geometricMarks_sort n
  have hendpoints :
      (0 : ℝ) :: (geometricMarks n).sort (· ≤ ·) ++ [1] =
        (List.range (n + 2)).map f := by
    rw [hsort]
    dsimp [f, D]
    rw [show List.range (n + 2) = 0 :: (List.range (n + 1)).map (· + 1) by
      simpa [Nat.succ_eq_add_one] using (List.range_succ_eq_map (n := n + 1))]
    rw [List.range_succ, List.map_append]
    simp [(answer_den_pos n).ne']
  unfold pieceLengths
  rw [hendpoints, zipWith_sub_map_range]
  unfold geometricWeights
  apply List.map_congr_left
  intro k hk
  dsimp [f, D]
  ring

/-- Write adjacent gaps after an initial endpoint `a`. -/
def adjacentSub (a : ℝ) (l : List ℝ) : List ℝ :=
  List.zipWith (fun x y : ℝ => y - x) (a :: l) l

lemma pairwise_last_eq_forces_tail_nil {a : ℝ} {fine : List ℝ}
    (hsort : (a :: fine).Pairwise (· < ·))
    (hlast : (a :: fine).getLast? = some a) : fine = [] := by
  by_contra hf
  have haLast : (a :: fine).getLast (by simp) = a := by
    have hsome := List.getLast?_eq_some_getLast (l := a :: fine) (by simp)
    rw [hlast] at hsome
    exact Option.some.inj hsome.symm
  have haMem : a ∈ fine := by
    have hlastmem : fine.getLast hf ∈ fine := List.getLast_mem hf
    have heq : (a :: fine).getLast (by simp) = fine.getLast hf := List.getLast_cons hf
    rw [← heq, haLast] at hlastmem
    exact hlastmem
  have haa : a < a := by
    rw [List.pairwise_cons] at hsort
    exact hsort.1 a haMem
  exact (lt_irrefl a) haa

lemma getLast?_cons_of_ne {a : ℝ} {l : List ℝ} (hl : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  rw [List.getLast?_cons, List.getLast?_eq_some_getLast hl]
  simp

/-- Generic refinement grouping: if `base` is a sublist of the strictly ordered endpoint tail
`fine`, then the fine adjacent gaps can be grouped into consecutive blocks whose sums are the
base adjacent gaps. -/
lemma group_refinement_aux : ∀ {base fine : List ℝ} (a : ℝ),
    List.Sublist base fine → base ≠ [] → (a :: fine).Pairwise (· < ·) →
    base.getLast? = fine.getLast? →
    ∃ blocks : List (List ℝ),
      blocks.length = base.length ∧
      blocks.flatten = adjacentSub a fine ∧
      blocks.map List.sum = adjacentSub a base := by
  intro base fine a hsub hbase hsort hlast
  induction hsub generalizing a with
  | slnil => exact (hbase rfl).elim
  | @cons l₁ l₂ y hsub ih =>
      have hfine : l₂ ≠ [] := by
        intro hf
        subst l₂
        exact hbase (List.eq_nil_of_sublist_nil hsub)
      have hlast' : l₁.getLast? = l₂.getLast? := by
        rw [getLast?_cons_of_ne hfine] at hlast
        exact hlast
      obtain ⟨blocks, hlen, hflatten, hsums⟩ :=
        ih y hbase hsort.tail hlast'
      have hblocks : blocks ≠ [] := by
        intro hb
        rw [hb] at hlen
        simp only [List.length_nil] at hlen
        exact hbase (List.length_eq_zero_iff.mp hlen.symm)
      cases hb : blocks with
      | nil => exact (hblocks hb).elim
      | cons block rest =>
          refine ⟨((y - a) :: block) :: rest, ?_, ?_, ?_⟩
          · simpa [hb] using hlen
          · simp only [List.flatten_cons, List.cons_append, adjacentSub,
              List.zipWith_cons_cons]
            unfold adjacentSub at hflatten
            rw [← hflatten, hb]
            rfl
          · cases hbbase : l₁ with
            | nil => exact (hbase hbbase).elim
            | cons b bs =>
                simp only [adjacentSub, List.zipWith_cons_cons, List.map_cons]
                rw [hbbase, hb] at hsums
                simp only [List.map_cons, adjacentSub, List.zipWith_cons_cons] at hsums
                have hblocksum : block.sum = b - y := (List.cons.inj hsums).1
                have hrest : List.map List.sum rest =
                    List.zipWith (fun x y : ℝ => y - x) (b :: bs) bs :=
                  (List.cons.inj hsums).2
                rw [hrest, List.sum_cons, hblocksum]
                congr 1
                ring
  | @cons_cons l₁ l₂ b hsub ih =>
      by_cases hb : l₁ = []
      · subst l₁
        have hsingle : (b :: l₂).getLast? = some b := by simpa using hlast.symm
        have hfine : l₂ = [] := pairwise_last_eq_forces_tail_nil hsort.tail hsingle
        subst l₂
        exact ⟨[[b - a]], by simp, by simp [adjacentSub], by simp [adjacentSub]⟩
      · have hfine : l₂ ≠ [] := by
          intro hf
          subst l₂
          exact hb (List.eq_nil_of_sublist_nil hsub)
        have hlast' : l₁.getLast? = l₂.getLast? := by
          rw [getLast?_cons_of_ne hb, getLast?_cons_of_ne hfine] at hlast
          exact hlast
        obtain ⟨blocks, hlen, hflatten, hsums⟩ :=
          ih b hb hsort.tail hlast'
        refine ⟨[b - a] :: blocks, ?_, ?_, ?_⟩
        · simp [hlen]
        · simp [adjacentSub, hflatten]
        · simp [adjacentSub, hsums]

lemma sorted_endpoints_sublist_of_subset {A C : Finset ℝ} (hAC : A ⊆ C) :
    List.Sublist ((0 : ℝ) :: A.sort (· ≤ ·) ++ [1])
      ((0 : ℝ) :: C.sort (· ≤ ·) ++ [1]) := by
  have hbase : List.Sublist (A.sort (· ≤ ·)) (C.sort (· ≤ ·)) := by
    have hsubperm : List.Subperm (A.sort (· ≤ ·)) (C.sort (· ≤ ·)) := by
      apply (Finset.sort_nodup A (· ≤ ·)).subperm
      intro x hx
      rw [Finset.mem_sort] at hx ⊢
      exact hAC hx
    have h := List.sublist_insertionSort' (Finset.pairwise_sort A (· ≤ ·)) hsubperm
    simpa [List.Pairwise.insertionSort_eq (Finset.pairwise_sort C (· ≤ ·))] using h
  exact (hbase.cons_cons 0).append (List.Sublist.refl [1])

lemma sorted_endpoints_pairwise_lt {S : Finset ℝ}
    (hS : (↑S : Set ℝ) ⊆ Set.Ioo 0 1) :
    ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).Pairwise (· < ·) := by
  change ((0 : ℝ) :: (S.sort (· ≤ ·) ++ [1])).Pairwise (· < ·)
  rw [List.pairwise_cons]
  constructor
  · intro y hy
    simp only [List.mem_append, Finset.mem_sort, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact (hS hy).1
    · norm_num
  · rw [List.pairwise_append]
    refine ⟨finset_sort_pairwise_lt S, by simp, ?_⟩
    intro y hy z hz
    simp only [Finset.mem_sort] at hy
    simp only [List.mem_singleton] at hz
    subst z
    exact (hS hy).2

/-- Adding marks refines the old interval list into consecutive blocks with the old interval sums. -/
lemma pieceLengths_refinement_blocks {A C : Finset ℝ} (hAC : A ⊆ C)
    (hC : (↑C : Set ℝ) ⊆ Set.Ioo 0 1) :
    ∃ blocks : List (List ℝ),
      blocks.length = A.card + 1 ∧
      blocks.flatten = pieceLengths C ∧
      blocks.map List.sum = pieceLengths A := by
  have hsub := (sorted_endpoints_sublist_of_subset hAC).tail
  have hbase : A.sort (· ≤ ·) ++ [1] ≠ [] := by simp
  have hsort : ((0 : ℝ) :: (C.sort (· ≤ ·) ++ [1])).Pairwise (· < ·) :=
    sorted_endpoints_pairwise_lt hC
  have hlast : (A.sort (· ≤ ·) ++ [1]).getLast? =
      (C.sort (· ≤ ·) ++ [1]).getLast? := by simp
  obtain ⟨blocks, hlen, hflatten, hsums⟩ :=
    group_refinement_aux 0 hsub hbase hsort hlast
  refine ⟨blocks, ?_, ?_, ?_⟩
  · simpa using hlen
  · simpa [pieceLengths, adjacentSub] using hflatten
  · simpa [pieceLengths, adjacentSub] using hsums

lemma geometricWeights_get (n : ℕ) (i : Fin (n + 1)) :
    (geometricWeights n).get (Fin.cast (by simp [geometricWeights]) i) =
      (1 / ((2 : ℝ) ^ (n + 1) - 1)) * (2 : ℝ) ^ (i : ℕ) := by
  simp [geometricWeights]
  ring

/-- The geometric strategy forces the sharp lower bound against every legal response. -/
lemma L_ge_answer_geometricMarks (n : ℕ) {B : Finset ℝ}
    (hB : AdmissibleMark n B) : answer n ≤ L (geometricMarks n) B := by
  let A := geometricMarks n
  let C := A ∪ B
  let δ : ℝ := 1 / ((2 : ℝ) ^ (n + 1) - 1)
  have hAadm : AdmissibleMark n A := geometricMarks_admissible n
  have hC : (↑C : Set ℝ) ⊆ Set.Ioo 0 1 := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_union] at hx
    exact hx.elim (fun hxA => hAadm.1 hxA) (fun hxB => hB.1 hxB)
  obtain ⟨blocks, hlen, hflatten, hsums⟩ :=
    pieceLengths_refinement_blocks (A := A) (C := C)
      (Finset.subset_union_left) hC
  have hlen' : blocks.length = n + 1 := by
    rw [hlen, show A.card = n from geometricMarks_card n]
  have hnonneg : ∀ x ∈ blocks.flatten, 0 ≤ x := by
    intro x hx
    rw [hflatten] at hx
    exact pieceLengths_nonneg hC x hx
  have hblocksum : ∀ i : Fin (n + 1),
      (blocks.get (Fin.cast hlen'.symm i)).sum = δ * (2 : ℝ) ^ (i : ℕ) := by
    intro i
    have hiblocks : i.1 < blocks.length := by
      rw [hlen']
      exact i.2
    have hiA : i.1 < (pieceLengths A).length := by
      rw [pieceLengths_length, show A.card = n from geometricMarks_card n]
      exact i.2
    have hmap := congrArg (fun l : List ℝ => l.getD i.1 0) hsums
    dsimp only at hmap
    rw [List.getD_eq_getElem _ _ (by simpa using hiblocks),
      List.getD_eq_getElem _ _ hiA] at hmap
    simp only [List.getElem_map] at hmap
    have hgeom : pieceLengths A = geometricWeights n := by
      exact pieceLengths_geometricMarks n
    have hiweights : i.1 < (geometricWeights n).length := by
      simpa [geometricWeights] using i.2
    have hgeomMap := congrArg (fun l : List ℝ => l.getD i.1 0) hgeom
    dsimp only at hgeomMap
    rw [List.getD_eq_getElem _ _ hiA,
      List.getD_eq_getElem _ _ hiweights] at hgeomMap
    calc
      (blocks.get (Fin.cast hlen'.symm i)).sum =
          (pieceLengths A)[i.1]'hiA := by
            simpa only [List.get_eq_getElem] using hmap
      _ = (geometricWeights n)[i.1]'hiweights := hgeomMap
      _ = δ * (2 : ℝ) ^ (i : ℕ) := by
        simpa only [List.get_eq_getElem] using geometricWeights_get n i
  have hfrag : blocks.flatten.length ≤ 2 * (n + 1) - 1 := by
    rw [hflatten, pieceLengths_length]
    have hu : C.card ≤ A.card + B.card := Finset.card_union_le A B
    have hAle : A.card ≤ n := hAadm.2
    have hBle : B.card ≤ n := hB.2
    omega
  let R : GeometricRefinement δ (n + 1) :=
    ⟨blocks, hlen', hnonneg, hblocksum, hfrag⟩
  have hδ : 0 ≤ δ := (one_div_pos.mpr (answer_den_pos n)).le
  have halt : δ ≤ altSum (sortedFragments R.blocks) :=
    R.altSum_sortedFragments_ge_delta (by omega) hδ
  have hsorted : sortedFragments R.blocks =
      (pieceLengths C).mergeSort (· ≥ ·) := by
    unfold sortedFragments R
    rw [hflatten]
  rw [hsorted] at halt
  rw [show L (geometricMarks n) B = L A B by rfl]
  rw [L_eq]
  change answer n ≤ (1 + altSum ((pieceLengths C).mergeSort (· ≥ ·))) / 2
  have hanswer : answer n = (1 + δ) / 2 := by
    unfold answer δ
    have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := (answer_den_pos n).ne'
    have heq :
        2 * (2 : ℝ) ^ n = ((2 : ℝ) ^ (n + 1) - 1) + 1 := by
      rw [pow_succ]
      ring
    calc
      (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) =
          (2 * (2 : ℝ) ^ n) / (2 * ((2 : ℝ) ^ (n + 1) - 1)) := by
            field_simp
      _ = (((2 : ℝ) ^ (n + 1) - 1) + 1) /
          (2 * ((2 : ℝ) ^ (n + 1) - 1)) := by rw [heq]
      _ = (1 + 1 / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
        field_simp
  rw [hanswer]
  linarith

/-- Full lower bound, using `geometricMarks n` as the fixed legal first-player strategy. -/
lemma answer_le_V (n : ℕ) : answer n ≤ V n := by
  let A0 : {A : Finset ℝ // AdmissibleMark n A} :=
    ⟨geometricMarks n, geometricMarks_admissible n⟩
  have hBddAbove : BddAbove (Set.range fun A : {A : Finset ℝ // AdmissibleMark n A} =>
      ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨A, rfl⟩
    let B0 : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨∅, admissible_empty n, by simp⟩
    have hBddBelow : BddBelow (Set.range fun B :
        {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1) := by
      refine ⟨(1 : ℝ) / 2, ?_⟩
      rintro _ ⟨B, rfl⟩
      exact (L_bounds_of_admissible A.2 B.2.1).1
    exact (ciInf_le hBddBelow B0).trans (L_bounds_of_admissible A.2 B0.2.1).2
  apply (le_ciSup hBddAbove A0).trans'
  letI := responseSubtypeNonempty n A0
  apply le_ciInf
  intro B
  exact L_ge_answer_geometricMarks n B.2.1


/-- The requested value identity. -/
theorem imo2026_p3 (n : ℕ) (hn : 0 < n) : V n = answer n := by
  exact le_antisymm (V_le_answer n hn) (answer_le_V n)

end
end IMO2026P3
