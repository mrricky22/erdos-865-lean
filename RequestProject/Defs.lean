import Mathlib

open scoped BigOperators
open Finset

namespace Erdos865

/-!
# Erdős problem 865 — core definitions

We work with finite subsets `A : Finset ℕ`.  A set "contains a triple" if there are
three distinct elements `a, b, c ∈ A` all of whose pairwise sums lie in `A`.
A set is *bad* if it contains no such triple.

The constraint `A ⊆ {1,…,N}` is expressed by the predicate `MemRange N A`.
-/

/-- `A ⊆ {1, …, N}`. -/
def MemRange (N : ℕ) (A : Finset ℕ) : Prop := ∀ x ∈ A, 1 ≤ x ∧ x ≤ N

/-- `A` contains three distinct elements whose three pairwise sums all lie in `A`. -/
def HasTriple (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/-- `A` is *bad* if it contains no admissible triple. -/
def IsBad (A : Finset ℕ) : Prop := ¬ HasTriple A

/-! ## Folded additive sets (used in Lemma 1) -/

/-- The set of residues occurring as a *non-wrapped* sum `x + y` of two distinct elements
of `B`, with `x + y < m`. -/
noncomputable def lowSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (((B ×ˢ B).filter (fun p => p.1 < p.2 ∧ p.1 + p.2 < m)).image (fun p => p.1 + p.2))

/-- The set of residues occurring as a *wrapped* sum `x + y - m` of two distinct elements
of `B`, with `x + y > m`. -/
noncomputable def highSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (((B ×ˢ B).filter (fun p => p.1 < p.2 ∧ m < p.1 + p.2)).image (fun p => p.1 + p.2 - m))

/-- Residues that occur both as a low (non-wrapped) and a high (wrapped) sum. -/
noncomputable def collisions (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  lowSums m B ∩ highSums m B

/-- The hypothesis of Lemma 1: `B ⊆ {1,…,m-1}` and no two distinct elements of `B`
have sum `≡ 0 (mod m)` or `≡ an element of B (mod m)`. -/
def FoldedOK (m : ℕ) (B : Finset ℕ) : Prop :=
  (∀ x ∈ B, 1 ≤ x ∧ x < m) ∧
  (∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ (m ∣ (x + y)) ∧ (x + y) % m ∉ B)

/-! ## Folding a bad set around a pivot `h` (used in Lemma 2) -/

/-- `X = { r : 1 ≤ r < h, r ∈ A }`. -/
noncomputable def Xset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => r ∈ A)

/-- `Y = { r : 1 ≤ r < h, h + r ∈ A }` (with the automatic constraint `h + r ≤ N` coming
from `MemRange N A`). -/
noncomputable def Yset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => h + r ∈ A)

/-- `B = X ∩ Y`: the residues `r` with both `r` and `h + r` in `A`. -/
noncomputable def Bset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  Xset h A ∩ Yset h A

/-- `E = {1,…,h-1} \ (X ∪ Y)`. -/
noncomputable def Eset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 h) \ (Xset h A ∪ Yset h A)

end Erdos865
