import RequestProject.Defs
import RequestProject.Lemma1

set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset

namespace Erdos865

/-!
# Erdős problem 865 — conditional proof of the `5/8` upper bound

This file formalizes the user's argument that every *bad* set `A ⊆ {1,…,N}` has
`|A| ≤ (5/8) N + O(1)`, **conditional on** the external "coarse theorem"
`CoarseBound θ K₀` for some `θ < 2/3`.

The logical chain is:

* `lemma1`  : the folded additive lemma, `|B| − |C(B)| ≤ m/4 + O(1)`.
* `lemma2`  : folding a bad set around a pivot, `|X| + |Y| ≤ (5/4)h − |I| + O(1)`.
* `badset_even` : the `5/4 H` bound for bad subsets of `{1,…,2H}` (uses `lemma2` + coarse).
* `badset_card_le` : the `5/8 N` bound for all `N` (reduces odd `N` to even).
* `erdos865` : the threshold statement (existence of a triple once `|A| ≥ (5/8)N + C`).
* `sharp`   : the matching construction, showing the constant `5/8` is best possible.
-/

/-- The external "coarse theorem": every bad `S ⊆ {1,…,M}` has `|S| ≤ θ M + K₀`. -/
def CoarseBound (θ K0 : ℝ) : Prop :=
  ∀ (M : ℕ) (S : Finset ℕ), MemRange M S → IsBad S → (S.card : ℝ) ≤ θ * M + K0

/-! ## Helper lemmas for Lemma 2 -/

/-
The folded set `B = X ∩ Y` satisfies the hypothesis `FoldedOK h B` of Lemma 1.
-/
theorem Bset_foldedOK (h : ℕ) (A : Finset ℕ) (hbad : IsBad A)
    (hh : h ∈ A) (hh1 : 1 ≤ h) : FoldedOK h (Bset h A) := by
  refine' ⟨ _, _ ⟩;
  · exact fun x hx => ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1 ) |>.1, Finset.mem_Ico.mp ( Finset.mem_filter.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1 ) |>.2 ⟩;
  · intro x hx y hy hxy
    by_contra h_contra
    have h_triple : x + y ∈ A := by
      unfold Bset at *; simp_all +decide [ Finset.mem_inter ] ;
      unfold Xset Yset at *; simp_all +decide [ Finset.mem_filter, Finset.mem_Ico ] ;
      by_cases h_div : h ∣ x + y <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      · have := Nat.dvd_of_mod_eq_zero h_div; obtain ⟨ k, hk ⟩ := this; rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        grind;
      · -- Since $x + y \equiv r \pmod{h}$ and $r \in A$, we have $x + y = r + kh$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, x + y = (x + y) % h + k * h := by
          exact ⟨ ( x + y ) / h, by rw [ Nat.mod_add_div' ] ⟩;
        rcases k with ( _ | _ | k ) <;> norm_num at *;
        · grind;
        · grind +splitIndPred;
        · grind +splitIndPred;
    refine' hbad _;
    use x, ?_, y, ?_, h, ?_ <;> simp_all +decide [ Bset, Xset, Yset ];
    lia

/-
Every collision residue lies in the excluded set `E`.
-/
theorem collisions_subset_Eset (h : ℕ) (A : Finset ℕ) (hbad : IsBad A)
    (hh : h ∈ A) : collisions h (Bset h A) ⊆ Eset h A := by
  intro x hx
  simp [collisions, lowSums, highSums, Eset] at hx ⊢
  rcases hx with ⟨ ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, hlt ⟩, rfl ⟩, ⟨ c, d, ⟨ ⟨ hc, hd ⟩, hcd, hlt' ⟩, hcd' ⟩ ⟩ ; simp_all +decide [ Bset, Xset, Yset ] ;
  refine' ⟨ by linarith, _, _ ⟩ <;> intro <;> contrapose! hbad <;> simp_all +decide [ IsBad ];
  · use a, ha.1.2, b, hb.1.2, h, hh;
    grind;
  · use c, hc.1.2, d, hd.1.2, h, hh;
    grind

/-
The basic counting identity `|X| + |Y| + |E| = |{1,…,h-1}| + |B|`.
-/
theorem card_XY_identity (h : ℕ) (A : Finset ℕ) :
    (Xset h A).card + (Yset h A).card + (Eset h A).card
      = (Finset.Ico 1 h).card + (Bset h A).card := by
  unfold Xset Yset Bset Eset;
  rw [ Finset.card_sdiff ];
  rw [ show ( Xset h A ∪ Yset h A ) ∩ Finset.Ico 1 h = ( Xset h A ∪ Yset h A ) from ?_ ];
  · zify [ Xset, Yset ];
    rw [ Nat.cast_sub ];
    · grind;
    · exact Finset.card_le_card ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) );
  · exact Finset.inter_eq_left.mpr ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) )

/-! ## Lemma 2 : folding a bad set around a pivot -/

/-
**Lemma 2.** There is an absolute constant `K₂` such that for every bad `A ⊆ {1,…,N}`,
every pivot `h ∈ A`, and every `I ⊆ E ∖ C(B)`, one has
`|X| + |Y| ≤ (5/4)h − |I| + K₂`.
-/
theorem lemma2 :
    ∃ K2 : ℝ, ∀ (N h : ℕ) (A : Finset ℕ), MemRange N A → IsBad A → h ∈ A → 1 ≤ h →
      ∀ I : Finset ℕ, I ⊆ (Eset h A) \ (collisions h (Bset h A)) →
        ((Xset h A).card + (Yset h A).card : ℝ) ≤ 5 / 4 * h - I.card + K2 := by
  -- Let's choose K2 as the maximum of the constants from lemma1 and 0, plus 2.
  use max (Classical.choose (lemma1)) 0 + 2;
  intro N h A hA hbad hh hh1 I hI;
  by_cases hh2 : 2 ≤ h;
  · have := Classical.choose_spec ( lemma1 ) h ( Bset h A ) hh2 ( Bset_foldedOK h A hbad hh hh1 );
    -- Using the identity from `card_XY_identity`, we can rewrite the goal in terms of `B` and `E`.
    have h_identity : ((Xset h A).card : ℝ) + ((Yset h A).card : ℝ) = (h - 1 : ℝ) + (Bset h A).card - (Eset h A).card := by
      have h_identity : ((Xset h A).card : ℝ) + ((Yset h A).card : ℝ) + ((Eset h A).card : ℝ) = (h - 1 : ℝ) + (Bset h A).card := by
        have := card_XY_identity h A; norm_cast at *; aesop;
      linarith;
    -- Using the fact that $E \geq I + C$, we can substitute this into the identity.
    have h_E_ge_I_C : (Eset h A).card ≥ (I.card : ℝ) + (collisions h (Bset h A)).card := by
      norm_cast;
      rw [ ← Finset.card_union_of_disjoint ];
      · exact Finset.card_le_card ( Finset.union_subset ( hI.trans ( Finset.sdiff_subset ) ) ( collisions_subset_Eset h A hbad hh ) );
      · exact Finset.disjoint_left.mpr fun x hxI hx => Finset.mem_sdiff.mp ( hI hxI ) |>.2 hx;
    grind;
  · interval_cases h ; norm_num [ Xset, Yset, Eset ] at *;
    norm_num [ hI ] ; positivity

/-! ## The even case -/

/-
Counting helper: every element of a bad set `A ⊆ {1,…,2H}` is counted by `X` (if `< h`),
is the pivot `h`, is counted by `Y` (if `h < · < 2h`), or lies in the tail `· ≥ 2h`.
-/
theorem card_le_XY_tail (H h : ℕ) (A : Finset ℕ) (hA : MemRange (2 * H) A) (hh1 : 1 ≤ h) :
    A.card ≤ (Xset h A).card + (Yset h A).card + (A.filter (fun a => 2 * h ≤ a)).card + 1 := by
  -- Let's simplify the goal using the definitions of `Xset`, `Yset`, and `Eset`.
  suffices h_suff : A ⊆ (Xset h A) ∪ (Yset h A).image (fun r => h + r) ∪ {h} ∪ (A.filter (fun a => 2 * h ≤ a)) by
    refine le_trans ( Finset.card_le_card h_suff ) ?_;
    grind;
  intro x hx; by_cases hx' : x < h <;> by_cases hx'' : x = h <;> simp_all +decide [ Xset, Yset ] ;
  · exact Or.inl ( hA x hx |>.1 );
  · exact if h'' : x < 2 * h then Or.inr <| Or.inl ⟨ x - h, ⟨ ⟨ by omega, by omega ⟩, by convert hx using 1; omega ⟩, by omega ⟩ else Or.inr <| Or.inr <| by omega;

/-
Combined counting bound: folding a bad set around a pivot `h`, with an excluded set `I`
and the tail of elements `≥ 2h`, gives `|A| ≤ (5/4)h + |tail| − |I| + O(1)`.
-/
theorem pivot_bound :
    ∃ K : ℝ, ∀ (H h : ℕ) (A : Finset ℕ), MemRange (2 * H) A → IsBad A → h ∈ A → 1 ≤ h →
      ∀ I : Finset ℕ, I ⊆ (Eset h A) \ (collisions h (Bset h A)) →
        (A.card : ℝ) ≤ 5 / 4 * h + (A.filter (fun a => 2 * h ≤ a)).card - I.card + K := by
  obtain ⟨ K2, hK2 ⟩ := lemma2;
  use K2 + 1;
  intro H h A hA hbad hh hh1 I hI; linarith [ hK2 ( 2 * H ) h A hA hbad hh hh1 I hI, show ( A.card : ℝ ) ≤ ( Xset h A ).card + ( Yset h A ).card + ( A.filter fun a => 2 * h ≤ a ).card + 1 from mod_cast card_le_XY_tail H h A hA hh1 ] ;

/-
**Case 1** (`s ≤ 4e`): fold around `q = H + s`.  No use of the coarse theorem.
-/
theorem badset_case1 :
    ∃ C : ℝ, ∀ (H : ℕ) (A : Finset ℕ) (p q : ℕ),
      MemRange (2 * H) A → IsBad A → 1 ≤ p → p ≤ H → H ≤ q → q ≤ 2 * H →
      p ∈ A → q ∈ A → (∀ x ∈ A, x ≤ p ∨ q ≤ x) → q - H ≤ 4 * (H - p) →
      (A.card : ℝ) ≤ 5 / 4 * H + C := by
  by_contra h_contra;
  -- Apply `pivot_bound` to obtain a contradiction.
  obtain ⟨K, hK⟩ := pivot_bound;
  refine' h_contra ⟨ K + 2, fun H A p q hA hbad hp1 hpH hHq hq2H hpA hqA hgap hcase => _ ⟩;
  -- Let $I := \text{Finset.Ioo}(H - \min(e, s), q)$.
  set e := H - p
  set s := q - H
  set m0 := min e s
  set I := Finset.Ioo (H - m0) q;
  -- CLAIM A: I ⊆ Eset q A \ collisions q (Bset q A).
  have hI_subset : I ⊆ Eset q A \ collisions q (Bset q A) := by
    intro r hr; simp_all +decide [ Eset, collisions ] ;
    refine' ⟨ ⟨ ⟨ _, _ ⟩, _, _ ⟩, _ ⟩;
    · grind;
    · exact Finset.mem_Ioo.mp hr |>.2;
    · simp +zetaDelta at *;
      exact fun h => by have := hgap r ( Finset.mem_filter.mp h |>.2 ) ; omega;
    · simp +zetaDelta at *;
      exact fun h => by have := hA _ ( Finset.mem_filter.mp h |>.2 ) ; omega;
    · intro hr₁ hr₂; simp_all +decide [ lowSums, highSums ] ;
      obtain ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, h ⟩, rfl ⟩ := hr₁; obtain ⟨ c, d, ⟨ ⟨ hc, hd ⟩, hcd, h' ⟩, h'' ⟩ := hr₂; simp_all +decide [ Bset, Xset, Yset ] ;
      grind;
  -- CLAIM B: (I.card : ℝ) ≥ (s:ℝ) + m0 - 1.
  have hI_card : (I.card : ℝ) ≥ (s : ℝ) + m0 - 1 := by
    simp +zetaDelta at *;
    norm_cast;
    omega;
  -- CLAIM C: (A.filter (fun a => 2*q ≤ a)).card ≤ 1.
  have h_filter_card : (A.filter (fun a => 2 * q ≤ a)).card ≤ 1 := by
    exact Finset.card_le_one.mpr fun x hx y hy => by linarith [ Finset.mem_filter.mp hx, Finset.mem_filter.mp hy, hA x ( Finset.mem_filter.mp hx |>.1 ), hA y ( Finset.mem_filter.mp hy |>.1 ) ] ;
  -- Apply `pivot_bound` with `h = q`.
  have h_pivot : (A.card : ℝ) ≤ 5 / 4 * q + (A.filter (fun a => 2 * q ≤ a)).card - I.card + K := by
    grind;
  -- Since $m0 = \min(e, s)$, we have $(1/4)*s - m0 \leq 0$.
  have h_min : (1 / 4 : ℝ) * s - m0 ≤ 0 := by
    cases min_cases e s <;> simp +decide [ * ];
    · rw [ inv_mul_le_iff₀ ] <;> norm_cast;
      grind;
    · grind +splitImp;
  linarith [ show ( q : ℝ ) = H + s by rw [ Nat.cast_sub ] <;> linarith, show ( Finset.card ( Finset.filter ( fun a => 2 * q ≤ a ) A ) : ℝ ) ≤ 1 by exact_mod_cast h_filter_card ]

/-
**Case 2** (`s > 4e`): fold around `p = H − e`; uses the coarse theorem.
-/
theorem badset_case2 {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (H : ℕ) (A : Finset ℕ) (p q : ℕ),
      MemRange (2 * H) A → IsBad A → 1 ≤ p → p ≤ H → H ≤ q → q ≤ 2 * H →
      p ∈ A → q ∈ A → (∀ x ∈ A, x ≤ p ∨ q ≤ x) → 4 * (H - p) < q - H →
      (A.card : ℝ) ≤ 5 / 4 * H + C := by
  -- Apply `pivot_bound` to obtain the constant `K`.
  obtain ⟨K, hK⟩ := pivot_bound;
  use K0 + K + 3;
  intro H A p q hA hbad hp1 hpH hHq hq2H hpA hqA hgap hcase;
  let e := H - p;
  let s := q - H;
  have he : p = H - e := by
    rw [ Nat.sub_sub_self hpH ];
  have hs : q = H + s := by
    rw [ Nat.add_sub_of_le hHq ];
  have h4e : 4 * e < s := by
    exact hcase;
  have hs_le_H : s ≤ H := by
    omega;
  have ht : 1 ≤ p := by
    grind;
  obtain ⟨I, hI⟩ : ∃ I : Finset ℕ, I ⊆ (Eset p A) \ (collisions p (Bset p A)) ∧ (I.card : ℝ) ≥ (1 - θ) * (min (s + e - 1) (p - 1)) - K0 := by
    refine' ⟨ Finset.Icc 1 ( Min.min ( s + e - 1 ) ( p - 1 ) ) \ A, _, _ ⟩;
    · intro x hx; simp +decide [ Eset, Bset ] at hx ⊢;
      refine' ⟨ ⟨ ⟨ hx.1.1, lt_of_le_of_lt hx.1.2.2 ( Nat.pred_lt ( ne_bot_of_gt ht ) ) ⟩, _, _ ⟩, _ ⟩ <;> simp +decide [ Xset, Yset, collisions ] at hx ⊢;
      · exact fun _ _ => hx.2;
      · grind +extAll;
      · intro hx' hx''; simp +decide [ lowSums, highSums ] at hx' hx'';
        grind +qlia;
    · have hI_card : (Finset.Icc 1 (min (s + e - 1) (p - 1)) ∩ A).card ≤ θ * (min (s + e - 1) (p - 1)) + K0 := by
        convert hc ( Min.min ( s + e - 1 ) ( p - 1 ) ) ( Finset.Icc 1 ( Min.min ( s + e - 1 ) ( p - 1 ) ) ∩ A ) _ _ using 1;
        · exact fun x hx => ⟨ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1, Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.1 ) |>.2 ⟩;
        · intro h;
          obtain ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, ha', hb', hc' ⟩ := h;
          exact hbad ⟨ a, by simp +decide at ha; tauto, b, by simp +decide at hb; tauto, c, by simp +decide at hc; tauto, hab, hac, hbc, by simp +decide at ha'; tauto, by simp +decide at hb'; tauto, by simp +decide at hc'; tauto ⟩;
      rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · norm_num [ Finset.inter_comm ] at * ; linarith;
      · exact Finset.card_le_card fun x hx => by simpa using Finset.mem_inter.mp hx |>.2;
  -- Apply `pivot_bound` with `h = p` and `I` as chosen.
  have h_pivot : (A.card : ℝ) ≤ 5 / 4 * p + (A.filter (fun a => 2 * p ≤ a)).card - I.card + K := by
    exact hK H p A hA hbad hpA ht I hI.1;
  -- Bound the tail: $(A.filter (fun a => 2 * p ≤ a)).card ≤ 2 * e + 1$.
  have h_tail : (A.filter (fun a => 2 * p ≤ a)).card ≤ 2 * e + 1 := by
    have h_tail : (A.filter (fun a => 2 * p ≤ a)).card ≤ (Finset.Icc (2 * p) (2 * H)).card := by
      exact Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_filter.mp hx ], by linarith [ Finset.mem_filter.mp hx, hA x ( Finset.mem_filter.mp hx |>.1 ) ] ⟩;
    exact h_tail.trans ( by norm_num; omega );
  -- Bound the term $(3/4)*e - (1-θ)*t$.
  have h_bound : (3 / 4 : ℝ) * e - (1 - θ) * (min (s + e - 1) (p - 1)) ≤ 2 := by
    rcases le_total ( s + e - 1 ) ( p - 1 ) with h | h <;> norm_num [ h ];
    · rw [ Nat.cast_sub ];
      · rw [ Nat.cast_sub ] <;> push_cast;
        · rw [ Nat.cast_sub ];
          · nlinarith only [ show ( q : ℝ ) ≥ H + 4 * ( H - p ) + 1 by exact_mod_cast by omega, hθ, show ( p : ℝ ) ≤ H by exact_mod_cast hpH ];
          · grind +qlia;
        · omega;
      · grind +qlia;
    · rw [ Nat.cast_sub ];
      · rw [ Nat.cast_sub ] <;> norm_num;
        · nlinarith only [ show ( p : ℝ ) ≥ 1 by norm_cast, show ( H : ℝ ) ≥ p by norm_cast, hθ, show ( p : ℝ ) ≤ H by norm_cast, show ( q : ℝ ) ≥ H by norm_cast, show ( s : ℝ ) ≤ H by norm_cast, show ( e : ℝ ) = H - p by exact eq_sub_of_add_eq <| by norm_cast; omega, show ( s : ℝ ) ≥ 4 * e + 1 by norm_cast ];
        · linarith;
      · linarith;
  rw [ he ] at *;
  rw [ Nat.cast_sub ( by omega ) ] at *;
  rw [ Nat.cast_sub ( by omega ) ] at *;
  linarith [ show ( Finset.card ( Finset.filter ( fun a => 2 * ( H - ( H - p ) ) ≤ a ) A ) : ℝ ) ≤ 2 * ( H - p ) + 1 by exact_mod_cast h_tail ]

/-
**Even case.** Conditional on the coarse theorem, every bad `A ⊆ {1,…,2H}` has
`|A| ≤ (5/4)H + O(1)`.
-/
theorem badset_even {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (H : ℕ) (A : Finset ℕ), MemRange (2 * H) A → IsBad A →
      (A.card : ℝ) ≤ 5 / 4 * H + C := by
  -- Set $C$ to be the maximum of the constants from `badset_case1` and `badset_case2$ (and ensure it is at least zero).
  obtain ⟨C1, hC1⟩ := badset_case1
  obtain ⟨C2, hC2⟩ := badset_case2 hθ hc
  use max (max C1 C2) 0;
  intro H A hA hbad;
  by_cases hL1 : A.filter (fun x => x ≤ H) = ∅;
  · -- Since $Llow$ is empty, all elements of $A$ are greater than $H$, so $A \subseteq \{H+1, \ldots, 2H\}$.
    have hA_subset : A ⊆ Finset.Icc (H + 1) (2 * H) := by
      exact fun x hx => Finset.mem_Icc.mpr ⟨ Nat.succ_le_of_lt ( lt_of_not_ge fun hx' => Finset.notMem_empty x <| hL1 ▸ Finset.mem_filter.mpr ⟨ hx, hx' ⟩ ), hA x hx |>.2 ⟩;
    have := Finset.card_le_card hA_subset; norm_num at *;
    exact le_trans ( Nat.cast_le.mpr this ) ( by rw [ Nat.cast_sub ( by linarith ) ] ; push_cast; linarith [ le_max_left ( max C1 C2 ) 0, le_max_right ( max C1 C2 ) 0, le_max_left C1 C2, le_max_right C1 C2 ] );
  · by_cases hL2 : A.filter (fun x => H ≤ x) = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      exact le_add_of_le_of_nonneg ( by rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast ; linarith [ show A.card ≤ H from le_trans ( Finset.card_le_card ( show A ⊆ Finset.Ico 1 H from fun x hx => Finset.mem_Ico.mpr ⟨ by linarith [ hA x hx ], hL2 x hx ⟩ ) ) ( by simp ) ] ) ( by positivity );
    · -- Set $p := Llow.max' (nonempty)$ and $q := Lhigh.min' (nonempty)$.
      obtain ⟨p, hp⟩ : ∃ p ∈ A, p ≤ H ∧ ∀ x ∈ A, x ≤ H → x ≤ p := by
        exact ⟨ Finset.max' ( Finset.filter ( fun x => x ≤ H ) A ) ( Finset.nonempty_of_ne_empty hL1 ), Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun x => x ≤ H ) A ) ( Finset.nonempty_of_ne_empty hL1 ) ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun x => x ≤ H ) A ) ( Finset.nonempty_of_ne_empty hL1 ) ) |>.2, fun x hx hx' => Finset.le_max' _ _ ( by aesop ) ⟩
      obtain ⟨q, hq⟩ : ∃ q ∈ A, H ≤ q ∧ ∀ x ∈ A, H ≤ x → q ≤ x := by
        exact ⟨ Finset.min' ( Finset.filter ( fun x => H ≤ x ) A ) ( Finset.nonempty_of_ne_empty hL2 ), Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun x => H ≤ x ) A ) ( Finset.nonempty_of_ne_empty hL2 ) ) |>.1, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun x => H ≤ x ) A ) ( Finset.nonempty_of_ne_empty hL2 ) ) |>.2, fun x hx hx' => Finset.min'_le _ _ ( by aesop ) ⟩;
      by_cases h_case : q - H ≤ 4 * (H - p);
      · refine le_trans ( hC1 H A p q hA hbad ?_ ?_ ?_ ?_ hp.1 hq.1 ?_ h_case ) ?_;
        any_goals linarith [ hA p hp.1, hA q hq.1 ];
        · grind;
        · grind;
      · refine le_trans ( hC2 H A p q hA hbad ?_ ?_ ?_ ?_ hp.1 hq.1 ?_ ?_ ) ?_;
        any_goals linarith [ hA p hp.1, hA q hq.1 ];
        · grind;
        · grind

/-! ## Reduction to general `N` -/

/-
The `5/8 N` bound for all `N`, obtained from the even case by embedding `{1,…,N}` into
`{1,…,2H}` with `N ≤ 2H ≤ N+1`.
-/
theorem badset_card_le {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), MemRange N A → IsBad A →
      (A.card : ℝ) ≤ 5 / 8 * N + C := by
  obtain ⟨ C, hC ⟩ := badset_even hθ hc;
  use C + 5 / 8;
  intro N A hA hA'; specialize hC ( ( N + 1 ) / 2 ) A;
  exact le_trans ( hC ( fun x hx => hA x hx |> fun h => ⟨ h.1, by linarith [ Nat.div_add_mod ( N + 1 ) 2, Nat.mod_lt ( N + 1 ) two_pos, h.2 ] ⟩ ) hA' ) ( by linarith [ show ( ( N + 1 ) / 2 : ℕ ) ≤ ( N : ℝ ) / 2 + 1 / 2 by rw [ div_add_div, le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( N + 1 ) 2 ] ] )

/-
**Erdős 865 (conditional threshold form).** Conditional on the coarse theorem, there is
a constant `C` such that every `A ⊆ {1,…,N}` with `|A| ≥ (5/8)N + C` contains an admissible
triple.
-/
theorem erdos865 {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), MemRange N A →
      (5 / 8 * N + C ≤ (A.card : ℝ)) → HasTriple A := by
  by_contra! h_contra;
  obtain ⟨ C, hC ⟩ := badset_card_le hθ hc;
  exact absurd ( h_contra ( C + 1 ) ) ( by rintro ⟨ N, A, hA₁, hA₂, hA₃ ⟩ ; linarith [ hC N A hA₁ ( by unfold IsBad; aesop ) ] )

/-! ## Sharpness of the constant `5/8` -/

/-
**Sharpness.** For `N = 8k` (`k ≥ 1`), the set `[k,2k] ∪ [4k,8k] ⊆ {1,…,N}` is bad and
has `5k + 2 = (5/8)N + 2` elements.  Hence the constant `5/8` is best possible.
-/
theorem sharp (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : Finset ℕ, MemRange (8 * k) A ∧ IsBad A ∧ A.card = 5 * k + 2 := by
  refine' ⟨ Finset.Icc k ( 2 * k ) ∪ Finset.Icc ( 4 * k ) ( 8 * k ), _, _, _ ⟩;
  · exact fun x hx => by rcases Finset.mem_union.mp hx with ( hx | hx ) <;> constructor <;> linarith [ Finset.mem_Icc.mp hx ] ;
  · rintro ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, h₁, h₂, h₃ ⟩;
    grind;
  · rw [ Finset.card_union_of_disjoint ] <;> norm_num;
    · omega;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp hx₂ ] ;

end Erdos865