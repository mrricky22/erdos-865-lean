import RequestProject.Defs

set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset

namespace Erdos865

/-!
# Lemma 1 — the folded additive lemma

We prove: there is an absolute constant `K₁` such that for every `m ≥ 2` and every `B`
satisfying `FoldedOK m B`, one has `|B| − |C(B)| ≤ m/4 + K₁`.

The proof is by strong induction on `|B|`, using:
* `negSet` reflection symmetry to reduce to the case where the two smallest elements have
  sum `< m`;
* the four-set bound `four_set_bound` for the base case (the two smallest sum is not a
  collision);
* the deletion step `collisions_erase_lt` for the inductive case.
-/

/-- Reflection `B ↦ {m − b : b ∈ B}` modulo `m`. -/
noncomputable def negSet (m : ℕ) (B : Finset ℕ) : Finset ℕ := B.image (fun b => m - b)

/-
Reflection preserves the cardinality.
-/
theorem negSet_card (m : ℕ) (B : Finset ℕ) (hB : FoldedOK m B) :
    (negSet m B).card = B.card := by
  exact Finset.card_image_of_injOn fun x hx y hy hxy => by have := hB.1 x hx; have := hB.1 y hy; omega;

/-
Reflection preserves the `FoldedOK` hypothesis.
-/
theorem negSet_foldedOK (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    FoldedOK m (negSet m B) := by
  constructor <;> intro x hx <;> simp_all +decide [ negSet ];
  · rcases hx with ⟨ a, ha, rfl ⟩ ; exact ⟨ Nat.sub_pos_of_lt ( hB.1 a ha |>.2 ), Nat.sub_lt ( by linarith ) ( hB.1 a ha |>.1 ) ⟩ ;
  · obtain ⟨ a, ha, rfl ⟩ := hx; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    intro b hb hab;
    have h_mod : (m - a + (m - b)) % m = (2 * m - (a + b)) % m := by
      rw [ show 2 * m - ( a + b ) = m - a + ( m - b ) by rw [ two_mul, tsub_add_tsub_comm ] <;> linarith [ hB.1 a ha, hB.1 b hb ] ];
    have h_mod : (2 * m - (a + b)) % m = (m - (a + b) % m) % m := by
      zify;
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ two_mul, Int.add_emod, Int.sub_emod ];
      · exact Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) );
      · linarith [ hB.1 a ha, hB.1 b hb ];
    have h_mod : (m - (a + b) % m) % m = m - (a + b) % m := by
      rw [ Nat.mod_eq_of_lt ];
      exact Nat.sub_lt ( by linarith ) ( Nat.pos_of_ne_zero fun h => by have := hB.2 a ha b hb ( by aesop ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] );
    have := hB.2 a ha b hb ( by aesop ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    exact ⟨ Nat.sub_ne_zero_of_lt ( Nat.mod_lt _ ( by linarith ) ), fun x hx hx' => this.2 <| by convert hx using 1; rw [ tsub_right_inj ] at hx' <;> linarith [ Nat.mod_lt ( a + b ) ( by linarith : 0 < m ), hB.1 x hx, hB.1 a ha, hB.1 b hb ] ⟩

/-
Low sums of the reflection are the reflected high sums.
-/
theorem lowSums_negSet (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    lowSums m (negSet m B) = (highSums m B).image (fun r => m - r) := by
  ext r; simp [lowSums, highSums, negSet];
  constructor <;> rintro ⟨ a, b, h, rfl ⟩ <;> use a, b <;> simp_all +decide [ Nat.sub_sub ];
  · have := hB.1 a h.1.2; have := hB.1 b h.1.1; omega;
  · have := hB.1 a h.1.1; have := hB.1 b h.1.2; omega;

/-
High sums of the reflection are the reflected low sums.
-/
theorem highSums_negSet (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    highSums m (negSet m B) = (lowSums m B).image (fun r => m - r) := by
  ext r;
  simp +zetaDelta at *;
  constructor <;> intro hr;
  · obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hr;
    obtain ⟨ x, hx, hx' ⟩ := Finset.mem_image.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.1 ) ; obtain ⟨ y, hy, hy' ⟩ := Finset.mem_image.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.2 ) ; use x + y; simp_all +decide [ lowSums ] ;
    exact ⟨ ⟨ y, x, ⟨ ⟨ hy, hx ⟩, by omega, by omega ⟩, by ring ⟩, by omega ⟩;
  · rcases hr with ⟨ r, hr, rfl ⟩ ; unfold lowSums highSums negSet at *; simp_all +decide [ Finset.mem_image ] ;
    grind

/-
Reflection preserves the number of collisions.
-/
theorem negSet_collisions_card (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    (collisions m (negSet m B)).card = (collisions m B).card := by
  -- By definition of `collisions`, we have:
  have h_collisions : collisions m (negSet m B) = (collisions m B).image (fun r => m - r) := by
    ext; simp [collisions, lowSums_negSet, highSums_negSet];
    constructor <;> intro h <;> simp_all +decide [ lowSums_negSet, highSums_negSet ];
    · rcases h with ⟨ ⟨ a, ha, rfl ⟩, ⟨ b, hb, hab ⟩ ⟩ ; use b; simp_all +decide [ Nat.sub_eq_iff_eq_add ] ;
      convert ha using 1;
      unfold lowSums highSums at *; simp_all +decide [ Finset.mem_image ] ;
      grind;
    · grind;
  rw [ h_collisions, Finset.card_image_of_injOn ];
  intro x hx y hy; rw [ tsub_right_inj ] <;> norm_num at *;
  · exact Finset.mem_inter.mp hx |>.1 |> fun h => Finset.mem_image.mp h |> fun ⟨ p, hp₁, hp₂ ⟩ => by linarith [ Finset.mem_filter.mp hp₁ |>.2.2 ] ;
  · unfold collisions at hx hy; simp_all +decide [ lowSums, highSums ] ;
    grind

/-
Erasing an element preserves the `FoldedOK` hypothesis.
-/
theorem FoldedOK_erase (m : ℕ) (B : Finset ℕ) (a : ℕ) (hB : FoldedOK m B) :
    FoldedOK m (B.erase a) := by
  simp_all +decide [ FoldedOK ]

/-
A four-set Bonferroni inequality: the sum of the cardinalities is at most the cardinality
of the union plus the sum of the six pairwise intersection cardinalities.
-/
theorem card_sum_le_union_add_pairwise {α : Type*} [DecidableEq α]
    (T1 T2 T3 T4 : Finset α) :
    T1.card + T2.card + T3.card + T4.card ≤
      (T1 ∪ T2 ∪ T3 ∪ T4).card +
        ((T1 ∩ T2).card + (T1 ∩ T3).card + (T1 ∩ T4).card +
          (T2 ∩ T3).card + (T2 ∩ T4).card + (T3 ∩ T4).card) := by
  simp +arith +decide [ ← add_assoc, Finset.card_union_add_card_inter ];
  rw [ Finset.card_union, Finset.card_union, Finset.card_union ];
  rw [ show T2 ∩ ( T3 ∪ T4 ) = ( T2 ∩ T3 ) ∪ ( T2 ∩ T4 ) by rw [ Finset.inter_union_distrib_left ], show T1 ∩ ( T2 ∪ ( T3 ∪ T4 ) ) = ( T1 ∩ T2 ) ∪ ( T1 ∩ ( T3 ∪ T4 ) ) by rw [ Finset.inter_union_distrib_left ], show T1 ∩ ( T3 ∪ T4 ) = ( T1 ∩ T3 ) ∪ ( T1 ∩ T4 ) by rw [ Finset.inter_union_distrib_left ] ];
  grind

/-! ### The four sets in `ZMod m` for the four-set bound -/

/-- `T1 = {x : x ∈ B}` in `ZMod m`. -/
noncomputable def fsT1 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  B.image (fun x : ℕ => (x : ZMod m))
/-- `T2 = {-x : x ∈ B}` in `ZMod m`. -/
noncomputable def fsT2 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  B.image (fun x : ℕ => -(x : ZMod m))
/-- `T3 = {x - a : x ∈ B} \ {0}` in `ZMod m`. -/
noncomputable def fsT3 (m a : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  (B.image (fun x : ℕ => (x : ZMod m) - (a : ZMod m))).erase 0
/-- `T4 = {b - x : x ∈ B} \ {0}` in `ZMod m`. -/
noncomputable def fsT4 (m b : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  (B.image (fun x : ℕ => (b : ZMod m) - (x : ZMod m))).erase 0

/-
In the cyclic group `ZMod m`, the equation `t + t = w` has at most two solutions among
the (distinct) residues of `B`.
-/
theorem card_two_mul_fiber_le (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hBlt : ∀ x ∈ B, x < m)
    (w : ZMod m) :
    (B.filter (fun x : ℕ => (x : ZMod m) + (x : ZMod m) = w)).card ≤ 2 := by
  by_contra! h_contra;
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hxz⟩ : ∃ x y z : ℕ, x ∈ B ∧ y ∈ B ∧ z ∈ B ∧ x < m ∧ y < m ∧ z < m ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (x : ZMod m) + (x : ZMod m) = w ∧ (y : ZMod m) + (y : ZMod m) = w ∧ (z : ZMod m) + (z : ZMod m) = w := by
    rcases Finset.two_lt_card.mp h_contra with ⟨ x, hx, y, hy, hxy ⟩ ; use x, y ; aesop;
  have h_diff : (x - y : ZMod m) + (x - y : ZMod m) = 0 ∧ (x - z : ZMod m) + (x - z : ZMod m) = 0 ∧ (y - z : ZMod m) + (y - z : ZMod m) = 0 := by
    grind;
  have h_diff_ne_zero : (x - y : ZMod m) ≠ 0 ∧ (x - z : ZMod m) ≠ 0 ∧ (y - z : ZMod m) ≠ 0 := by
    simp_all +decide [ sub_eq_iff_eq_add ];
    exact ⟨ by rw [ ZMod.natCast_eq_natCast_iff ] ; exact fun h => hxz.1 <| Nat.mod_eq_of_lt ( hBlt x hx ) ▸ Nat.mod_eq_of_lt ( hBlt y hy ) ▸ h, by rw [ ZMod.natCast_eq_natCast_iff ] ; exact fun h => hxz.2.1 <| Nat.mod_eq_of_lt ( hBlt x hx ) ▸ Nat.mod_eq_of_lt ( hBlt z hz ) ▸ h, by rw [ ZMod.natCast_eq_natCast_iff ] ; exact fun h => hxz.2.2.1 <| Nat.mod_eq_of_lt ( hBlt y hy ) ▸ Nat.mod_eq_of_lt ( hBlt z hz ) ▸ h ⟩;
  have h_diff_eq : (x - y : ZMod m) = (x - z : ZMod m) := by
    have h_diff_eq : ∀ (u v : ZMod m), u + u = 0 → v + v = 0 → u ≠ 0 → v ≠ 0 → u = v := by
      intros u v hu hv hu_ne hv_ne
      have h_two_torsion : ∀ u : ZMod m, u + u = 0 → u ≠ 0 → u = (m / 2 : ℕ) := by
        intro u hu hu_ne
        have h_two_torsion : 2 * u.val = m := by
          have h_two_torsion : 2 * u.val ≡ 0 [MOD m] := by
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, two_mul ];
            cases m <;> aesop;
          obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp h_two_torsion;
          rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.ModEq ];
          haveI := Fact.mk ( by linarith : 1 < m ) ; exact absurd hk ( by nlinarith [ show u.val < m from u.val_lt ] ) ;
        norm_num [ ← h_two_torsion, Nat.mul_div_cancel_left _ ( by decide : 0 < 2 ) ];
        cases m <;> aesop;
      rw [ h_two_torsion u hu hu_ne, h_two_torsion v hv hv_ne ];
    exact h_diff_eq _ _ h_diff.1 h_diff.2.1 h_diff_ne_zero.1 h_diff_ne_zero.2.1;
  simp_all +decide [ sub_eq_sub_iff_add_eq_add ]

/-
In `ZMod m`, there is at most one nonzero element of order dividing two.
-/
theorem two_torsion_eq (m : ℕ) (u v : ZMod m) (hu : u + u = 0) (hv : v + v = 0)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : u = v := by
  rcases m with ( _ | _ | m ) <;> simp_all +decide [ ← two_mul ];
  · fin_cases u ; fin_cases v ; trivial;
  · have h_eq : 2 * u.val = m + 2 ∧ 2 * v.val = m + 2 := by
      have h_eq : 2 * u.val ≡ 0 [MOD (m + 2)] ∧ 2 * v.val ≡ 0 [MOD (m + 2)] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      have h_eq : u.val < m + 2 ∧ v.val < m + 2 := by
        exact ⟨ u.val_lt, v.val_lt ⟩;
      have h_eq : u.val ≠ 0 ∧ v.val ≠ 0 := by
        exact ⟨ by contrapose! hu0; exact Fin.ext hu0, by contrapose! hv0; exact Fin.ext hv0 ⟩;
      exact ⟨ by obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp ( by tauto : 2 * u.val ≡ 0 [MOD m + 2] ) ; nlinarith [ show k = 1 by nlinarith [ Nat.pos_of_ne_zero h_eq.1 ] ], by obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp ( by tauto : 2 * v.val ≡ 0 [MOD m + 2] ) ; nlinarith [ show k = 1 by nlinarith [ Nat.pos_of_ne_zero h_eq.2 ] ] ⟩;
    exact ZMod.val_injective _ ( by linarith )

/-
`|T1| = |B|`.
-/
theorem fsT1_card (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) :
    (fsT1 m B).card = B.card := by
  apply Finset.card_image_of_injOn;
  intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h

/-
`|T2| = |B|`.
-/
theorem fsT2_card (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) :
    (fsT2 m B).card = B.card := by
  apply Finset.card_image_of_injOn; intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h

/-
`|T3| = |B| - 1`.
-/
theorem fsT3_card (m a : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (haB : a ∈ B) :
    (fsT3 m a B).card = B.card - 1 := by
  -- The function x ↦ (x: ZMod m) - (a: ZMod m) is injective on B since B is a subset of {1, ..., m-1}.
  have h_inj : (B.image (fun x : ℕ => (x : ZMod m) - (a : ZMod m))).card = B.card := by
    rw [ Finset.card_image_of_injOn ];
    intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ sub_eq_iff_eq_add, ZMod.natCast_eq_natCast_iff' ] ;
    exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h;
  rw [ ← h_inj, fsT3, Finset.card_erase_of_mem ] ; aesop

/-
`|T4| = |B| - 1`.
-/
theorem fsT4_card (m b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (hbB : b ∈ B) :
    (fsT4 m b B).card = B.card - 1 := by
  erw [ Finset.card_erase_of_mem, Finset.card_image_of_injOn ];
  · intro x hx y hy; simp_all +decide [ sub_eq_sub_iff_add_eq_add, ZMod.natCast_eq_natCast_iff' ] ;
    exact fun h => Nat.mod_eq_of_lt ( hB.1 x hx |>.2 ) ▸ Nat.mod_eq_of_lt ( hB.1 y hy |>.2 ) ▸ h;
  · exact Finset.mem_image.mpr ⟨ b, hbB, by simp +decide ⟩

/-
`|T1 ∩ T2| ≤ 1`.
-/
theorem fsT1T2_le (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) :
    (fsT1 m B ∩ fsT2 m B).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_;
  intros a ha b hb
  have h_torsion : a + a = 0 ∧ a ≠ 0 ∧ b + b = 0 ∧ b ≠ 0 := by
    have h_torsion : ∀ x ∈ B, ∀ y ∈ B, (x : ZMod m) = -(y : ZMod m) → x = y ∧ 2 * (x : ZMod m) = 0 ∧ (x : ZMod m) ≠ 0 := by
      intros x hx y hy hxy
      have h_eq : x + y ≡ 0 [MOD m] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
      have h_ne : x ≠ y → ¬(m ∣ (x + y)) := by
        exact fun h => hB.2 x hx y hy h |>.1
      have h_eq' : x = y := by
        exact Classical.not_not.1 fun h => h_ne h <| Nat.dvd_of_mod_eq_zero h_eq
      have h_torsion : 2 * (x : ZMod m) = 0 := by
        grind
      have h_nonzero : (x : ZMod m) ≠ 0 := by
        rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( hB.1 x hx |>.1 ) ( hB.1 x hx |>.2 )
      exact ⟨h_eq', h_torsion, h_nonzero⟩;
    simp_all +decide [ fsT1, fsT2 ];
    grind;
  exact two_torsion_eq m a b h_torsion.1 h_torsion.2.2.1 h_torsion.2.1 h_torsion.2.2.2

/-
`|T1 ∩ T3| ≤ 1`.
-/
theorem fsT1T3_le (m a : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (haB : a ∈ B) :
    (fsT1 m B ∩ fsT3 m a B).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_;
  simp +zetaDelta at *;
  intros x hx hx' y hy hy'
  obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ B, (x' : ZMod m) = x := by
    unfold fsT1 at hx; aesop;
  obtain ⟨y', hy', hy''⟩ : ∃ y' ∈ B, (y' : ZMod m) - (a : ZMod m) = x := by
    unfold fsT3 at *; aesop;
  obtain ⟨z', hz', hz''⟩ : ∃ z' ∈ B, (z' : ZMod m) = y := by
    unfold fsT1 at hy; aesop;
  obtain ⟨w', hw', hw''⟩ : ∃ w' ∈ B, (w' : ZMod m) - (a : ZMod m) = y := by
    unfold fsT3 at *; aesop;
  have h_eq : (x' + a) % m = y' ∧ (z' + a) % m = w' := by
    simp_all +decide [ sub_eq_iff_eq_add, ← ZMod.val_natCast ];
    rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod.val_natCast ];
    exact ⟨ by rw [ ← hy'', ZMod.val_cast_of_lt ( show y' < m + 1 + 1 from by linarith [ hB.1 y' ‹_› ] ) ], by rw [ ← hw'', ZMod.val_cast_of_lt ( show w' < m + 1 + 1 from by linarith [ hB.1 w' ‹_› ] ) ] ⟩;
  have := hB.2 x' hx' a haB; have := hB.2 z' hz' a haB; simp_all +decide [ Nat.mod_eq_of_lt ] ;

/-
`|T1 ∩ T4| ≤ 2`.
-/
theorem fsT1T4_le (m b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (hbB : b ∈ B) :
    (fsT1 m B ∩ fsT4 m b B).card ≤ 2 := by
  -- Show that $T1 \cap T4 \subseteq \{ x \in B : x + x \equiv b \pmod{m} \}$.
  have h_subset : fsT1 m B ∩ fsT4 m b B ⊆ (Finset.image (fun x : ℕ => (x : ZMod m)) (B.filter (fun x : ℕ => (x : ZMod m) + (x : ZMod m) = (b : ZMod m)))) := by
    intro x hx; simp_all +decide [ Finset.subset_iff ] ;
    obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx.1; use a; simp_all +decide [ fsT4 ] ;
    obtain ⟨ c, hc, h ⟩ := hx.2.2; have := hB.2 a ha c hc; simp_all +decide [ sub_eq_iff_eq_add ] ;
    by_cases hac : a = c <;> simp_all +decide [ ← ZMod.val_natCast ];
    simp_all +decide [ ← h, ZMod.val_natCast ];
    exact False.elim <| this.2 <| by simpa [ Nat.mod_eq_of_lt ( show b < m from hB.1 b hbB |>.2 ) ] using hbB;
  exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( card_two_mul_fiber_le m hm B ( fun x hx => by linarith [ hB.1 x hx ] ) _ ) )

/-
`|T2 ∩ T3| ≤ 2`.
-/
theorem fsT2T3_le (m a : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (haB : a ∈ B) :
    (fsT2 m B ∩ fsT3 m a B).card ≤ 2 := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image ( fun x : ℕ => - ( x : ZMod m ) ) ( B.filter ( fun x : ℕ => ( x : ZMod m ) + ( x : ZMod m ) = ( a : ZMod m ) ) );
  · intro z hz;
    obtain ⟨x, hx, hx'⟩ : ∃ x ∈ B, z = -(x : ZMod m) := by
      unfold fsT2 at hz; aesop;
    obtain ⟨y, hy, hy'⟩ : ∃ y ∈ B, z = (y : ZMod m) - (a : ZMod m) ∧ z ≠ 0 := by
      grind +locals;
    by_cases hxy : x = y;
    · grind +qlia;
    · have h_contradiction : (x + y) % m = a := by
        haveI := Fact.mk ( by linarith : 1 < m ) ; simp_all +decide [ ← ZMod.val_natCast, Nat.add_mod ] ;
        rw [ show ( x + y : ZMod m ) = a by linear_combination' hx' ] ; rw [ ZMod.val_cast_of_lt ] ; linarith [ hB.1 a haB ] ;
      have := hB.2 x hx y hy hxy; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  · refine' le_trans ( Finset.card_image_le ) _;
    convert card_two_mul_fiber_le m hm B ( fun x hx => by linarith [ hB.1 x hx ] ) ( a : ZMod m ) using 1

/-
`|T2 ∩ T4| ≤ 1`.
-/
theorem fsT2T4_le (m b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (hbB : b ∈ B) :
    (fsT2 m B ∩ fsT4 m b B).card ≤ 1 := by
  have h_eq : ∀ z ∈ fsT2 m B ∩ fsT4 m b B, z = -(b : ZMod m) := by
    intro z hz
    obtain ⟨x, hx⟩ : ∃ x ∈ B, z = -(x : ZMod m) := by
      unfold fsT2 at hz; aesop;
    obtain ⟨y, hy⟩ : ∃ y ∈ B, z = (b : ZMod m) - (y : ZMod m) := by
      grind +locals
    have hxy : (x + b) % m = y := by
      have hxy : (x + b : ZMod m) = y := by
        grind +ring;
      haveI := Fact.mk ( by linarith : 1 < m ) ; simp_all +decide [ ← ZMod.val_natCast ] ;
      exact ZMod.val_cast_of_lt ( by linarith [ hB.1 y hy.1 ] )
    by_cases hxb : x = b;
    · grind;
    · have := hB.2 x hx.1 b hbB hxb; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  exact Finset.card_le_one.mpr fun x hx y hy => h_eq x hx ▸ h_eq y hy ▸ rfl

/-
`|T3 ∩ T4| ≤ 3`.
-/
theorem fsT3T4_le (m a b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B)
    (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x)
    (hlt : a + b < m) (hnc : a + b ∉ collisions m B) :
    (fsT3 m a B ∩ fsT4 m b B).card ≤ 3 := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact { ( b : ZMod m ) - ( a : ZMod m ) } ∪ Finset.image ( fun x : ℕ => ( x : ZMod m ) - ( a : ZMod m ) ) ( Finset.filter ( fun x : ℕ => ( x : ZMod m ) + ( x : ZMod m ) = ( a : ZMod m ) + ( b : ZMod m ) ) B );
  · intro z hz
    simp [fsT3, fsT4] at hz;
    obtain ⟨ ⟨ x, hx, hx' ⟩, hz', ⟨ y, hy, hy' ⟩ ⟩ := hz; simp_all +decide [ sub_eq_iff_eq_add ] ;
    -- Since $x + y \equiv a + b \pmod{m}$, we have $x + y = a + b$ or $x + y = a + b + m$.
    have hxy : x + y = a + b ∨ x + y = a + b + m := by
      have hxy : (x + y : ℤ) ≡ (a + b : ℤ) [ZMOD m] := by
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        ring;
      obtain ⟨ k, hk ⟩ := hxy.symm.dvd;
      rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> first | left; nlinarith | skip;
      exact Or.inr ( by nlinarith [ show k = 1 by nlinarith [ hB.1 x hx, hB.1 y hy ] ] );
    cases hxy <;> simp_all +decide [ ← eq_sub_iff_add_eq' ];
    · grind;
    · -- Since $x + y = a + b + m$, we have $x = y$.
      have hxy_eq : x = y := by
        contrapose! hnc;
        refine' Finset.mem_inter.mpr ⟨ _, _ ⟩;
        · exact Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ haB, hbB ⟩, by linarith, by linarith ⟩, by ring ⟩;
        · refine' Finset.mem_image.mpr ⟨ ( if x < y then ( x, y ) else ( y, x ) ), _, _ ⟩ <;> split_ifs <;> simp_all +decide [ add_comm ];
          · exact Or.inr ( by linarith );
          · exact ⟨ lt_of_le_of_ne ‹_› ( Ne.symm hnc ), Or.inl ( by linarith [ hB.1 a haB ] ) ⟩;
      grind;
  · refine' le_trans ( Finset.card_union_le _ _ ) _;
    refine' le_trans ( add_le_add ( Finset.card_singleton _ |> le_of_eq ) ( Finset.card_image_le ) ) _;
    have := card_two_mul_fiber_le m hm B ( fun x hx => by linarith [ hB.1 x hx ] ) ( a + b : ZMod m ) ; simp_all +decide [ ← two_mul ] ;
    linarith

/-
**Case 2 (four-set bound).** If the two smallest elements `a < b` of `B` have
`a + b < m` and `a + b` is *not* a collision, then `|B| ≤ m/4 + 3`.
-/
theorem four_set_bound (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B)
    (a b : ℕ) (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x)
    (hlt : a + b < m) (hnc : a + b ∉ collisions m B) :
    (B.card : ℝ) ≤ (m : ℝ) / 4 + 3 := by
  rw [ div_add', le_div_iff₀ ] <;> norm_cast;
  have h_four_set : (fsT1 m B).card + (fsT2 m B).card + (fsT3 m a B).card + (fsT4 m b B).card ≤ m + 10 := by
    -- By the four-set bound, we have:
    have h_four_set_bound : (fsT1 m B ∪ fsT2 m B ∪ fsT3 m a B ∪ fsT4 m b B).card ≤ m := by
      cases m <;> [ aesop; exact le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ];
    have := card_sum_le_union_add_pairwise ( fsT1 m B ) ( fsT2 m B ) ( fsT3 m a B ) ( fsT4 m b B );
    linarith [ fsT1T2_le m hm B hB, fsT1T3_le m a hm B hB haB, fsT1T4_le m b hm B hB hbB, fsT2T3_le m a hm B hB haB, fsT2T4_le m b hm B hB hbB, fsT3T4_le m a b hm B hB haB hbB hab hmin h2nd hlt hnc ];
  linarith [ fsT1_card m hm B hB, fsT2_card m hm B hB, fsT3_card m a hm B hB haB, fsT4_card m b hm B hB hbB, Nat.sub_add_cancel ( show 1 ≤ B.card from Finset.card_pos.mpr ⟨ a, haB ⟩ ) ]

/-
**Case 1 (deletion step).** If the two smallest elements `a < b` of `B` have
`a + b < m` and `a + b` *is* a collision, then deleting `a` strictly decreases the number of
collisions.
-/
theorem collisions_erase_lt (m : ℕ) (B : Finset ℕ) (hB : FoldedOK m B)
    (a b : ℕ) (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x)
    (hlt : a + b < m) (hc : a + b ∈ collisions m B) :
    (collisions m (B.erase a)).card < (collisions m B).card := by
  refine' Finset.card_lt_card _;
  constructor;
  · exact Finset.inter_subset_inter ( Finset.image_subset_image <| Finset.filter_subset_filter _ <| Finset.product_subset_product ( Finset.erase_subset _ _ ) ( Finset.erase_subset _ _ ) ) ( Finset.image_subset_image <| Finset.filter_subset_filter _ <| Finset.product_subset_product ( Finset.erase_subset _ _ ) ( Finset.erase_subset _ _ ) );
  · simp_all +decide [ Finset.subset_iff, collisions ];
    use a + b; simp_all +decide [ lowSums, highSums ] ;
    grind

/-
One induction step: given the two smallest elements `a < b` with `a + b < m` and the
induction hypothesis for all strictly smaller sets (same `m`), the bound holds for `B`.
-/
theorem lemma1_step (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B)
    (IH : ∀ B' : Finset ℕ, B'.card < B.card → FoldedOK m B' →
          (B'.card : ℝ) - (collisions m B').card ≤ (m : ℝ) / 4 + 3)
    (a b : ℕ) (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x) (hlt : a + b < m) :
    (B.card : ℝ) - (collisions m B).card ≤ (m : ℝ) / 4 + 3 := by
  by_cases h : a + b ∈ collisions m B;
  · have := IH ( B.erase a ) ?_ ?_;
    · rw [ Finset.card_erase_of_mem haB ] at this;
      rw [ Nat.cast_pred ( Finset.card_pos.mpr ⟨ a, haB ⟩ ) ] at this;
      linarith [ show ( collisions m B |> Finset.card : ℝ ) ≥ ( collisions m ( B.erase a ) |> Finset.card : ℝ ) + 1 by exact_mod_cast collisions_erase_lt m B hB a b haB hbB hab hmin h2nd hlt h ];
    · exact Finset.card_lt_card ( Finset.erase_ssubset haB );
    · exact FoldedOK_erase m B a hB;
  · exact le_trans ( sub_le_self _ <| Nat.cast_nonneg _ ) ( four_set_bound m B hm hB a b haB hbB hab hmin h2nd hlt h )

/-
**Lemma 1.** There is an absolute constant `K₁` such that for every `m ≥ 2` and every
`B` satisfying `FoldedOK m B`, one has `|B| − |C(B)| ≤ m/4 + K₁`.
-/
theorem lemma1 :
    ∃ K1 : ℝ, ∀ (m : ℕ) (B : Finset ℕ), 2 ≤ m → FoldedOK m B →
      (B.card : ℝ) - (collisions m B).card ≤ (m : ℝ) / 4 + K1 := by
  use 3;
  have h_ind : ∀ n : ℕ, ∀ m : ℕ, 2 ≤ m → ∀ B : Finset ℕ, B.card = n → FoldedOK m B → (B.card : ℝ) - (collisions m B).card ≤ (m : ℝ) / 4 + 3 := by
    intro n;
    induction' n using Nat.strong_induction_on with n ih;
    intro m hm B hB_card hB_foldedOK
    by_cases hB_card_le_1 : B.card ≤ 1;
    · interval_cases _ : #B <;> norm_num at *;
      · exact le_trans ( neg_nonpos_of_nonneg ( Nat.cast_nonneg _ ) ) ( by positivity );
      · grind +qlia;
    · obtain ⟨a, b, haB, hbB, hab, hmin, h2nd⟩ : ∃ a b : ℕ, a ∈ B ∧ b ∈ B ∧ a < b ∧ (∀ x ∈ B, a ≤ x) ∧ (∀ x ∈ B, x ≠ a → b ≤ x) := by
        obtain ⟨a, haB⟩ : ∃ a : ℕ, a ∈ B ∧ ∀ x ∈ B, a ≤ x := by
          exact ⟨ Nat.find <| Finset.card_pos.mp <| by linarith, Nat.find_spec <| Finset.card_pos.mp <| by linarith, fun x hx => Nat.find_min' _ hx ⟩;
        obtain ⟨b, hbB, hb_min⟩ : ∃ b : ℕ, b ∈ B ∧ b ≠ a ∧ ∀ x ∈ B, x ≠ a → b ≤ x := by
          exact ⟨ Nat.find ( Finset.exists_mem_ne ( by linarith ) a ), Nat.find_spec ( Finset.exists_mem_ne ( by linarith ) a ) |>.1, Nat.find_spec ( Finset.exists_mem_ne ( by linarith ) a ) |>.2, fun x hx hx' => Nat.find_min' ( Finset.exists_mem_ne ( by linarith ) a ) ⟨ hx, hx' ⟩ ⟩;
        exact ⟨ a, b, haB.1, hbB, lt_of_le_of_ne ( haB.2 b hbB ) ( Ne.symm hb_min.1 ), haB.2, hb_min.2 ⟩;
      by_cases hlt : a + b < m;
      · apply lemma1_step m B hm hB_foldedOK (fun B' hB'_card hB'_foldedOK => ih B'.card (by
        linarith) m hm B' rfl hB'_foldedOK) a b haB hbB hab hmin h2nd hlt;
      · -- Let $u := B.max'$ and $v := (B.erase u).max'$ (the two largest of $B$), so $v < u$, $u,v \in B$.
        obtain ⟨u, huB, hu_max⟩ : ∃ u ∈ B, ∀ x ∈ B, x ≤ u := by
          exact ⟨ Finset.max' B ⟨ a, haB ⟩, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
        obtain ⟨v, hvB, hv_max⟩ : ∃ v ∈ B, v ≠ u ∧ ∀ x ∈ B, x ≠ u → x ≤ v := by
          obtain ⟨v, hvB, hv_max⟩ : ∃ v ∈ B, v ≠ u := by
            exact Finset.exists_mem_ne ( by linarith ) u;
          exact ⟨ Finset.max' ( B.filter fun x => x ≠ u ) ⟨ v, by aesop ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( B.filter fun x => x ≠ u ) ⟨ v, by aesop ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( B.filter fun x => x ≠ u ) ⟨ v, by aesop ⟩ ) |>.2, fun x hx hx' => Finset.le_max' _ _ ( by aesop ) ⟩
        have hv_lt_u : v < u := by
          exact lt_of_le_of_ne ( hu_max v hvB ) hv_max.1
        have hu_v_ge_m : u + v ≥ m := by
          grind
        have hu_v_ne_m : u + v ≠ m := by
          intro h; have := hB_foldedOK.2 u huB v hvB; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
        have hu_v_gt_m : u + v > m := by
          exact lt_of_le_of_ne hu_v_ge_m hu_v_ne_m.symm;
        -- The two smallest elements of $B'$ are $a' := m - u$ and $b' := m - v$, with $a' < b'$ (since $v < u$), $a', b' \in B'$.
        set a' := m - u
        set b' := m - v
        have ha'_B' : a' ∈ negSet m B := by
          exact Finset.mem_image.mpr ⟨ u, huB, rfl ⟩
        have hb'_B' : b' ∈ negSet m B := by
          exact Finset.mem_image.mpr ⟨ v, hvB, rfl ⟩
        have ha'_lt_b' : a' < b' := by
          exact Nat.sub_lt_sub_left ( by linarith [ hB_foldedOK.1 u huB, hB_foldedOK.1 v hvB ] ) hv_lt_u
        have ha'_min : ∀ x ∈ negSet m B, a' ≤ x := by
          simp +zetaDelta at *;
          intro x hx; obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; linarith [ hu_max y hy, Nat.sub_add_cancel ( show y ≤ m from by linarith [ hB_foldedOK.1 y hy ] ) ] ;
        have hb'_2nd : ∀ x ∈ negSet m B, x ≠ a' → b' ≤ x := by
          intros x hx hx_ne_a'
          obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, x = m - y := by
            unfold negSet at hx; aesop;
          grind
        have ha'_b'_lt_m : a' + b' < m := by
          rw [ tsub_add_tsub_comm ] <;> try linarith [ hB_foldedOK.1 u huB, hB_foldedOK.1 v hvB ];
          lia;
        -- Apply `lemma1_step` to $B'$.
        have hB'_step : (negSet m B).card - (collisions m (negSet m B)).card ≤ (m : ℝ) / 4 + 3 := by
          apply lemma1_step m (negSet m B) hm (negSet_foldedOK m B hm hB_foldedOK) (fun B' hB'_card hB'_foldedOK => by
            convert ih _ _ _ hm _ rfl hB'_foldedOK using 1;
            exact hB'_card.trans_le ( by rw [ negSet_card m B hB_foldedOK ] ; linarith )) a' b' ha'_B' hb'_B' ha'_lt_b' ha'_min hb'_2nd ha'_b'_lt_m;
        convert hB'_step using 1;
        rw [ negSet_card m B hB_foldedOK, negSet_collisions_card m B hm hB_foldedOK ];
  exact fun m B hm hB => h_ind _ _ hm _ rfl hB

end Erdos865