import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-!
# Cardinality of `X`

Everything needed to prove `p_does_not_divide_X`, used in `Ludwig/Sylow1.lean`.
-/

--  difference it that this is any subset of G
abbrev X  (G: Type) [Group G] (p n : Nat )  :=
{P : Set   G // Nat.card P = p ^ n}

-- X but a FinSet, makes the below lot easier
noncomputable def FiniteX (G : Type) [Group G] [Fintype G] (p n : Nat) :
    X G p n ≃ {s : Finset G // s.card = p ^ n} := by
  classical
  exact
  { toFun := fun S => ⟨S.1.toFinset, by rw [← Nat.card_eq_card_toFinset]; exact S.2⟩
    invFun := fun s => ⟨(s.1 : Set G), by simpa using s.2⟩
    left_inv := fun S => Subtype.ext (by simp)
    right_inv := fun s => Subtype.ext (by simp) }


lemma card_X_equals_binomial (G:Type) [Group G][Finite G] (hG: Nat.card G = m * p ^ n):
Nat.card (X G p n) = Nat.choose (m * p ^ n) (p ^ n)
:= by
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_congr (FiniteX G p n), Nat.card_eq_fintype_card,
    Fintype.card_finset_len, ← Nat.card_eq_fintype_card, hG]

lemma lemma_3_4_ii (p n m : Nat) :
(Nat.choose (m * p ^ n) (p ^ n)) ≡ m [MOD p] := by


  sorry

lemma card_X_congruent_to_m_mod_p (G:Type) [Group G][Finite G] (hG: Nat.card G = m * p ^ n) :
 Nat.card (X G p n) ≡ m [MOD p] := by

    have h1 := card_X_equals_binomial G hG
    have h2 := lemma_3_4_ii p n m
    exact h1 ▸  h2

lemma p_does_not_divide_X (G: Type)[Group G] [Finite G]
(p n : Nat)
:  ¬ (p ∣ Nat.card (X G p n)) := by

  sorry
