import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.GCD

abbrev X  (G: Type) [Group G] (p n : Nat )  :=
{P : Set   G // Nat.card P = p ^ n}

abbrev SylowSubgroups (G: Type) [Group G] (p n : Nat ) :=
 {P: Subgroup G // Nat.card P = p ^ n}

lemma p_does_not_divide_X (G: Type)[Group G] [Finite G]
(p n : Nat)
:  ¬ (p ∣ Nat.card ( X G p n)) := by
  sorry


theorem prop_3_5 (G: Type) [Group G] [Finite G] (p m n  : Nat)
(G_equals_pnm:  Nat.card G = m  * p ^ n   )
(pm_coprime : Nat.gcd p m = 1)
:
 Nat.card (SylowSubgroups G p n)  ≡ 1 [MOD p]  := by
    have h:= p_does_not_divide_X G p n
    sorry
