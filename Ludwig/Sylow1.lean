import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.GCD
abbrev SylowSubgroups (G: Type) [Group G] (p n : Nat ) :=
 {P:Subgroup G // Nat.card P = p ^ n}

theorem prop_3_5 (G: Type) [Group G] [Finite G] (p m n  : Nat)
(G_equals_pnm:  Nat.card G = m  * p ^ n   )
(pm_coprime : Nat.gcd p m = 1)
:
 Nat.card (SylowSubgroups G p n)  ≡ 1 [MOD p]  := by
    sorry
