import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.GroupAction.Basic

#check MulAction
#check MulAction.orbit
#check MulAction.stabilizer
#check Nat.card_congr

abbrev X  (G: Type) [Group G] (p n : Nat )  :=
{P : Set   G // Nat.card P = p ^ n}

def leftMulEquiv (G : Type) [Group G] (g : G) : G ≃ G where
  toFun := fun x => g * x
  invFun := fun x => g⁻¹ * x
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp

def imageEquiv {α β : Type} (e : α ≃ β) (S : Set α) :
    S ≃ e '' S where
  toFun x := ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨e.symm y.1, by
    rcases y.2 with ⟨x, hx, hxy⟩
    change e x = y.1 at hxy
    rw [← hxy]
    rw [e.symm_apply_apply]
    exact hx
  ⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro y
    apply Subtype.ext
    simp

instance instMulActionX (G : Type) [Group G] (p n : Nat) :
    MulAction G (X G p n) where

  smul := fun g S =>
    ⟨(fun x : G => g * x) '' S.1, by
      exact (Nat.card_congr (imageEquiv (leftMulEquiv G g) S.1)).symm.trans S.2
    ⟩

  one_smul := by
    intro S
    apply Subtype.ext
    ext x
    change x ∈ (fun y : G => (1 : G) * y) '' S.1 ↔ x ∈ S.1
    simp

  mul_smul := by
    intro g h S
    apply Subtype.ext
    change (fun x : G => (g * h) * x) '' S.1 =
      (fun x : G => g * x) '' ((fun x : G => h * x) '' S.1)
    rw [Set.image_image]
    congr 1
    funext x
    simp [mul_assoc]




abbrev SylowSubgroups (G: Type) [Group G] (p n : Nat ) :=
 {P: Subgroup G // Nat.card P = p ^ n}

lemma p_does_not_divide_X (G: Type)[Group G] [Finite G]
(p n : Nat)
:  ¬ (p ∣ Nat.card (X G p n)) := by
  sorry

-- lemma X_equals_sum_of_orb_G (G: Type) [Group G] [Finite G]



theorem prop_3_5 (G: Type) [Group G] [Finite G] (p m n  : Nat)
(G_equals_pnm:  Nat.card G = m  * p ^ n   )
(pm_coprime : Nat.gcd p m = 1)
:
 Nat.card (SylowSubgroups G p n)  ≡ 1 [MOD p]  := by
    have h:= p_does_not_divide_X G p n
    -- X is the sum of orbit of S  Kevin
    -- claim 1 Daniel
    -- claim 2 Aryan
    -- conclusion Ed

    sorry


--
