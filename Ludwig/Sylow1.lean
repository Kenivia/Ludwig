import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic



private theorem finish_sylow_count {p m n : Nat}
    (hp : Nat.Prime p)
    (hm : ¬ (p ∣ m))
    (hcount : m ≡ m * n [MOD p]) :
    n ≡ 1 [MOD p] := by
  have hcoprime : Nat.Coprime p m :=
    hp.coprime_iff_not_dvd.mpr hm
  have hmul : m * n ≡ m * 1 [MOD p] := by
    simpa only [Nat.mul_one] using hcount.symm
  exact Nat.ModEq.cancel_left_of_coprime hcoprime hmul



theorem sylow_one (G : Type) [Group G] [Finite G]
    (p a m : Nat)
    (p_prime_divisor_G : p ∣ Nat.card G) [Fact p.Prime]
    (pa_divides_G : p ^ a ∣ Nat.card G)
    (hcard : Nat.card G = p ^ a * m)
    (hm : ¬ (p ∣ m)) :
    Nat.card {H : Subgroup G // Nat.card H = p ^ a} ≡ 1 [MOD p] := by
  let n := Nat.card {H : Subgroup G // Nat.card H = p ^ a}
  let total := Nat.choose (Nat.card G) (p ^ a)

  have hbinomial : total ≡ m [MOD p] := by
    -- Use hcard and Lemma 3.4(ii).
    sorry

  obtain ⟨good, bad, orbitSize, hgood, hbad, hnumber, htotal⟩ :
      ∃ (good bad : Finset Nat) (orbitSize : Nat → Nat),
        (∀ i ∈ good, orbitSize i = m) ∧
        (∀ i ∈ bad, p ∣ orbitSize i) ∧
        good.card = n ∧
        total = good.sum orbitSize + bad.sum orbitSize := by
    -- Establish the orbit partition, sizes, and correspondence.
    sorry

  have hgoodSum : good.sum orbitSize = m * n := by
    calc
      good.sum orbitSize = good.card * m := Finset.sum_const_nat hgood
      _ = n * m := by rw [hnumber]
      _ = m * n := Nat.mul_comm n m

  have hbadZero : bad.sum orbitSize ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (Finset.dvd_sum hbad)

  have horbit : total ≡ m * n [MOD p] := by
    rw [htotal, hgoodSum]
    simpa only [Nat.add_zero] using
      (Nat.ModEq.refl (m * n)).add hbadZero

  have hcount : m ≡ m * n [MOD p] := by
    have hmTotal : m ≡ total [MOD p] := hbinomial.symm
    exact hmTotal.trans horbit

  exact finish_sylow_count (Fact.out : Nat.Prime p) hm hcount

theorem sylow_exists_of_count (G : Type) [Group G] (p a : Nat)
  (hp : Nat.Prime p)
  (hcount : Nat.card {H : Subgroup G // Nat.card H = p ^ a} ≡ 1 [MOD p]) :
  ∃ H : Subgroup G, Nat.card H = p ^ a := by
  have hnonzero : Nat.card {H : Subgroup G // Nat.card H = p ^ a} ≠ 0 := by
    intro hzero
    rw [hzero] at hcount
    have hdiv : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp hcount.symm
    exact hp.not_dvd_one hdiv
  obtain ⟨P⟩ := (Nat.card_ne_zero.mp hnonzero).1
  exact ⟨P.val, P.property⟩
