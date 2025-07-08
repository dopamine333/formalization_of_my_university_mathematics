-- This module serves as the root of the `Leantest4` library.
-- Import modules here that should be built as part of the library.

-- import Leantest4.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Nat.Gcd
import Init.Data.Nat.Dvd
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.IntervalCases

-- import mathlib.Analysis.Calculus.Deriv.MeanValue
-- #check exists_ratio_deriv_eq_ratio_slope

instance : Pow ℕ+ ℕ+ where
    pow a n := ⟨a.val ^ n.val, Nat.pow_pos a.pos⟩

instance : HDiv ℕ+ ℕ+ ℕ where
    hDiv a b := a.val / b.val

def Fermat (n a b c: ℕ+) : Prop := 2*a^n + 3*b^n = 4*c^n

-- def `if` : Nat := 5

def exists_abc (n : ℕ+) : Prop := ∃ (a b c : ℕ+), Fermat n a b c


def Putnam2025A1 : Prop := {n : ℕ+ | exists_abc n} = {1}

lemma n1_is_good : exists_abc 1 := by
    unfold exists_abc
    let a : ℕ+ := 1
    let b : ℕ+ := 2
    let c : ℕ+ := 2
    use a, b, c
    rfl

def only_1 : Prop := ∀ (n : ℕ+) (abc : exists_abc n), n = 1

theorem it_remains_to_show (deferred : only_1) : Putnam2025A1 := by
    unfold Putnam2025A1
    let good_n_set := {n : ℕ+ | exists_abc n}

    have super_step : good_n_set ⊇ {1} := by
        intro n inset1
        have is1 : n = 1 := Set.eq_of_mem_singleton inset1
        rw [is1]
        exact n1_is_good

    have subset_step : good_n_set ⊆ {1} := by
        intro n inset
        have isgood : exists_abc n := inset
        unfold only_1 at deferred
        exact deferred n isgood

    have equal_step : good_n_set = {1} :=
        Set.Subset.antisymm subset_step super_step

    exact equal_step

lemma can_assume_coprime (n a b c : ℕ+) (Feq : Fermat n a b c) :
    ∃ (d e f : ℕ+), Fermat n d e f ∧ (d.val.gcd e.val).gcd f.val = 1 := by

    let nn := n.val
    let aa := a.val
    let bb := b.val
    let cc := c.val
    let gg := aa.gcd bb
    let hh := gg.gcd cc

    have g.pos : 0 < gg := Nat.gcd_pos_of_pos_left bb a.pos
    have h.pos : 0 < hh := Nat.gcd_pos_of_pos_left cc g.pos
    have hdvdg : hh ∣ gg := Nat.gcd_dvd_left gg cc
    have hleg : hh ≤ gg := Nat.le_of_dvd g.pos hdvdg

    have gdvda : gg ∣ aa := Nat.gcd_dvd_left aa bb
    have hdvda : hh ∣ aa := Nat.dvd_trans hdvdg gdvda
    have gdvdb : gg ∣ bb := Nat.gcd_dvd_right aa bb
    have hdvdb : hh ∣ bb := Nat.dvd_trans hdvdg gdvdb
    have hdvdc : hh ∣ cc := Nat.gcd_dvd_right gg cc

    have hlea : hh ≤ aa := Nat.le_of_dvd a.pos hdvda
    have hleb : hh ≤ bb := Nat.le_of_dvd b.pos hdvdb
    have hlec : hh ≤ cc := Nat.gcd_le_right cc c.pos

    let dd : ℕ := aa / hh
    let ee : ℕ := bb / hh
    let ff : ℕ := cc / hh
    let d : ℕ+ := ⟨dd,  Nat.div_pos hlea h.pos⟩
    let e : ℕ+ := ⟨ee,  Nat.div_pos hleb h.pos⟩
    let f : ℕ+ := ⟨ff,  Nat.div_pos hlec h.pos⟩

    have gcd_eq1 : dd.gcd ee = gg / hh := by
        unfold dd ee gg
        exact Nat.gcd_div hdvda hdvdb
    have gcd_eq2 : (dd.gcd ee).gcd ff = hh/hh := by
        unfold dd ee ff
        rw [gcd_eq1]
        exact Nat.gcd_div hdvdg hdvdc
    have gcd_eq3 : (dd.gcd ee).gcd ff = 1 := by
        rw [gcd_eq2]
        exact Nat.div_self h.pos

    have eqeq : 2*aa^nn + 3*bb^nn = 4*cc^nn := by
        have step1 : 2*aa^nn + 3*bb^nn = (2*a^n + 3*b^n).val := by
            rfl
        have step2 : (2*a^n + 3*b^n).val = (4*c^n).val := by
            unfold Fermat at Feq
            rw [Feq]
        have step3 : (4*c^n).val = 4*cc^nn := by
            rfl
        rw [step1, step2, step3]

    have eq0 : (2*d^n + 3*e^n).val = 2*dd^nn + 3*ee^nn := rfl

    have eq1 : 2*dd^nn + 3*ee^nn = 2*aa^nn / hh^nn + 3*bb^nn / hh^nn := by
        have eq1_1 : hh^nn ∣ aa^nn := pow_dvd_pow_of_dvd hdvda nn
        have eq1_2 : 2*dd^nn = (2*aa^nn) / hh^nn := by
            rw [Nat.div_pow hdvda]
            exact (Nat.mul_div_assoc 2 eq1_1).symm

        have eq1_3 : hh^nn ∣ bb^nn := pow_dvd_pow_of_dvd hdvdb nn
        have eq1_4 : 3*ee^nn = (3*bb^nn) / hh^nn := by
            rw [Nat.div_pow hdvdb]
            exact (Nat.mul_div_assoc 3 eq1_3).symm
        rw [eq1_2, eq1_4]

    have eq2 : 2*aa^nn / hh^nn + 3*bb^nn / hh^nn = 4*cc^nn / hh^nn := by
        have eq2_1 : hh^nn ∣ aa^nn := pow_dvd_pow_of_dvd hdvda nn
        have eq2_2 : aa^nn ∣ 2*aa^nn := Nat.dvd_mul_left (aa^nn) 2
        have eq2_3 : hh^nn ∣ 2 * aa^nn := Nat.dvd_trans eq2_1 eq2_2
        have eq2_4 : 2*aa^nn / hh^nn + 3*bb^nn / hh^nn
            = (2*aa^nn + 3*bb^nn) / hh^nn :=
            (Nat.add_div_of_dvd_right (b := 3*bb^nn) eq2_3).symm
        have eq2_5 : (2*aa^nn + 3*bb^nn) / hh^nn =  (4*cc^nn) / hh^nn := by
            unfold Fermat at Feq
            rw [eqeq]
        have eq2_6 : (4*cc^nn) / hh^nn = 4*cc^nn / hh^nn := by
            rfl
        rw [eq2_4, eq2_5, eq2_6]

    have eq3 : 4*cc^nn / hh^nn = 4*ff^nn := by
        have eq3_1 : hh^nn ∣ cc^nn := pow_dvd_pow_of_dvd hdvdc nn
        have eq3_2 : 4*cc^nn / hh^nn = (4*cc^nn) / hh^nn := rfl
        have eq3_3 : (4*cc^nn) / hh^nn = 4*ff^nn := by
            rw [Nat.div_pow hdvdc]
            exact Nat.mul_div_assoc 4 eq3_1
        rw [eq3_2, eq3_3]

    have eq4: 4*ff^nn = (4*f^n).val := rfl

    have eq_val : (2*d^n + 3*e^n).val = (4*f^n).val := by
        rw [eq0, eq1, eq2, eq3, eq4]

    have eq_final : Fermat n d e f := by
        unfold Fermat
        exact Subtype.ext eq_val

    use d, e, f
    exact ⟨eq_final, gcd_eq3⟩

lemma always0 (n : ℕ+) : 0^n.val = 0 := by
    have h : 0 < n.val := n.pos
    exact Nat.zero_pow h

lemma pow_parity (n : ℕ+) (x : ℕ) : (x%2)^n.val % 2 = x % 2 := by
    have h : x % 2 = 0 ∨ x % 2 = 1 := by
        have hlt : x % 2 < 2 := Nat.mod_lt x (by decide)
        interval_cases x % 2
        · left; rfl
        · right; rfl
    cases h with
    | inl h0 =>
        rw [h0, Nat.zero_pow n.pos]
    | inr h1 =>
        rw [h1, Nat.one_pow n.val]

lemma square_parity3 (x : ℕ) : (x%3)^2 % 3 = x^2 % 3 :=
    (Nat.pow_mod x 2 3).symm

lemma indeed_only_1 : only_1 := by
    unfold only_1
    intro n
    intro abc_sol

    obtain ⟨a, b, c, eqabc⟩ := abc_sol
    have xyz_sol : ∃ (d e f : ℕ+), 2*d^n + 3*e^n = 4*f^n
        ∧ (d.val.gcd e).gcd f = 1 :=
        can_assume_coprime n a b c eqabc

    obtain ⟨x, y, z, eqxyz, coprime⟩ := xyz_sol
    let nn := n.val
    let xx := x.val
    let yy := y.val
    let zz := z.val

    have eqxyz' : 2*xx^nn + 3*yy^nn = 4*zz^nn := by
        unfold Fermat at eqxyz
        have step1 : 2*xx^nn + 3*yy^nn = (2*x^n + 3*y^n).val := rfl
        have step2 : (2*x^n + 3*y^n).val = (4*z^n).val := by
            rw [eqxyz]
        have step3 : (4*z^n).val = 4*zz^nn := rfl
        rw [step1, step2, step3]

    have coprime' : (xx.gcd yy).gcd zz = 1 := by
        unfold xx yy zz
        exact coprime

    have yeven : yy % 2 = 0 := by
        have step1: yy^nn % 2 = yy % 2 := by
            have step1_1 : yy^nn % 2 = (yy%2)^nn % 2:= Nat.pow_mod yy nn 2
            have step1_2 : (yy%2)^nn % 2 = yy % 2 := pow_parity n yy
            rw [step1_1, step1_2]

        have step2 : yy^nn % 2 = 3*yy^nn % 2 := by
            rw [Nat.mul_mod 3 (yy^nn) 2]
            norm_num

        have step3 : 2*xx^nn % 2 = 0 := by
            rw [Nat.mul_mod 2 (xx^nn) 2]
            norm_num

        have step4 : 4*zz^nn % 2 = 0 := by
            rw [Nat.mul_mod 4 (zz^nn) 2]
            norm_num

        have either : yy % 2 = 0 ∨ yy % 2 = 1 := by
            have hlt : yy % 2 < 2 := Nat.mod_lt yy (by decide)
            interval_cases yy % 2
            · left; rfl
            · right; rfl

        cases either with
        | inl h0 =>
            exact h0
        | inr h1 =>
            have step5 : 3*yy^nn % 2 = 1 := by
                rw [step2.symm, step1]
                exact h1
            have step6 : 2*xx^nn % 2 + 3*yy^nn % 2 = 1 := by
                rw [step3, step5]

            have step7 : (2*xx^nn % 2 + 3*yy^nn % 2) % 2 = 1 := by
                rw [step6]

            have step8 : (2*xx^nn % 2 + 3*yy^nn % 2) % 2
                = (2*xx^nn + 3*yy^nn) % 2 := by
                rw [Nat.add_mod (2*xx^nn) (3*yy^nn) 2]

            have step9 : (2*xx^nn + 3*yy^nn) % 2 = 1 := by
                rw [step8.symm, step7]

            have step10 : (4*zz^nn) % 2 = 1 := by
                rw [eqxyz'.symm, step9]

            have step10 : 1 = 0 := by
                rw [step10.symm, step4]

            have step11 : 1 <= 0 := Nat.le_of_eq step10

            have step12 : False := by
                exact Nat.not_succ_le_zero 0 step11

            have step13 : yy % 2 = 0 := by
                exact False.elim step12

            exact step13

    have yeven' : 2 ∣ yy := by
        exact Nat.dvd_of_mod_eq_zero yeven

    by_contra not1

    have ge2 : 2 ≤ nn := by
        by_contra not2
        have step1 : nn + 1 <= 2 := (Nat.not_le_eq 2 nn).mp not2
        have step2 : nn <= 1 := Nat.le_of_succ_le_succ step1
        have step4 : 1 <= nn := n.pos
        have step5 : n.val = 1 := Nat.le_antisymm step2 step4
        have step6 : ¬ n.val = 1 := by
            intro h
            apply not1
            apply Subtype.ext
            exact h
        exact step6 step5

    have xeven : xx % 2 = 0 := by
        have step1: xx^nn % 2 = xx % 2 := by
            have step1_1 : xx^nn % 2 = (xx%2)^nn % 2:= Nat.pow_mod xx nn 2
            have step1_2 : (xx%2)^nn % 2 = xx % 2 := pow_parity n xx
            rw [step1_1, step1_2]

        have step2 : (xx^nn % 2) * 2 = xx^nn * 2 % 4 := by
            rw [Nat.mul_mod_mul_right 2 (xx^nn) 2]

        have either : xx % 2 = 0 ∨ xx % 2 = 1 := by
            have hlt : xx % 2 < 2 := Nat.mod_lt xx (by decide)
            interval_cases xx % 2
            · left; rfl
            · right; rfl

        cases either with
        | inl h0 =>
            exact h0
        | inr h2 =>
            have step3 : 2 * xx^nn % 4 = 2 * (xx^nn % 2) := by
                rw [Nat.mul_mod_mul_left 2 (xx^nn) 2]
            have step4 : 2 * xx^nn % 4 = 2 := by
                rw [step3, step1, h2]
            have step8 : 2^nn ∣ yy^nn := pow_dvd_pow_of_dvd yeven' nn
            have step9 : 2^2 ∣ 2^nn := pow_dvd_pow 2 ge2
            have step10 : 2^2 ∣ yy^nn := Nat.dvd_trans step9 step8
            have step11 : 4 ∣ yy^nn := by
                have four : 2^2 = 4 := rfl
                rw [four.symm]
                exact step10
            have step12 : yy^nn % 4 = 0 := by
                rw [Nat.mod_eq_zero_of_dvd step11]
            have step13 : 3 * yy^nn % 4 = 0 := by
                rw [Nat.mul_mod 3 (yy^nn) 4, step12]
            have step14 : 4*zz^nn % 4 = 0 := by
                rw [Nat.mul_mod 4 (zz^nn) 4]
                norm_num
            have step15 : (2*xx^nn % 4 + 3*yy^nn % 4) % 4
                = (2*xx^nn + 3*yy^nn) % 4 := by
                rw [Nat.add_mod (2*xx^nn) (3*yy^nn) 4]
            have step16 : (2*xx^nn + 3*yy^nn) % 4 = 2 := by
                rw [step15.symm, step4, step13]
            have step17 : (4*zz^nn) % 4 = 2 := by
                rw [eqxyz'.symm, step16]
            have step18 : 2 = 0 := by
                rw [step17.symm, step14]

            contradiction

    have xeven' : 2 ∣ xx := by
        exact Nat.dvd_of_mod_eq_zero xeven

    have not3 : ¬ 3 ≤ nn := by
        by_contra if3
        have step1 : 2 ∣ xx := Nat.dvd_of_mod_eq_zero xeven
        have step2 : 2^nn ∣ xx^nn := pow_dvd_pow_of_dvd step1 nn
        have step3 : 2^3 ∣ 2^nn := pow_dvd_pow 2 if3
        have step4 : 2^3 ∣ xx^nn := Nat.dvd_trans step3 step2
        have step5 : 8 ∣ xx^nn := by
            have eight : 2^3 = 8 := rfl
            rw [eight.symm]
            exact step4

        have step6 : 2 ∣ yy := Nat.dvd_of_mod_eq_zero yeven
        have step7 : 2^nn ∣ yy^nn := pow_dvd_pow_of_dvd step6 nn
        have step8 : 2^3 ∣ 2^nn := pow_dvd_pow 2 if3
        have step9 : 2^3 ∣ yy^nn := Nat.dvd_trans step8 step7
        have step10 : 8 ∣ yy^nn := by
            have eight : 2^3 = 8 := rfl
            rw [eight.symm]
            exact step9

        have either : zz % 2 = 0 ∨ zz % 2 = 1 := by
            have hlt : zz % 2 < 2 := Nat.mod_lt zz (by decide)
            interval_cases zz % 2
            · left; rfl
            · right; rfl
        cases either with
        | inl h0 =>
            have zeven : 2 ∣ zz := Nat.dvd_of_mod_eq_zero h0
            have evengcd : 2 ∣ xx.gcd yy := by
                exact Nat.dvd_gcd xeven' yeven'
            have evengcd2 : 2 ∣ (xx.gcd yy).gcd zz := Nat.dvd_gcd evengcd zeven
            have evengcd3 : (xx.gcd yy).gcd zz % 2 = 0 := by
                rw [Nat.mod_eq_zero_of_dvd evengcd2]
            have oddgcd : (xx.gcd yy).gcd zz % 2 = 1 := by
                rw [coprime']
            have gcd_contra : 0 = 1 := by
                rw [evengcd3.symm, oddgcd]
            contradiction
        | inr h1 =>
            have step1 : 4 * zz^nn % 8 = 4 * (zz^nn % 2) := by
                rw [Nat.mul_mod_mul_left 4 (zz^nn) 2]
            have step2 : zz^nn % 2 = zz % 2 := by
                have step2_1 : zz^nn % 2 = (zz%2)^nn % 2 := Nat.pow_mod zz nn 2
                have step2_2 : (zz%2)^nn % 2 = zz % 2 := pow_parity n zz
                rw [step2_1, step2_2]
            have step3 : 4 * (zz^nn % 2) = 4 := by
                rw [step2, h1]
            have step4 : 4 * zz^nn % 8 = 4 := by
                rw [step1, step3]
            have step5' : 3*8 ∣ 3*yy^nn := Nat.mul_dvd_mul_left 3 (step10)
            have step6 : 8 ∣ 3*8 := by
                rw [Nat.mul_comm]
                exact Nat.dvd_mul_right 8 3
            have step7 : 8 ∣ 3*yy^nn := Nat.dvd_trans step6 step5'
            have step8 : 3 * yy^nn % 8 = 0 := Nat.mod_eq_zero_of_dvd step7
            have step9 : 2*8 ∣ 2*xx^nn := Nat.mul_dvd_mul_left 2 (step5)
            have step10 : 8 ∣ 2*8 := by
                rw [Nat.mul_comm]
                exact Nat.dvd_mul_right 8 2
            have step11 : 8 ∣ 2*xx^nn := Nat.dvd_trans step10 step9
            have step12 : 2*xx^nn % 8 = 0 := Nat.mod_eq_zero_of_dvd step11
            have step13 : (2*xx^nn % 8 + 3*yy^nn % 8) % 8
                = (2*xx^nn + 3*yy^nn) % 8 := by
                rw [Nat.add_mod (2*xx^nn) (3*yy^nn) 8]
            have step14 : (2*xx^nn + 3*yy^nn) % 8 = 0 := by
                rw [step13.symm, step12, step8]
            have step15 : (2*xx^nn + 3*yy^nn) % 8 = (4*zz^nn) % 8 := by
                rw [eqxyz'.symm]
            have step16 : 4 = 0 := by
                rw [step4.symm, step15.symm, step14]
            contradiction
    have not2 : ¬ 2 = nn := by
        by_contra if2
        have step1 : 2*xx^2 + 3*yy^2 = 4*zz^2 := by
            unfold Fermat at eqabc
            have step1_1 : 2*xx^2 + 3*yy^2 = (2*x^2 + 3*y^2).val := rfl
            have step1_2 : (2*x^2 + 3*y^2).val = (2*x^nn + 3*y^nn).val := by
                rw [if2.symm]
            have step1_3 : (2*x^nn + 3*y^nn).val = (2*x^n + 3*y^n).val := rfl
            have step1_4 : (2*x^n + 3*y^n).val = (4*z^n).val := by
                rw [eqxyz]
            have step1_5 : (4*z^n).val = (4*z^nn).val := rfl
            have step1_6 : (4*z^nn).val = (4*z^2).val := by
                rw [if2.symm]
            have step1_7 : (4*z^2).val = 4*zz^2 := rfl
            rw [step1_1, step1_2, step1_3, step1_4, step1_5, step1_6, step1_7]

        have step2 : (2*xx^2 + 3*yy^2) % 3 = (4*zz^2) % 3 := by
            rw [step1]

        have step3 : (2*xx^2 + 3*yy^2) % 3 = (2*xx^2 % 3 + 3*yy^2 % 3) % 3 := by
            rw [Nat.add_mod (2*xx^2) (3*yy^2) 3]
        have step4 : 3*yy^2 % 3 = 0 := by
            rw [Nat.mul_mod 3 (yy^2) 3]
            norm_num
        have step5 : (2*xx^2 + 3*yy^2) % 3 = 2*xx^2 % 3:= by
            rw [step3, step4]
            norm_num
        have step6 : 2*xx^2 % 3 = 4*zz^2 % 3:= by
            rw [step2.symm, step5]
        have step7 : 4*zz^2 % 3 = 1*zz^2 % 3 := by
            rw [Nat.mul_mod 4 (zz^2) 3]
            norm_num
        have step8 : 1*zz^2 % 3 = zz^2 %3 := by
            rw [Nat.mul_comm 1 (zz^2)]
            rw [Nat.mul_one (zz^2)]
        have step9 : 2*xx^2 % 3 = zz^2 % 3:= by
            rw [step6, step7, step8]
        have step10 : (xx%3)^2 % 3 = xx^2 % 3 :=
            (Nat.pow_mod x 2 3).symm
        let A := (xx%3)^2
        let B:= xx^2
        have step11: A % 3 = B % 3 := by
            rw [step10]
        have step12 : 2*A % 3 = (2%3) * (A%3) % 3 := by
            rw [Nat.mul_mod 2 A 3]
        have step13 : (2%3) * (A%3) % 3 = (2%3) * (B%3) % 3 := by
            rw [step11]
        have step14 : (2%3) * (B%3) % 3 = 2*B % 3 := by
            rw [Nat.mul_mod 2 B 3]
        have step15 : 2*A % 3 = 2*B % 3 := by
            rw [step12, step13, step14]
        have step16 : 2*(xx%3)^2 % 3 = 2*xx^2 % 3 := by
            rw [step15]
        have step17 : 2*(xx%3)^2 % 3 = zz^2 % 3 := by
            rw [step16, step9]
        have step18 : 2*(xx%3)^2 % 3 = (zz%3)^2 % 3 := by
            let X := Nat.pow_mod zz 2 3
            rw [X.symm, step17]

        have either_x : xx % 3 = 0 ∨ (xx % 3 = 1 ∨ xx % 3 = 2) := by
            have hlt : xx % 3 < 3 := Nat.mod_lt xx (by decide)
            interval_cases xx % 3
            · left; rfl
            · right; left; rfl
            · right; right; rfl
        have either_y : yy % 3 = 0 ∨ (yy % 3 = 1 ∨ yy % 3 = 2) := by
            have hlt : yy % 3 < 3 := Nat.mod_lt yy (by decide)
            interval_cases yy % 3
            · left; rfl
            · right; left; rfl
            · right; right; rfl
        have either_z : zz % 3 = 0 ∨ (zz % 3 = 1 ∨ zz % 3 = 2) := by
            have hlt : zz % 3 < 3 := Nat.mod_lt zz (by decide)
            interval_cases zz % 3
            · left; rfl
            · right; left; rfl
            · right; right; rfl
        cases either_x with
        | inl x0 =>
            have s1 : 0 = 2 * (xx % 3) ^ 2 % 3 := by
                rw [x0]
                simp
            cases either_z with
            | inl z0 =>
                have q1 : 3 ∣ xx := Nat.dvd_of_mod_eq_zero x0
                have q2 : 3 ∣ zz := Nat.dvd_of_mod_eq_zero z0
                have q3 : 9 ∣ xx^2 := pow_dvd_pow_of_dvd q1 2
                have q4 : 9 ∣ zz^2 := pow_dvd_pow_of_dvd q2 2
                have q5 : xx^2 ∣ 2*xx^2 := Nat.dvd_mul_left (xx^2) 2
                have q6 : zz^2 ∣ 4*zz^2 := Nat.dvd_mul_left (zz^2) 4
                have q7 : 9 ∣ 2*xx^2 := Nat.dvd_trans q3 q5
                have q8 : 9 ∣ 4*zz^2 := Nat.dvd_trans q4 q6
                have q9 : (2*xx^2 + 3*yy^2) % 9 = (2*xx^nn + 3*yy^nn) % 9 := by
                    rw [if2]
                have q10 : (2*xx^nn + 3*yy^nn) % 9 = (4*zz^nn) % 9:= by
                    rw [eqxyz'.symm]
                have q11 : (4*zz^nn) % 9 = (4*zz^2) % 9 := by
                    rw [if2]
                have q12 : (4*zz^2) % 9 = 0 := Nat.mod_eq_zero_of_dvd q8
                have q13 : (2*xx^2 + 3*yy^2) % 9 = 0 := by
                    rw [q9, q10, q11, q12]
                have q14 : (2*xx^2 % 9 + 3*yy^2 % 9) % 9 = 0 := by
                    rw [(Nat.add_mod (2*xx^2) (3*yy^2) 9).symm]
                    exact q13
                have q15 : (2*xx^2 % 9 + 3*yy^2 % 9) % 9 = (3*yy^2 % 9) % 9 := by
                    rw [Nat.mod_eq_zero_of_dvd q7]
                    simp
                have q16 : (3*yy^2 % 9) % 9 = 3*yy^2 % 9 := Nat.mod_mod (3*yy^2) 9
                have q17 : 3*yy^2 % 9 = 0 := by
                    rw [q16.symm, q15.symm, q14]
                have q18 : 9 ∣ 3*yy^2 := Nat.dvd_of_mod_eq_zero q17
                have q19 : 9 % 3 = 0 := rfl
                have q20 : 3 ∣ 9 := Nat.dvd_of_mod_eq_zero q19
                have q21 : 9 / 3 ∣ 3 * yy^2 / 3 := Nat.div_dvd_div q20 q18
                have q22 : 3 = 9 / 3 := rfl
                have q23 : 3 * yy^2 / 3 = yy^2 := by
                    rw [Nat.mul_comm 3 (yy^2)]
                    rw [Nat.mul_div_assoc (yy^2) (by decide)]
                    simp
                have q24 : 3 ∣ yy^2 := by
                    rw [q22, q23.symm]
                    exact q21
                have q25 : yy^2 % 3 = 0 := Nat.mod_eq_zero_of_dvd q24
                cases either_y with
                | inl y0 =>
                    have r1 : 3 ∣ yy := Nat.dvd_of_mod_eq_zero y0
                    have r2 : 3 ∣ xx.gcd yy :=
                        Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero x0) r1
                    have r3 : 3 ∣ (xx.gcd yy).gcd zz :=
                        Nat.dvd_gcd r2 (Nat.dvd_of_mod_eq_zero z0)
                    have r4 : 3 ∣ 1 := by
                        rw [coprime'.symm]
                        exact r3
                    have r5 : 1 % 3 = 0 := by
                        rw [Nat.mod_eq_zero_of_dvd r4]
                    have r6 : 1 = 0 := by
                        rw [r5.symm]
                    contradiction
                | inr y12 =>
                    cases y12 with
                    | inl y1 =>
                        have r7 : (yy%3)^2 % 3 = 1 := by
                            rw [y1]
                            simp
                        have r8 : yy^2 % 3 = 1 := by
                            rw [Nat.pow_mod yy 2 3, r7]
                        have r9 : 1 = 0 := by
                            rw [q25.symm, r8]
                        contradiction
                    | inr y2 =>
                        have r10 : (yy%3)^2 % 3 = 1 := by
                            rw [y2]
                            simp
                        have r11 : yy^2 % 3 = 1 := by
                            rw [Nat.pow_mod yy 2 3, r10]
                        have r12 : 1 = 0 := by
                            rw [q25.symm, r11]
                        contradiction
            | inr z12 =>
                cases z12 with
                | inl z1 =>
                    have s2 : (zz%3)^2 % 3 = 1 := by
                        rw [z1]
                        simp
                    have s3 : 0 = 1 := by
                        rw [s1, step18, s2]
                    contradiction
                | inr z2 =>
                    have s4 : (zz%3)^2 % 3 = 1 := by
                        rw [z2]
                        simp
                    have s5 : 0 = 1 := by
                        rw [s1, step18, s4]
                    contradiction
        | inr x12 =>
            cases x12 with
            | inl x1 =>
                have s6 : 2 * (xx%3) ^ 2 % 3 = 2 := by
                    rw [x1]
                    simp
                cases either_z with
                | inl z0 =>
                    have s7 : (zz%3)^2 % 3 = 0 := by
                        rw [z0]
                        simp
                    have s8 : 2 = 0 := by
                        rw [s6.symm, step18, s7]
                    contradiction
                | inr z12 =>
                    cases z12 with
                    | inl z1 =>
                        have s9 : (zz%3)^2 % 3 = 1 := by
                            rw [z1]
                            simp
                        have s10 : 2 = 1 := by
                            rw [s6.symm, step18, s9]
                        contradiction
                    | inr z2 =>
                        have s11 : (zz%3)^2 % 3 = 1 := by
                            rw [z2]
                            simp
                        have s12 : 2 = 1 := by
                            rw [s6.symm, step18, s11]
                        contradiction
            | inr x2 =>
                have s13 : 2 * (xx%3) ^ 2 % 3 = 2 := by
                    rw [x2]
                    simp
                cases either_z with
                | inl z0 =>
                    have s14 : (zz%3)^2 % 3 = 0 := by
                        rw [z0]
                        simp
                    have s15 : 2 = 0 := by
                        rw [s13.symm, step18, s14]
                    contradiction
                | inr z12 =>
                    cases z12 with
                    | inl z1 =>
                        have s16 : (zz%3)^2 % 3 = 1 := by
                            rw [z1]
                            simp
                        have s17 : 2 = 1 := by
                            rw [s13.symm, step18, s16]
                        contradiction
                    | inr z2 =>
                        have s18 : (zz%3)^2 % 3 = 1 := by
                            rw [z2]
                            simp
                        have s19 : 2 = 1 := by
                            rw [s13.symm, step18, s18]
                        contradiction
    let recall1 := ge2
    let recall2 := not2
    let recall3 := not3
    have infer4 : nn < 3 ∨ 3 ≤ nn := lt_or_ge nn 3
    have infer5 : nn < 3 := Or.resolve_right infer4 recall3
    have infer6 : nn <= 2 := Nat.le_of_lt_succ infer5
    have infer7 : nn = 2 := Nat.le_antisymm infer6 recall1
    have infer8 : 2 = nn := by
        rw [infer7]
    exact not2 infer8

theorem sol : Putnam2025A1 := by
    unfold Putnam2025A1
    have big_lemma : {n : ℕ+ | exists_abc n} = {1} :=
        it_remains_to_show indeed_only_1
    rw [big_lemma]

#print axioms sol

-- Tactics cheetsheet
-- https://github.com/madvorak/lean4-tactics

-- Auto-gen docs from source code, good for searching
-- https://leanprover-community.github.io/mathlib4_docs/

-- Collection of (advanced) math topics in mathlib
-- https://leanprover-community.github.io/mathlib-overview.html

-- Seacrh engines
-- https://loogle.lean-lang.org -- pattern matching
-- https://www.moogle.ai        -- use AI

-- Putnam
-- https://maa.org/wp-content/uploads/2025/02/2024-Putnam-Session-A-Solutions-1.pdf
