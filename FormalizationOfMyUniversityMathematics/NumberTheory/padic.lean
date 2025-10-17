import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Harmonic.Defs

#check padicValRat
#eval padicValRat 2 (1/2)
#eval padicValRat 2 (1/20)
#eval List.range 30|>.map (fun n ↦ 1/(n : ℚ))|>.map (padicValRat 2)
#eval List.range 30|>.map (fun n ↦ 1/(n : ℚ))|>.map (padicValRat 5)

#check harmonic
#eval harmonic 3

set_option pp.deepTerms true
set_option pp.rawOnError true
-- #eval ((List.range 200).map harmonic).map (padicValRat 2)
-- #eval ((List.range 200).map harmonic).map (padicValRat 3)
-- #eval (List.range 500).map (fun n ↦ padicValRat 3 (harmonic n))
#eval (List.range 300).map (fun n ↦ (n, padicValRat 3 (harmonic n)))
-- #eval ([200,205,206,207,210].map harmonic).map (padicValRat 3)
-- #eval ([3^4, 2*3^4, 3^5].map harmonic).map (padicValRat 3)
/-
1/2 → -1
1/3 → 0
1/4 → -2
1/5 → 0
1/6 → -1
1/7 → 0
1/8 → -3

-/

#eval 3^4
#eval 2*3^4
#eval 3^5
#eval 2*3*3*11
#eval 9 * 23
#eval 9 * 3 * 8

-- c₀ + c₁(x-a) + c₂(x-a)² + ... + cₙ(x-a)ⁿ
-- c₀ + c₁p + c₂p² + ... + cₙpⁿ
