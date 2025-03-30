-- import Batteries.Data.Rat.Basic
-- import Mathlib.NumberTheory.Padics.PadicVal.Defs
-- import Mathlib.Data.String.Defs

-- def Float.toExactDecimal (x : Float) : String := x.toRat0.pow2ToBase10

-- #eval Float.toExactDecimal (1.0 / 10.0)
-- import Batteries.Data.Rat.Basic
import Mathlib
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.String.Defs

def Rat.pow2ToBase10 (x : Rat) : String := toString (x.floor) ++ "." ++ (toString (x.num * 5 ^ (padicValNat 2 x.den) % (5 ^ (padicValNat 2 x.den) * x.den))).leftpad (padicValNat 2 x.den) '0'

#eval Rat.pow2ToBase10 ((1.0 : Rat) / 10.0)
#eval Rat.pow2ToBase10 ((1.0 : Rat) / (Rat.ofInt (2 ^ 52)) + 1.32421875)

-- 1.32421 87500 00000 22204 46049 25031 30808 47263 33618 16406 25
-- 1.3242187500000002220446049250313080847263336181640625
