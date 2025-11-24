namespace quine
open List
def a :=
["open List\ndef a :=", "#eval (IO.println (head! a))\n#eval a\n#eval (IO.println (head (tail a)))"]
#eval (IO.println (head! a))
#eval a
#eval (IO.println (head! (tail a)))
