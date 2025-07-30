import Mathlib.Tactic

def collatz (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

def print_collatz_sequence (n : ℕ) : IO Unit := do
  IO.println n
  if n == 1 then
    IO.println "stop!"
  else
    print_collatz_sequence (collatz n)
decreasing_by sorry

#eval! print_collatz_sequence 100
