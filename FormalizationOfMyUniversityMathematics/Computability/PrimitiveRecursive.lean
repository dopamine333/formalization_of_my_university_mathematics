import Mathlib.Computability.Primrec

open Nat Nat.Primrec

#check Nat.rec

rec : ℕ → (ℕ → ℕ → ℕ) → (ℕ → ℕ)
#check Nat.Primrec
#check Nat.Primrec.prec
#check Nat.unpaired
/-

if f, g is primitive recursive then

fix z,
  Nat.rec
      (f z)
      (fun y IH ↦ g (Nat.pair z (Nat.pair y IH)))
is a function F : ℕ → ℕ
 F 0 = f z
 F (n+1) = g (z, n, F n)
release z, then define

h(z, n) = F n

m ↦ h(m.1, m.2) is also primitive recursive


h (z, 0) = f(z)
h (z, n+1) = g(z, n, h(z, n))

Nat.Primrec f →
Nat.Primrec g →
Nat.Primrec (
  Nat.unpaired fun z n ↦
    Nat.rec
      (f z)
      (fun y IH ↦ g (Nat.pair z (Nat.pair y IH))) n)


-/

#check Nat.add
/-
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
-/
theorem add' : Nat.Primrec (unpaired (· + ·)) := by
  have : (fun a b : ℕ ↦ a + b) = (fun a b ↦ Nat.rec a (fun _ IH ↦ IH + 1) b) := by
    ext a b
    induction b with
    | zero => rfl
    | succ b ih =>
      rw [add_succ, succ_inj]
      exact ih
  rw [this]
  convert prec (f := fun z ↦ z) (g := fun p ↦ (unpair (unpair p).2).2 + 1) ?_ ?_
  . rw [unpair_pair, unpair_pair]
  . have := pair left right
    convert this
    rw [pair_unpair]
  . exact (Nat.Primrec.succ.comp right).comp right

/-
/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive Primrec : (ℕ → ℕ) → Prop
  | zero : Nat.Primrec fun _ => 0
  | protected succ : Nat.Primrec succ
  | left : Nat.Primrec fun n => n.unpair.1
  | right : Nat.Primrec fun n => n.unpair.2
  | pair {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => pair (f n) (g n)
  | comp {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g n)
  | prec {f g} :
      Nat.Primrec f →
        Nat.Primrec g →
          Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)


# Naturals pairing function

(a, b) = if a < b then b * b + a else a * a + a + b

let s := sqrt n
n.1 = if n - s * s < s then n - s * s else s
n.2 = if n - s * s < s then s else n - s * s - s

lemma : ∀ a b, (a, b).1 = a
lemma : ∀ a b, (a, b).2 = b
lemma : ∀ n, (n.1, n.2) = n

# Primitive recursive

a ℕ → ℕ function is primitive recursive if
it can be built from the following rules:

1. fun n ↦ 0 is primitive recursive
2. fun n ↦ n + 1 is primitive recursive
3. fun n ↦ n.1 is primitive recursive
4. fun n ↦ n.2 is primitive recursive
5. if f, g are primitive recursive, then so is fun n ↦ (f n, g n)
6. if f, g are primitive recursive, then so is fun n ↦ f (g n)
7. if f, g are primitive recursive, then so is h defined by
    h (z, 0) = f z
    h (z, n + 1) = g(z, (n, h(z, n)))


7. if f, g are primitive recursive,
define h : ℕ → ℕ → ℕ by
h z n := rec (f z) (fun y IH ↦ g (z, (y, IH))) n
then fun n ↦ h n.1 n.2 is also primitive recursive

7. if f, g are primitive recursive, then so is
  fun n ↦ rec (f n.1) (fun m IH ↦ g (n.1, (m, IH))) n.2

IH is come from Induction Hypothesis


add a b = rec a (fun _ IH => IH + 1) b
goal : fun n ↦ add n.1 n.2 is primitive recursive (a.k.a primrec)

let f := fun z ↦ z
claim : f is primrec
  by 3, 4, fun n ↦ n.1, fun n ↦ n.2 is primrec
  by 5, fun n ↦ ((fun n ↦ n.1) n, (fun n ↦ n.2) n) is primrec
  but ((fun n ↦ n.1) n, (fun n ↦ n.2) n)
  = (n.1, n.2)  (just substitute)
  = n (by lemma)
  thus fun n ↦ n is primrec

let g := fun p ↦ p.2.2 + 1
claim : g is primrec
  by 4, fun n ↦ n.2 is primrec
  by 6, fun n ↦ (fun n ↦ n.2) ((fun n ↦ n.2) n) is primrec
  by substitute, fun n ↦ n.2.2 is primrec
  thus fun n ↦ n.2.2 is primrec
  by 2, fun n ↦ n + 1 is primrec
  by 6, fun n ↦ (fun n ↦ n + 1) ((fun n ↦ n.2.2) n) is primrec
  by substitute, fun n ↦ n.2.2 + 1 is primrec

by 7. the function is primrec :
fun n ↦ rec (f n.1) (fun m IH ↦ g (n.1, (m, IH))) n.2
= fun n ↦ rec n.1 (fun m IH ↦ (n.1, (m, IH)).2.2 + 1) n.2
= fun n ↦ rec n.1 (fun m IH ↦ (m, IH).2 + 1) n.2
= fun n ↦ rec n.1 (fun m IH ↦ IH + 1) n.2
= add n.1 n.2



zero. fun n ↦ 0 is primitive recursive
succ. fun n ↦ n + 1 is primitive recursive
left. fun n ↦ n.1 is primitive recursive
right. fun n ↦ n.2 is primitive recursive
pair. if f, g are primitive recursive, then so is fun n ↦ (f n, g n)
comp. if f, g are primitive recursive, then so is fun n ↦ f (g n)
prec. if f, g are primitive recursive, then so is
  fun n ↦ rec (f n.1) (fun m IH ↦ g (n.1, (m, IH))) n.2

add a b = rec a (fun _ IH => IH + 1) b
goal : fun n ↦ add n.1 n.2 is primitive recursive (a.k.a primrec)

let f := fun z ↦ z
claim : f is primrec
  by left, right, fun n ↦ n.1, fun n ↦ n.2 is primrec
  by pair, fun n ↦ ((fun n ↦ n.1) n, (fun n ↦ n.2) n) is primrec
  but ((fun n ↦ n.1) n, (fun n ↦ n.2) n)
  = (n.1, n.2)  (just substitute)
  = n (by lemma)
  thus fun n ↦ n is primrec

let g := fun p ↦ p.2.2 + 1
claim : g is primrec
  by right, fun n ↦ n.2 is primrec
  by comp, fun n ↦ (fun n ↦ n.2) ((fun n ↦ n.2) n) is primrec
  by substitute, fun n ↦ n.2.2 is primrec
  thus fun n ↦ n.2.2 is primrec
  by succ, fun n ↦ n + 1 is primrec
  by comp, fun n ↦ (fun n ↦ n + 1) ((fun n ↦ n.2.2) n) is primrec
  by substitute, fun n ↦ n.2.2 + 1 is primrec

by prec. the function is primrec :
fun n ↦ rec (f n.1) (fun m IH ↦ g (n.1, (m, IH))) n.2
= fun n ↦ rec n.1 (fun m IH ↦ (n.1, (m, IH)).2.2 + 1) n.2
= fun n ↦ rec n.1 (fun m IH ↦ (m, IH).2 + 1) n.2
= fun n ↦ rec n.1 (fun m IH ↦ IH + 1) n.2
= add n.1 n.2

∪ {undefined}
-/

#check Primcodable
#check Primcodable.prim

/-

Nat.Primrec fun n ↦ Encodable.encode (Encodable.decode n)

fun n ↦ if decode n = undefined then 0 else (encode (decode n) + 1)


-/

#check em
