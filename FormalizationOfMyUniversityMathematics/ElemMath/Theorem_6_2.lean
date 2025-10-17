


-- Natural number was defined in lean, without mathlib.
#check Nat

-- Theorem 5.5
theorem mathematical_induciton
  (n₀ : Nat) (P : Nat → Prop)
  (basis : P n₀)
  (step : ∀ n ≥ n₀, P n → P (n + 1)) :
  ∀ n ≥ n₀, P n := by
  sorry

-- Theorem 6.1
theorem strong_mathematical_induciton
  (n₀ : Nat) (P : Nat → Prop)
  (basis : P n₀)
  (step : ∀ k ≥ n₀, (∀ i, n₀ ≤ i → i ≤ k → P i) → P (k + 1)) :
  ∀ n ≥ n₀, P n := by
  sorry


def mathematical_induciton_proposition : Prop :=
  ∀ (n₀ : Nat) (P : Nat → Prop)
  (basis : P n₀)
  (step : ∀ n ≥ n₀, P n → P (n + 1)),
  ∀ n ≥ n₀, P n

def strong_mathematical_induciton_proposition : Prop :=
  ∀ (n₀ : Nat) (P : Nat → Prop)
  (basis : P n₀)
  (step : ∀ k ≥ n₀, (∀ i, n₀ ≤ i → i ≤ k → P i) → P (k + 1)),
  ∀ n ≥ n₀, P n

-- Theorem 6.3
theorem induction_are_equicalent :
  mathematical_induciton_proposition
  ↔ strong_mathematical_induciton_proposition := by
  constructor
  . -- MI to SMI
    -- suppose MI is true
    intro MI
    -- to show SMI, given n₀, P, suppose
    -- 1. basis : P n₀
    -- 2. step : ∀ k ≥ n₀, (∀ i, n₀ ≤ i → i ≤ k → P i) → P (k + 1)
    -- holds
    intro n₀ P basis step
    -- let Q(k) := ∀ n₀ ≤ i ≤ k, P i holds
    let Q k := ∀ i, n₀ ≤ i → i ≤ k → P i
    -- to use MI on n₀ Q, we need to show
    -- 1. basis' : Q n₀ holds
    -- 2. step' : ∀ n ≥ n₀, Q n → Q (n + 1)
    have basis' : Q n₀ := by
      -- recall def of Q, (Q n₀) ↔ (∀ n₀ ≤ i ≤ n₀, P i)
      -- given n₀ ≤ i ≤ n₀, we need to show P i holds
      intro i n₀_le_i i_le_n₀
      -- we have i = n₀ by antisymmetric of natural nubmer
      have n₀_eq_i : n₀ = i := Nat.le_antisymm n₀_le_i i_le_n₀
      -- thus P i ↔ P n₀
      rw [← n₀_eq_i]
      -- it is exactly basis : P n₀
      exact basis

    have step' : ∀ n ≥ n₀, Q n → Q (n + 1) := by
      -- given n ≥ n₀ with Q n holds, we need to show Q (n + 1)
      intro n n₀_le_n Qn
      -- key : we need P (n + 1) holds, then "Q n + P (n + 1) = Q (n + 1)"
      have key : P (n + 1) := by
        -- why key holds, recall
        -- step : ∀ (k : Nat), k ≥ n₀ → (∀ n₀ ≤ i ≤ k, P i) → P (k + 1)
        -- replace k := n, we have
        -- step n : n ≥ n₀ → (∀ n₀ ≤ i ≤ n, P i) → P (n + 1)
        -- now, n ≥ n₀ is exactly n₀_le_n
        -- (∀ n₀ ≤ i ≤ n, P i) is exactly Q n
        -- thus
        -- step n n₀_le_n Qn : P (n + 1)
        -- is exactly the key
        exact step n n₀_le_n Qn
      -- to show Q (n + 1)
      -- given n₀ ≤ i ≤ n + 1, we split the case on i to show P i holds
      intro i n₀_le_i i_le_n_succ
      by_cases i_eq_n_succ : i = n + 1
      . -- case 1, i = n + 1, then use key, we are done
        rw [i_eq_n_succ]
        exact key
      . -- case 2, i ≠ n + 1 (the hypothesis i_eq_n_succ become i ≠ n + 1)
        -- then we have i ≤ n + 1 and i ≠ n + 1
        -- thus i < n + 1 (by the lemma Nat.lt_of_le_of_ne)
        have i_lt_n_succ: i < n + 1 := Nat.lt_of_le_of_ne i_le_n_succ i_eq_n_succ
        -- is is equivalent to i ≤ n (by the lemma Nat.lt_succ)
        have i_le_n : i ≤ n := Nat.lt_succ.mp i_lt_n_succ
        -- since Q n holds and n₀ ≤ i ≤ n, we have P i holds
        exact Qn i n₀_le_i i_le_n

    -- we showed basis' step' holds
    -- Therefore, by MI (apply to n₀ Q basis' step'), we get ∀ n ≥ n₀, Q n
    have all_Q_holds : ∀ n ≥ n₀, Q n := MI n₀ Q basis' step'
    -- in particular, ∀ n ≥ n₀, Q n will implies ∀ n ≥ n₀, P n
    -- quick check :
    -- given n ≥ n₀, get Q n, use n, since n₀ ≤ n and n ≤ n, thus P n holds
    -- (n ≤ n by Nat.le_refl)
    intro n n₀_le_n
    have h : Q n := all_Q_holds n n₀_le_n
    exact h n n₀_le_n (Nat.le_refl n)

  . -- SMI to MI
    sorry

theorem induction_are_equicalent' :
  mathematical_induciton_proposition
  ↔ strong_mathematical_induciton_proposition := by
  constructor
  . intro MI n₀ P basis step
    let Q k := ∀ i, n₀ ≤ i → i ≤ k → P i
    have basis' : Q n₀ := by
      intro i hn₀i hin₀
      have n₀_eq_i : n₀ = i := Nat.le_antisymm hn₀i hin₀
      exact n₀_eq_i ▸ basis
    have step' : ∀ n ≥ n₀, Q n → Q (n + 1) := by
      intro n n₀_le_n Qn
      have key : P (n + 1) := step n n₀_le_n Qn
      intro i hn₀i hinsucc
      by_cases h : i = n + 1
      . exact h ▸ key
      . exact Qn i hn₀i (Nat.lt_succ.mp (Nat.lt_of_le_of_ne hinsucc h))
    have all_Q_holds : ∀ n ≥ n₀, Q n := MI n₀ Q basis' step'
    exact fun n hn₀n ↦ all_Q_holds n hn₀n n hn₀n (Nat.le_refl n)
  . intro SMI n₀ Q basis' step'
    refine SMI n₀ Q basis' ?_
    intro n hn₀n h
    apply step' n hn₀n (h n hn₀n (Nat.le_refl n))

-- Example 10.2
theorem well_order
  (S : Nat → Prop) (nonempty : ∃ x, S x) :
  ∃ x, ∀ y, S y → x ≤ y := by sorry

def well_order_proposition : Prop :=
  ∀ (S : Nat → Prop) (nonempty : ∃ x, S x),
  ∃ x, ∀ y, S y → x ≤ y

-- Theorem 18.5
theorem induction_and_well_order_are_equivalent :
  well_order_proposition ↔ strong_mathematical_induciton_proposition := by sorry
