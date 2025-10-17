import Mathlib.Control.Combinators


#check OptionT

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    failure
  else pure trimmed

structure UserInfo where
  name : String
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩

def interact : IO Unit := do
  match ← getUserInfo with
  -- getUserInfo has type `OptionT IO UserInfo`
  -- which equivelent to `IO (Option UsetInfo)`
  -- so it is in the same monad as `IO Unit`
  | none => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favorite beetle is {beetle}."

#print interact

def main : IO Unit := interact

#synth Monad Option
#synth LawfulMonad Option
#synth Monad (OptionT Option)
-- #synth LawfulMonad (OptionT Option)
#synth LawfulMonad (StateT _ Option)
#check OptionT
#check StateT.instLawfulMonad

#check bind_pure
#check pure_bind
#check bind_assoc


theorem OptionT_bind_pure'
  [Monad m] [LawfulMonad m] (x : OptionT m α) :
  x >>= pure = x := by
  change (.mk _) = x
  change (.mk do _) = x
  change (.mk do let y ← _; _) = x
  change (.mk do
    let y ← x
    match y with
    | some a => pure (some a)
    | none => pure none
  ) = x
  have (y : Option α) :
    (pure y : m (Option α))
    =
    match y with
      | some a => pure (some a)
      | none => pure none
    := by cases y <;> rfl
  simp only [← this]
  rw [bind_pure]
  rfl

theorem OptionT_bind_pure
  [Monad m] [LawfulMonad m] (x : OptionT m α) :
  x >>= pure = x := by
    calc _
      _ = bind x pure := rfl
      _ = bind x (fun y ↦ pure y) := rfl
      _ = bind x (fun y ↦ .mk (pure (some y))) := rfl
      _ = .mk (do
        let z ← x
        match z with
        | some w => pure (some w)
        | none => pure none
      ) := rfl
      _ = .mk (
        bind x fun z ↦
        match z with
        | some w => pure (some w)
        | none => pure none
      ) := rfl
      _ = .mk (
        bind x fun z ↦ pure z
      ) := by
        congr
        ext z
        cases z
        . rfl
        . rfl
      _ = .mk (bind x pure) := rfl
      _ = .mk x := by rw [bind_pure]
      _ = _ := rfl

theorem OptionT_pure_bind
  [Monad m] [LawfulMonad m] (x : α) (f : α → OptionT m β) :
  pure x >>= f = f x := by
    calc _
      _ = bind (pure x) f := rfl
      _ = bind (.mk (pure (some x))) f := rfl
      _ = .mk (do
        let y ← pure (some x)
        match y with
        | some z => f z
        | none => pure none
        ) := rfl
      _ = .mk (
        bind (pure (some x)) fun y ↦
        match y with
        | some z => f z
        | none => pure none
        ) := rfl
      _ = .mk (
        match (some x) with
        | some z => f z
        | none => pure none
        ) := by rw [pure_bind]
      _ = .mk (f x) := rfl
      _ = _ := rfl

theorem OptionT_bind_assoc
  [Monad m] [LawfulMonad m] (x : OptionT m α)
  (f : α → OptionT m β) (g : β → OptionT m γ) :
  x >>= f >>= g = x >>= fun x ↦ f x >>= g := by
    calc _
      _ = (
        bind (x >>= f).run fun y ↦
        match y with
        | some z => g z
        | none => pure none
      ) := rfl
      _ = (
        bind (
          bind x.run fun w ↦
          match w with
          | some a => f a
          | none => pure none
        ) fun y ↦
        match y with
        | some z => g z
        | none => pure none
      ) := rfl
      _ = x.run >>= _ >>= _ := rfl
      _ = x.run >>= (fun y ↦ _ >>= _) := by rw [bind_assoc]
      _ = (
        bind x.run fun y ↦
        match y with
        | some z => _
        | none => pure none
      ) := by
        congr
        ext y
        match y with
        | none =>
          dsimp
          rw [pure_bind]
        | some y =>
          dsimp
          rfl
      _ = x >>= fun y ↦ f y >>= g := rfl

#check joinM
