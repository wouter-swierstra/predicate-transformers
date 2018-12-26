module ticks where

  open import Prelude

  -- Define a free monad
  open import Free

  data C : Set where
    Tick : C

  R : C -> Set
  R t = ⊤

  Ticked : Set -> Set
  Ticked = Free C R

  -- Define smart constructors
  tick : Ticked ⊤
  tick = Step Tick Pure

  -- Here we could define
  --  wp : ∀ {a b : Set} -> (a -> Ticked b) -> (a -> b -> Set) -> (a -> Set)
  --  but it wouldn't be very interesting
  --  the handle function
  --  handle : Ticked a -> a
  --  is too trivial to assign interesting logic to Ticked computations
  -- We could argue that we can assign semantics:
  -- Define a regular handler
  ⟦_⟧ : ∀ {a} -> Ticked a -> Pair a Nat
  ⟦ Pure x ⟧ = x , Zero
  ⟦ Step Tick c ⟧ = let x , n = ⟦ c tt ⟧ in x , Succ n 

  -- Use the handler to define a 'propositional handler'
  --   or alternatively: transform a Nat -> a -> Set as you traverse
  --   the Ticked computation
  handle : ∀ {a} -> (P : a -> Nat -> Set) -> Ticked a -> Set
  handle P tx = let x , n = ⟦ tx ⟧ in P x n

  -- And assign wp semantics to kleisi arrows
  wp : ∀ {a b : Set} -> (a -> Ticked b) -> (a -> b -> Nat -> Set) -> (a -> Set)
  wp c P x = handle (P x) (c x)

  -- Example
  hanoi : Nat -> Ticked ⊤
  hanoi Zero = return tt
  hanoi (Succ n) = hanoi n >> (tick >> hanoi n)

  hanoiSpec : Nat -> ⊤ -> Nat -> Set
  hanoiSpec n _ ticks = (pred (2 ^ n)) == ticks

  correctness : (n : Nat) -> wp hanoi hanoiSpec n
  correctness Zero = Refl
  correctness (Succ n) =
    pred ((2 ^ n) + ((2 ^ n) + 0))
       ⟨ undefined ⟩
    pred ((2 ^ n) + (2 ^ n))
       ⟨ undefined ⟩
    pred (2 ^ n) + (2 ^ n)
       ⟨ undefined ⟩
    pred (2 ^ n) + (1 + pred (2 ^ n))
       ⟨ undefined ⟩ 
    Pair.snd ⟦ hanoi n ⟧ + (Pair.snd ⟦ tick ⟧ + Pair.snd ⟦ hanoi n ⟧)
       ⟨ Refl ⟩
    Pair.snd ⟦ hanoi n ⟧ + Pair.snd ⟦ tick >> hanoi n ⟧
       ⟨ undefined ⟩
    Pair.snd ⟦ hanoi n >> (tick >> hanoi n) ⟧ ■
     

