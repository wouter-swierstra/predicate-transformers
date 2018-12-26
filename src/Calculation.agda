{-#  OPTIONS --type-in-type #-}
module Calculation where

open import Prelude
open import Level

module Relations where

{-
  _⊆_ : {l : Level} {a b : Set l} ->
    (R1 R2 : a -> b -> Set l) -> Set l
  _⊆_ {a = a} {b = b} R1 R2 =
    (x : a) -> (y : b) -> R1 x y -> R2 x y 

  wp : {l : Level} {a b : Set l} -> (R : a -> b -> Set l) -> (b -> Set l) -> (a -> Set l)
  wp {b = b} R Q = λ x → Sigma b (\y -> R x y)

  isExec : {l : Level} {a b : Set l} -> (R : a -> b -> Set l) -> Set l
  isExec {a = a} {b = b} R = (x : a) -> Sigma b (\y -> R x y)

  extract : {l : Level} {a b : Set l} -> (R : a -> b -> Set l) -> isExec R -> a -> b
  extract R p x = Sigma.fst (p x)

  _⊑_ : {l : Level} -> {a b : Set l} -> (R R' : a -> b -> Set l) -> Set (suc l)
  _⊑_ {l} {a = a} {b = b} R R' = (P : b -> Set l) -> (x : a) -> wp R P x -> wp R' P x
  -}
  
{-
module Free where

  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
    Spec : ∀ {b : Set} (P : b -> Set) -> (b -> Free C R a) -> Free C R a

  return : {C : Set} {R : C -> Set} {a : Set} -> a -> Free C R a
  return = Pure

  _>>=_ : ∀ {C R a b} -> Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x >>= f = f x
  Step c x >>= f = Step c (\r -> x r >>= f)
  Spec P c >>= f = Spec P (\r -> c r >>= f)
  
  _>>_ : ∀ {C R a b} -> Free C R a -> Free C R b -> Free C R b
  c1 >> c2 = c1 >>= (\_ -> c2)

  fmap : ∀ {C R a b} -> (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x) = Pure (f x)
  fmap f (Step c k) = Step c (\r -> fmap f (k r)) 
  fmap f (Spec P c) = Spec P (\r -> fmap f (c r))
  
  fold : ∀ {C R a} {b : Set} ->
    ((c : C) -> (R c -> b) -> b) ->
    (a -> b) ->
    ({c : Set} -> (c -> Set) -> (c -> b) -> b) ->
    Free C R a -> b
  fold alg pure spec (Pure x) = pure x
  fold alg pure spec (Step c k) = alg c (\r -> fold alg pure spec (k r))
  fold alg pure spec (Spec {c} P k) = spec P (\r -> fold alg pure spec (k r))
  -}

module Maybe where

  -- Define our free monad
  open import Spec

  data C : Set where
    Nothing : C

  R : C -> Set
  R Nothing = ⊥

  Maybe : Set -> Set
  Maybe = Mix C R

  -- Define smart constructors
  just : ∀ {a : Set} -> a -> Maybe a
  just = Pure

  nothing : ∀ {a : Set} -> Maybe a
  nothing = Step Nothing λ()

  -- Define a propositional handler 
  handle : ∀ {a} -> (P : a -> Set) -> Maybe a -> Set
  handle P (Pure x) = P x
  handle P (Step Nothing x) = ⊥
  handle {a} P (Spec {b} pre post k) = Pair pre ((x : b) -> Pair (post x) (handle P (k x)))

  -- Compute wp for kleisli arrows
  wpMaybe : ∀ {a b : Set} -> (a -> Maybe b) -> (a -> b -> Set) -> (a -> Set)
  wpMaybe f pre x = handle (pre x) (f x)


  -- Rule of consequence
  >>-property : ∀ {a b} -> (c : Maybe a) -> (f : a -> Maybe b) ->
    (P : a -> Set) -> (Q : b -> Set) ->
      handle P c ->
      ((x : a) -> P x -> handle Q (f x)) ->
      handle Q (c >>= f)
  >>-property (Pure x) f P Q p q = q x p
  >>-property (Step Nothing x) f P Q () q
  >>-property (Spec pre post k) f P Q (x , y) q = x , (λ x₁ → Pair.fst (y x₁) , >>-property (k x₁) f P Q (Pair.snd (y x₁)) q)


--   -- Another example
--   fastProduct : List Nat -> Maybe Nat
--   fastProduct Nil = return 1
--   fastProduct (Cons Zero xs) = nothing
--   fastProduct (Cons (Succ k) xs) = fmap (\n -> Succ k * n) (fastProduct xs)

--   listProduct : List Nat -> Nat
--   listProduct Nil = 1
--   listProduct (Cons x xs) = x * listProduct xs
  
--   wpProduct : ∀ {a b : Set} ->
--     (d : b) -> (a -> Maybe b) -> (a -> b -> Set) -> (a -> Set)
--   wpProduct d c P x = handleDefault d (P x) (c x)

--   fastSpec : List Nat -> Nat -> Set
--   fastSpec xs n = listProduct xs == n

--   correctness : (xs : List Nat) ->
--     wpProduct Zero fastProduct fastSpec xs
--   correctness Nil = Refl
--   correctness (Cons Zero xs) = Refl
--   correctness (Cons (Succ k) xs) = {!!}
--   --   with fastProduct xs | listProduct xs | correctness xs
--   -- correctness (Cons (Succ k) xs) | Pure x | .x | Refl
--   --   = Refl
--   -- correctness (Cons (Succ k) xs) | Step Nothing x | .Zero | Refl
--   --   = zero-cancellative k

--   data Expr : Set where
--     Val : Nat -> Expr
--     Div : Expr -> Expr -> Expr

--   div : Nat -> Nat -> Maybe (Nat)
--   div n k = {!!}
  
--   ⟦_⟧ : Expr -> Maybe Nat
--   ⟦ Val x ⟧ = return x
--   ⟦ Div e e' ⟧ =  ⟦ e ⟧ >>= \x ->
--                  ⟦ e' ⟧ >>= \y ->
--                  div x y

--   mywp : (Nat -> Set) -> (Expr -> Set)
--   mywp P e = handle P ⟦ e ⟧

--   atLeast3 : (e : Expr) -> handle (\n -> 1 < n) ⟦ e ⟧
--   atLeast3 (Val x) = {!!}
--   atLeast3 (Div e e₁) = {!!}


