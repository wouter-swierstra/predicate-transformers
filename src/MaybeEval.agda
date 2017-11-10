module MaybeEval where

open import Prelude
open import Level hiding (lift)



module Free where
  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
  fmap : forall {  C R a b } ->  (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x) = Pure (f x)
  fmap f (Step c k) = Step c (\r -> fmap f (k r)) 

  return : forall {  C R a } ->  a -> Free C R a
  return = Pure
  _>>=_ : forall {  C R a b } ->  Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x   >>= f  = f x
  Step c x >>= f  = Step c (\r -> x r >>= f)
  fold : forall { C R a l } ->  {b : Set l} -> ((c : C) -> (R c -> b) -> b) -> (a -> b) -> Free C R a -> b
  fold alg pure (Pure x) = pure x
  fold alg pure (Step c k) = alg c (\ r -> fold alg pure (k r))
module Maybe where

  open Free
  data C : Set where
    Nothing : C

  R : C -> Set
  R Nothing = ⊥

  Maybe : Set -> Set
  Maybe = Free C R
  just     : forall { a } ->  a -> Maybe a
  just     = Pure

  nothing  : forall { a } ->  Maybe a
  nothing  = Step Nothing (\ ())
  lift : forall { a } ->  (P : a -> Set) -> Maybe a -> Set
  lift P (Pure x)          = P x
  lift P (Step Nothing _)  = ⊥
  data Expr : Set where
    Val : Nat -> Expr
    Div : Expr -> Expr -> Expr

  totalDiv : Nat -> Nat -> Nat
  totalDiv n k = {!!}

  div : Nat -> Nat -> Maybe Nat
  div n Zero = nothing
  div n (Succ k) = just (totalDiv n k)
  
  ⟦_⟧ : Expr -> Maybe Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    div v1 v2
--  wp : (Nat -> Set) -> (Expr -> Set)
--  wp P e = lift P ⟦ e ⟧
--  dom : Expr -> Set
--  dom = wp (\ _ -> ⊤)
--  test1 : dom (Val 3) == ⊤
--  test2 : dom (Div (Val 1) (Val 0)) == ⊥
--  test1 = Refl
--  test2 = Refl
  run : forall {  a } ->  a -> Maybe a -> a
  run d (Pure x)          = x
  run d (Step Nothing _)  = d


  data _⇓_ : Expr -> Nat -> Set where
    Base : ∀ {x} -> Val x ⇓ x
    Step : ∀ {l r x y} -> l ⇓ x -> r ⇓ (Succ y) ->
           Div l r ⇓ totalDiv x y

  correct : (e : Expr) -> lift (\n -> e ⇓ n) ⟦ e ⟧
  correct (Val x) = Base
  correct (Div l r) with ⟦ l ⟧ | ⟦ r ⟧ | correct l | correct r
  correct (Div l r) | Pure x | Pure Zero | p | q = {!!}
  correct (Div l r) | Pure x | Pure (Succ y) | p | q = Step p q
  correct (Div l r) | Pure x | Step Nothing x₁ | p | ()
  correct (Div l r) | Step Nothing x | y | p | q = p

  
  _⊆_ : {l : Level} {a : Set l} ->
    (R1 R2 : a -> Set l) -> Set l
  _⊆_ {a = a} R1 R2 =
    (x : a) -> R1 x -> R2 x 

  wpR : {l : Level} {a b : Set l} ->
    (R : a -> b -> Set l) -> (b -> Set l) -> (a -> Set l)
  wpR {b = b} R Q x = R x ⊆ Q 

  wp : {a b : Set} ->
    (a -> Maybe b) -> (b -> Set) -> (a -> Set)
  wp f P x = lift P (f x)

  _⊑_ : {a b : Set} ->
    (R R' : (b -> Set) -> (a -> Set)) -> Set₁
  _⊑_ {a = a} {b = b} R R' = (P : b -> Set) -> R P ⊆ R' P

  correct' : (wpR _⇓_) ⊑ (wp ⟦_⟧)
  correct' P (Val x) H = H x Base
  correct' P (Div l r) H = {!!}
  
