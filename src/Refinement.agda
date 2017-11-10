module Refinement where

open import Level hiding (lift)
open import Prelude

module Total where
  wp : {l : Level} {a b : Set l} ->
    (f : a -> b) -> (b -> Set l) -> (a -> Set l)
  wp f P = \x -> P (f x)

  -- Two total functions are a related by a refinement if and only iff
  --  they are equal on all points

  _⊑_ : {l : Level} -> {a b : Set l} ->
    (f g : a -> b) -> Set (suc l)
  _⊑_ {l} {a = a} {b = b} f g =
    (P : b -> Set l) -> (x : a) -> wp f P x -> wp g P x

  ⊑-eq : {l : Level} -> {a b : Set l} ->
    (f g : a -> b) -> f ⊑ g -> (x : a) -> f x == g x
  ⊑-eq f g R x = R (\y -> f x == y) x Refl

  eq-⊑ :  {l : Level} -> {a b : Set l} ->
    (f g : a -> b) -> ((x : a) -> f x == g x) ->  f ⊑ g
  eq-⊑ f g eq P x H with f x | g x | eq x
  ... | _ | _ | Refl = H

module Maybe where
  data Maybe (a : Set) : Set where
    Just : a -> Maybe a
    Nothing : Maybe a

  lift : {a : Set} -> (a -> Set) -> Maybe a -> Set
  lift P (Just x) = P x
  lift P Nothing = ⊥

  wp : {a b : Set} ->
    (f : a -> Maybe b) -> (b -> Set) -> (a -> Set)
  wp f P x = lift P (f x)

  _⊑_ : {a b : Set} ->
    (f g : a -> Maybe b) -> Set₁
  f ⊑ g = ∀ P x -> wp f P x -> wp g P x

  LT : ∀ {a b} (f g : a -> Maybe b) -> Set
  LT {a} {b} f g = (x : a) ->
    Either (f x == g x) (f x == Nothing)

  ⊑-eq : {a b : Set} ->
    (f g : a -> Maybe b) -> f ⊑ g -> LT f g
  ⊑-eq f g R x with f x | g x | R (\y -> f x == Just y) x
  ⊑-eq f g R x | Just y | Just x₁ | H = Inl (H Refl)
  ⊑-eq f g R x | Just y | Nothing | H = magic (H Refl)
  ⊑-eq f g R x | Nothing | _ | H = Inr Refl

  eq-⊑ : {a b : Set} ->
    (f g : a -> Maybe b) -> LT f g ->  f ⊑ g
  eq-⊑ f g eq P x H with f x | g x | eq x 
  eq-⊑ f g eq P x H | Just y | Just .y | Inl Refl = H
  eq-⊑ f g eq P x H | Just y | Nothing | Inl ()
  eq-⊑ f g eq P x H | Just y | _ | Inr ()
  eq-⊑ f g eq P x () | Nothing | _ | _

module Nondet where

  data ND (a : Set) : Set where
    Return : a -> ND a
    Join : ND a -> ND a -> ND a
    Fail : ND a

  module RefineAll where

    lift : ∀ {a} (P : a -> Set) -> ND a -> Set
    lift P (Return x) = P x
    lift P (Join l r) = Pair (lift P l) (lift P r)
    lift P Fail = ⊤

    wp : {a b : Set} ->
      (f : a -> ND b) -> (b -> Set) -> (a -> Set)
    wp f P x = lift P (f x)

    _⊑_ : {a b : Set} ->
      (f g : a -> ND b) -> Set₁
    _⊑_ {a = a} {b = b} f g =
      (P : b -> Set) -> (x : a) -> wp f P x -> wp g P x

    data Elem {a : Set} (x : a) : ND a -> Set where
      Here : Elem x (Return x)
      Left : ∀ {l r} -> Elem x l -> Elem x (Join l r)
      Right : ∀ {l r} -> Elem x r -> Elem x (Join l r)      

    R : ∀ {a} -> ND a -> ND a -> Set
    R (Return x) nd = Elem x nd
    R (Join nd1 nd2) nds = Either (R nd1 nds) (R nd2 nds)
    R Fail nd2 = ⊤


    ⊑-R : {a b : Set} ->
      (f g : a -> ND b) -> f ⊑ g -> (x : a) -> R (f x) (g x)
    ⊑-R f g H x with f x | g x | H (\y -> Elem y (f x) ) x
    ⊑-R f g H x | Return y | Return y' | p = {!!}
    ⊑-R f g H x | Return y | Join gx gx₁ | p = {!p!}
    ⊑-R f g H x | Return y | Fail | p = {!!}
    ⊑-R f g H x | Join fx fx₁ | gx | p = {!!}
    ⊑-R f g H x | Fail | gx | p = tt

    R-⊑ : {a b : Set} ->
      (f g : a -> ND b) -> ((x : a) -> R (f x) (g x)) -> f ⊑ g
    R-⊑ f g H P x y with f x | g x | H x
    R-⊑ f g H P x y | Return x₁ | Return .x₁ | Here = y
    R-⊑ f g H P x y | Return X | Join l nd2 | Left h = {!!}
    R-⊑ f g H P x y | Return X | Join l nd2 | Right h = {!!}
    R-⊑ f g H P x y | Return x₁ | Fail | h = {!!}
    R-⊑ f g H P x y | Join fx fx₁ | gx | h = {!!}
    R-⊑ f g H P x y | Fail | gx | h = {!!}


  module RefineAny where

    lift : ∀ {a} (P : a -> Set) -> ND a -> Set
    lift P (Return x) = P x
    lift P (Join l r) = Either (lift P l) (lift P r)
    lift P Fail = ⊥

    wp : {a b : Set} ->
      (f : a -> ND b) -> (b -> Set) -> (a -> Set)
    wp f P x = lift P (f x)

    _⊑_ : {a b : Set} ->
      (f g : a -> ND b) -> Set₁
    _⊑_ {a = a} {b = b} f g =
      (P : b -> Set) -> (x : a) -> wp f P x -> wp g P x

    data Elem {a : Set} (x : a) : ND a -> Set where
      Here : Elem x (Return x)
      Left : ∀ {l r} -> Elem x l -> Elem x (Join l r)
      Right : ∀ {l r} -> Elem x r -> Elem x (Join l r)      

    R : ∀ {a} -> ND a -> ND a -> Set
    R (Return x) nd = Elem x nd
    R (Join nd1 nd2) nds = Either (R nd1 nds) (R nd2 nds)
    R Fail nd2 = ⊤


    ⊑-R : {a b : Set} ->
      (f g : a -> ND b) -> f ⊑ g -> (x : a) -> R (f x) (g x)
    ⊑-R f g H x with f x | g x | H {!!} x
    ... | fx | gx | p = {!!}

    R-⊑ : {a b : Set} ->
      (f g : a -> ND b) -> ((x : a) -> R (f x) (g x)) -> f ⊑ g
    R-⊑ f g H P x p with f x | g x | H x
    R-⊑ f g H P x p | Return y | Return .y | Here = p
    R-⊑ f g H P x p | Return y | Join l r | Left z =
      Inl {!!}
    R-⊑ f g H P x p | Return y | Join l r | Right z =
      Inr {!!}
    R-⊑ f g H P x p | Return y | Fail | ()
    R-⊑ f g H P x p | Join fx fx₁ | gx | z = {!!}
    R-⊑ f g H P x p | Fail | gx | z = {!!}
