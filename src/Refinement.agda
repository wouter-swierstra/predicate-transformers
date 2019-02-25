module Refinement where

open import Level hiding (lift)
open import Prelude

module Total where
  wp : {l : Level} {a b : Set l} ->
    (f : a -> b) -> (b -> Set l) -> (a -> Set l)
  wp f P = \x -> P (f x)

  _⊑_ : {l : Level} -> {a b : Set l} ->
    (f g : a -> b) -> Set (suc l)
  _⊑_ {l} {a = a} {b = b} f g =
    (P : b -> Set l) -> (x : a) -> wp f P x -> wp g P x

  -- Two total functions are a related by a refinement if and only iff
  --  they are equal on all points
  ⊑-eq : {l : Level} -> {a b : Set l} ->
    (f g : a -> b) -> f ⊑ g -> (x : a) -> f x == g x
  ⊑-eq f g R x = R (\y -> f x == y) x refl

  eq-⊑ :  {l : Level} -> {a b : Set l} ->
    (f g : a -> b) -> ((x : a) -> f x == g x) ->  f ⊑ g
  eq-⊑ f g eq P x H with f x | g x | eq x
  ... | _ | _ | refl = H

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

  -- given two partial functions f and g,
  -- f ⊑ g if and only if dom(f) subset dom(g) and they
  -- agree on the domain of f
  LT : ∀ {a b} (f g : a -> Maybe b) -> Set
  LT {a} {b} f g = (x : a) ->
    Either (f x == g x) (f x == Nothing)

  ⊑-eq : {a b : Set} ->
    (f g : a -> Maybe b) -> f ⊑ g ->     Either (f x == g x) (f x == Nothing)

  ⊑-eq f g R x with f x | g x | R (\y -> f x == Just y) x
  ⊑-eq f g R x | Just y | Just x₁ | H = Inl (H refl)
  ⊑-eq f g R x | Just y | Nothing | H = magic (H refl)
  ⊑-eq f g R x | Nothing | _ | H = Inr refl

  eq-⊑ : {a b : Set} ->
    (f g : a -> Maybe b) ->     Either (f x == g x) (f x == Nothing)  ->  f ⊑ g
  eq-⊑ f g eq P x H with f x | g x | eq x
  eq-⊑ f g eq P x H | Just y | Just .y | Inl refl = H
  eq-⊑ f g eq P x H | Just y | Nothing | Inl ()
  eq-⊑ f g eq P x H | Just y | _ | Inr ()
  eq-⊑ f g eq P x () | Nothing | _ | _

module Nondet where

  data ND (a : Set) : Set where
    Return : a -> ND a
    Amb : ND a -> ND a -> ND a
    Fail : ND a

  data Elem {a : Set} (x : a) : ND a -> Set where
      Here : Elem x (Return x)
      Left : ∀ {l r} -> Elem x l -> Elem x (Amb l r)
      Right : ∀ {l r} -> Elem x r -> Elem x (Amb l r)

  Subset : ∀ {a : Set} -> (f g : ND a) -> Set
  Subset {a} nd1 nd2 = (y : a) -> Elem y nd2 -> Elem y nd1

  module RefineAll where

    allPT : ∀ {a} (P : a -> Set) -> ND a -> Set
    allPT P (Return x) = P x
    allPT P (Amb l r) = Pair (allPT P l) (allPT P r)
    allPT P Fail = ⊤

    wp : {a b : Set} ->
      (f : a -> ND b) -> (b -> Set) -> (a -> Set)
    wp f P x = allPT P (f x)

    _⊑_ : {a b : Set} ->
      (f g : a -> ND b) -> Set₁
    _⊑_ {a = a} {b = b} f g =
      (P : b -> Set) -> wp f P ⊆ wp g P


    mapAllPT : ∀ {a} {P Q : a -> Set} (nd : ND a) -> P ⊆ Q -> allPT P nd -> allPT Q nd
    mapAllPT (Return x) H all = H x all
    mapAllPT (Amb nd nd') H (all , all') = mapAllPT nd H all , mapAllPT nd' H all'
    mapAllPT Fail H all = tt

    allPT-Elem : ∀ {a} -> (nd : ND a) -> allPT (\x -> Elem x nd) nd
    allPT-Elem (Return x) = Here
    allPT-Elem (Amb nd nd') = mapAllPT nd (λ x y → Left y) (allPT-Elem nd)
                            , mapAllPT nd' (λ x y → Right y) (allPT-Elem nd')
    allPT-Elem Fail = tt

    lookup : {a : Set} {P : a -> Set} {x : a} -> (nd : ND a) -> allPT P nd -> Elem x nd -> P x
    lookup (Return x₁) all Here = all
    lookup (Amb nd1 nd2) (all1 , all2) (Left elem) = lookup nd1 all1 elem
    lookup (Amb nd1 nd2) (all1 , all2) (Right elem) = lookup nd2 all2 elem
    lookup Fail all ()

    allPT-ext : {a : Set} {P : a -> Set} ->
      (nd : ND a) -> ((x : a) -> Elem x nd -> P x) -> allPT P nd
    allPT-ext (Return x) H = H x Here
    allPT-ext (Amb nd1 nd2) H = (allPT-ext nd1 (\x e -> H x (Left e))
                              , (allPT-ext nd2 \x e -> H x (Right e)))
    allPT-ext Fail H = tt

    allPT-subset : {a : Set} {nd1 nd2 : ND a} {P : a -> Set} ->
      ((x : a) → Elem x nd1 → Elem x nd2) ->
      allPT P nd2 -> allPT P nd1
    allPT-subset {nd1 = nd1} {nd2 = nd2} elems all =
      allPT-ext nd1 (\x e -> lookup nd2 all (elems x e))

    -- For two non-deterministic computations f g : a -> ND b,
    -- f ⊑ g if and only if forall x, (g x) is a subset of (f x)    
    ⊑-Subset : {a b : Set} ->
      (f g : a -> ND b) -> f ⊑ g -> (x : a) -> Subset (f x) (g x)
    ⊑-Subset {a} {b} f g h x y elem =
      let H = h (\y -> Elem y (f x)) x (allPT-Elem (f x)) in
      lookup (g x) H elem 

    Subset-⊑ : {a b : Set} ->
      (f g : a -> ND b) -> ((x : a) -> Subset (f x) (g x)) -> f ⊑ g
    Subset-⊑ {a} {b} f g H P x y = allPT-subset {b} {g x} {f x} (H x) y

  module RefineAny where

    anyPT : ∀ {a} (P : a -> Set) -> ND a -> Set
    anyPT P (Return x) = P x
    anyPT P (Amb l r) = Either (anyPT P l) (anyPT P r)
    anyPT P Fail = ⊥

    wp : {a b : Set} ->
      (f : a -> ND b) -> (b -> Set) -> (a -> Set)
    wp f P x = anyPT P (f x)

    _⊑_ : {a b : Set} ->
      (f g : a -> ND b) -> Set₁
    _⊑_ {a = a} {b = b} f g =
      (P : b -> Set) -> (x : a) -> wp f P x -> wp g P x

    exists : {a : Set} {x : a} {P : a -> Set}
      (nd : ND a) (elem : Elem x nd) -> P x -> anyPT P nd
    exists (Return x) Here px = px
    exists (Amb nd1 nd2) (Left elem) px = Inl (exists nd1 elem px)
    exists (Amb nd1 nd2) (Right elem) px = Inr (exists nd2 elem px)
    exists Fail () px

    lookup : {a : Set} {P : a -> Set}
      (nd : ND a) -> anyPT P nd -> Sigma a (\x -> Pair (P x) (Elem x nd))
    lookup (Return x) any = x , (any , Here)
    lookup (Amb nd1 nd2) (Inl x) = let (x , (p , e)) = lookup nd1 x in x , (p , (Left e))
    lookup (Amb nd1 nd2) (Inr x) = let (x , (p , e)) = lookup nd2 x in x , (p , (Right e))
    lookup Fail ()      

    -- For two non-deterministic computations f g : a -> ND b,
    -- f ⊑ g if and only if forall x, (g x) is a subset of (f x)    
    ⊑-R : {a b : Set} ->
      (f g : a -> ND b) -> f ⊑ g -> (x : a) -> Subset (g x) (f x)
    ⊑-R {a} {b} f g h x y elem with
      let IH = (h (_==_ y) x (exists (f x) elem refl)) in lookup (g x) IH
    ⊑-R {a} {b} f g h x y elem | .y , (refl , p) = p
    
    R-⊑ : {a b : Set} ->
      (f g : a -> ND b) -> ((x : a) -> Subset (g x) (f x)) -> f ⊑ g
    R-⊑ f g H P x p =
      let (w , (pw , elw)) = lookup (f x) p in
      exists (g x) (H x w elw) pw

