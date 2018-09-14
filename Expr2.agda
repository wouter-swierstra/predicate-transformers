{-#  OPTIONS --type-in-type  #-}

module Expr2 where

open import Prelude
open import Level hiding (lift)

module Free where
  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
  fmap : forall {  C R a b } ->  (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x)    = Pure (f x)
  fmap f (Step c k)  = Step c (\ r -> fmap f (k r)) 

  return : forall {  C R a } ->  a -> Free C R a
  return = Pure
  _>>=_ : forall {  C R a b } ->  Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x   >>= f  = f x
  Step c x >>= f  = Step c (\ r -> x r >>= f)
  _⊆_ : {a : Set} -> (a -> Set) -> (a -> Set) -> Set
  P ⊆ Q = ∀ x -> P x -> Q x  
  wp : {a : Set} {b : a -> Set} -> (f : (x : a) -> b x) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wp f P = \ a -> P a (f a)
  _⊑_ : {a : Set} {b : a -> Set} (f g : (x : a) -> b x) -> Set1 
  _⊑_ {a} {b} f g = ((P : (x : a) -> b x -> Set) (x : a) -> wp f P x -> wp g P x)

module Maybe where

  open Free hiding (_⊑_)
  postulate
    _div_ : Nat -> Nat -> Nat
  data C : Set where
    Abort : C

  R : C -> Set
  R Abort = ⊥

  Partial : Set -> Set
  Partial = Free C R
  abort  : forall { a } ->  Partial a
  abort  = Step Abort (\ ())
  data Expr : Set where
    Val : Nat -> Expr
    Div : Expr -> Expr -> Expr
  ⟦_⟧ : Expr -> Partial Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    v1 ÷ v2
                      where
                      _÷_ : Nat -> Nat -> Partial Nat
                      n ÷ Zero      = abort
                      n ÷ (Succ k)  = return (n div (Succ k))
  data _⇓_ : Expr -> Nat -> Set where
    Base : forall { x } ->  Val x ⇓ x
    Step : forall { l r v1 v2 } ->  l ⇓ v1 -> r ⇓ (Succ v2) -> Div l r ⇓ (v1 div (Succ v2))

  mustPT : forall { a : Set } ->  {b : a -> Set} -> (P : (x : a) -> b x -> Set) -> (x : a) -> Partial (b x) -> Set
  mustPT P _ (Pure x)          = P _ x
  mustPT P _ (Step Abort _)    = ⊥

  wpPartial : { a : Set} -> { b : a -> Set} -> (f : (x : a) -> Partial (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpPartial f P = wp f (mustPT P)

  SafeDiv : Expr -> Set
  SafeDiv (Val x)       = (Val x ⇓ Zero) -> ⊥
  SafeDiv (Div e1 e2)   = (e2 ⇓ Zero -> ⊥) × SafeDiv e1 × SafeDiv e2
  correct : (e : Expr) -> SafeDiv e -> wpPartial ⟦_⟧ _⇓_ e
  correct (Val x) h = Base
  correct (Div e1 e2 ) (nz , (h1 , h2)) with ⟦ e1 ⟧ | ⟦ e2 ⟧ | correct e1 h1 | correct e2 h2
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure v1 | Pure Zero | ih1 | ih2 = magic (nz ih2)
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure v1 | Pure (Succ v2) | ih1 | ih2 = Step ih1 ih2
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure x | Step Abort x₁ | ih1 | ()
  correct (Div e1 e2) (nz , (h1 , h2)) | Step Abort x | v2 | () | ih2
  dom : {a : Set} -> { b : a -> Set} -> ((x : a) -> Partial (b x)) -> (a -> Set)
  dom f = wpPartial f (\ _ _ -> ⊤)
  complete  : wpPartial ⟦_⟧ _⇓_    ⊆   dom ⟦_⟧
  sound     : dom ⟦_⟧              ⊆   wpPartial ⟦_⟧ _⇓_
  sound (Val x) h = Base
  sound (Div e1 e2) h with ⟦ e1 ⟧ | ⟦ e2 ⟧ | sound e1 | sound e2
  sound (Div e1 e2) () | Pure v1 | Pure Zero | ih1 | ih2
  sound (Div e1 e2) h | Pure v1 | Pure (Succ v2) | ih1 | ih2 = Step (ih1 tt) (ih2 tt)
  sound (Div e1 e2) () | Pure x | Step Abort x₁ | ih1 | ih2
  sound (Div e1 e2) () | Step Abort x | v2 | ih1 | ih2

  inDom : {v : Nat} -> (e : Expr) -> ⟦ e ⟧ == Pure v -> dom ⟦_⟧ e
  inDom (Val x) h = tt
  inDom (Div e1 e2) h with ⟦ e1 ⟧ | ⟦ e2 ⟧
  inDom (Div e1 e2) () | Pure v1 | Pure Zero
  inDom (Div e1 e2) h | Pure v1 | Pure (Succ v2) = tt
  inDom (Div e1 e2) () | Pure _ | Step Abort _
  inDom (Div e1 e2) () | Step Abort _ | _

  wpPartial1 : {e1 e2 : Expr} -> wpPartial ⟦_⟧ _⇓_ (Div e1 e2) -> wpPartial ⟦_⟧ _⇓_ e1
  wpPartial1 {e1} {e2} h with inspect ⟦ e1 ⟧
  wpPartial1 {e1} {e2} h | Pure x with-≡ eq = sound e1 (inDom e1 eq)
  wpPartial1 {e1} {e2} h | Step Abort x with-≡ eq rewrite eq = magic h

  wpPartial2 : {e1 e2 : Expr} -> wpPartial ⟦_⟧ _⇓_ (Div e1 e2) -> wpPartial ⟦_⟧ _⇓_ e2
  wpPartial2 {e1} {e2} h with inspect ⟦ e1 ⟧ | inspect ⟦ e2 ⟧
  wpPartial2 {e1} {e2} h | Pure v1 with-≡ eq1 | Pure v2 with-≡ eq2
    = sound e2 (inDom e2 eq2)
  wpPartial2 {e1} {e2} h | Pure _ with-≡ eq1 | Step Abort _ with-≡ eq2
    rewrite eq1 | eq2 = magic h
  wpPartial2 {e1} {e2} h | Step Abort x with-≡ eq | _ rewrite eq = magic h

  complete (Val x) h = tt
  complete (Div e1 e2) h
    with inspect ⟦ e1 ⟧ | inspect ⟦ e2 ⟧
      | complete e1 (wpPartial1 {e1} {e2} h)
      | complete e2 (wpPartial2 {e1} {e2} h)
  complete (Div e1 e2) h | Pure v1 with-≡ eq1 | Pure Zero with-≡ eq2 | ih1 | ih2
    rewrite eq1 | eq2 = magic h
  complete (Div e1 e2) h | Pure v1 with-≡ eq1 | Pure (Succ v2) with-≡ eq2 | ih1 | ih2
    rewrite eq1 | eq2 = tt 
  complete (Div e1 e2) h | Pure _ with-≡ _ | Step Abort _ with-≡ eq | _ | ih2
    rewrite eq = magic ih2
  complete (Div e1 e2) h | Step Abort _ with-≡ eq | _ | ih1 | _
    rewrite eq = magic ih1

  data I {a : Set} (b : a -> Set) : Set1 where
    Done : ({x : a} -> b x) -> I b
    Spec : (pre : a -> Set) -> (post : (x : a) -> b x -> Set) -> I b

  M : {a : Set} -> (a -> Set) -> Set1
  M b = Partial (I b)

  spec : ∀ {a} {b : a -> Set} -> (P : a -> Set) -> (Q : (x : a) -> b x -> Set) -> M b
  spec P Q = Pure (Spec P Q)

  wpI : {a : Set} -> {b : a -> Set} -> (P : (x : a) -> b x -> Set) -> (x : a) -> I b -> Set
  wpI P i (Done o)  = P i o
  wpI {a} {b} P i (Spec pre post)  =
    Pair
      (pre i)
      (post i ⊆ P i) -- or should that be forall i...
                     -- or should it say that forall inputs, satisfying the precondition, etc.
                     -- cf indexed containers

  wpM : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M b) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpM f = wp f · mustPT · wpI

  record _⊑_ {a : Set} {b : a -> Set} (f g : (x : a) -> M b) : Set1 where
     constructor refinement
     field
       proof : (∀ P -> (i : a) -> (H : wpM f P i) -> wpM g P i)

  ⊑-refl : ∀ {a} {b : a -> Set} -> (f : (x : a) -> M b) -> f ⊑ f
  ⊑-refl f = refinement \P x H -> H

  ⊑-trans : ∀ {a} {b : a -> Set} -> {f g h : (x : a) -> M b} -> f ⊑ g -> g ⊑ h -> f ⊑ h
  ⊑-trans (record { proof = step1 }) (record { proof = step2 }) =
    refinement \P H x -> step2 P H (step1 P H x)

  strengthenPost : {a : Set} {b : a -> Set} (S1 S2 : (x : a) -> b x -> Set) (Pre : a -> Set) ->
    ((x : a) -> S2 x ⊆ S1 x) ->
    (\x -> spec Pre S1) ⊑ \x -> spec Pre S2
  strengthenPost S1 S2 Pre H = refinement λ { P x (fst , snd) → fst , λ bx s2 → snd bx (H _ bx s2)}

  infixr 2 _⟨_⟩_
  _⟨_⟩_ : forall {a : Set} {b : a -> Set}
    (f : (x : a) -> M (b)) -> {g h : (x : a) -> M (b)} -> (f ⊑ g) -> (g ⊑ h) -> f ⊑ h
  _⟨_⟩_ f {g} {h} step1 step2 = ⊑-trans {f = f} {g = g} {h = h} step1 step2

  _■ : forall {a : Set} {b : a -> Set} (f : (x : a) -> M (b)) -> f ⊑ f
  _■ f = ⊑-refl f

  Stack = List

  pop : ∀ {a} -> Stack a -> Partial (Pair a (Stack a))
  pop Nil = abort
  pop (Cons x xs) = return (x , xs)

  PopSpec : Stack Nat -> (Pair Nat (Stack Nat)) -> Set
  PopSpec xs (y , ys) = xs == Cons y ys

  K : {a : Set} -> Set -> (a -> Set)
  K A _ = A

  popSpec : (xs : Stack Nat) -> M {Stack Nat} (\_ -> Pair Nat (Stack Nat))
  popSpec xs = spec (\q -> q == Nil -> ⊥) PopSpec

  fromCode : ∀ {a b : Set} -> (Partial a) -> M {b} (\_ -> a)
  fromCode (Pure y) = Pure (Done y)
  fromCode (Step Abort x) = Step Abort \()

  popCorrect : popSpec ⊑ \xs -> fromCode {Pair Nat (Stack Nat)} (pop xs)
  popCorrect = refinement λ { P Nil (fst , snd) → magic (fst Refl)
                            ; P (Cons x xs) (fst , snd) → snd _ Refl}

  data AddSpec : Stack Nat -> Stack Nat -> Set where
    AddThem : ∀ {x1 x2 : Nat} {xs : Stack Nat} -> AddSpec (Cons x1 (Cons x2 xs)) (Cons (x1 + x2) xs)

  null? : Stack Nat -> Set
  null? Nil = ⊤
  null? _ = ⊥

  single? : Stack Nat -> Set
  single? Nil = ⊥
  single? (Cons x xs) = null? xs
  
  addSpec : Stack Nat -> M {Stack Nat} (\_ -> Stack Nat)
  addSpec (xs) = spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) AddSpec

  add : Stack Nat -> M {Stack Nat} (\_ -> Stack Nat)
  add xs =
    pop xs >>= \{ (x1 , xs) -> 
    pop xs >>= \{ (x2 , xs) ->
    return (Done (Cons (x1 + x2) xs))}}

  addCorrect : addSpec ⊑ add
  addCorrect = refinement prf
    where
    prf : (P : Stack Nat -> Stack Nat -> Set) -> wpM addSpec P ⊆ wpM add P
    prf P Nil ((fst , _) , _) = fst _
    prf P (Cons x Nil) ((_ , snd) , _) = snd _
    prf P (Cons x (Cons x₁ xs)) H = Pair.snd H _ AddThem

 -- Can we do calculation in this style?

  explicitDerivation : addSpec ⊑ add
  explicitDerivation =
    addSpec
      ⟨ step1 ⟩
    (\xs -> pop xs >>= \ { (x1 , xs) -> spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) (AddSpec)})
      ⟨ step2 ⟩
    (\xs -> pop xs >>= \ { (x1 , xs) ->
            pop xs >>= \ { (x2 , xs) ->
            spec (\xs -> ⊤) (AddSpec)}})
      ⟨ step3 ⟩
    add ■
      where
        step1 : addSpec ⊑ (\xs -> pop xs >>= \ { (x1 , xs) -> spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) ((\as bs -> AddSpec as bs))})
        step1 = refinement λ { P Nil ((fst , _) , snd) → magic (fst _)
                             ; P (Cons x Nil) ((_ , fst) , snd) → magic (fst _)
                             ; P (Cons x (Cons x₁ xs)) (H , snd) → H , snd}
        step2 : (\xs -> pop xs >>= \ { (x1 , xs) -> spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) AddSpec})
                ⊑
                (\xs -> pop xs >>= \ { (x1 , xs) ->
                        pop xs >>= \ { (x2 , xs) ->
                        spec (\xs -> ⊤) AddSpec}})
        step2 = refinement λ { P Nil ()
                             ; P (Cons x Nil) ((_ , fst) , snd) → magic (fst _)
                             ; P (Cons x (Cons x₁ i)) (fst , snd) → tt , snd}
        step3 : (\xs -> pop xs >>= \ { (x1 , xs) ->
                        pop xs >>= \ { (x2 , xs) ->
                        spec (\xs -> ⊤) AddSpec}})
                ⊑ add
        step3 = refinement λ { P Nil ()
                             ; P (Cons x Nil) ()
                             ; P (Cons x1 (Cons x2 xs)) (fst , snd) → snd (Cons (x1 + x2) xs) AddThem}

 --  -- Rephrasing things a bit...

 --  Σ : (a : Set) -> (b : a -> Set) -> Set
 --  Σ = Sigma

 --  popM : Stack Nat -> M (Pair Nat (Stack Nat))
 --  popM xs = pop xs >>= λ x → Pure (Done x)

 --  _>=>_ : ∀ {a b c} -> (I a -> M b) -> (I b -> M c) -> (I a -> M c)
 --  _>=>_ c1 c2 = \x ->  c1 x >>= c2

 --  popIt : (S : Stack Nat -> Stack Nat -> Set) ->
 --          Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
 --            (\g -> 
 --              (P : Stack Nat -> Stack Nat -> Set) ->
 --              wpM (spec · S) P ⊆ wpM (\xs -> pop xs >>= g) P) ->
 --          Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · S) ⊑ f)
 --  popIt S (g , H) = (\xs -> pop xs >>= g) , refinement H


 --  returnStep : ∀ {P : Stack Nat -> Stack Nat -> Set} ->
 --    ((xs : Stack Nat) -> P xs xs) ->
 --    Σ (Stack Nat -> M (Stack Nat)) (\f -> (\x -> spec (P x)) ⊑ f)    
 --  returnStep H = (\xs -> Pure (Done xs)) , refinement λ { P ys (fst , snd) → snd ys (H ys)}

 --  popStep : (S : Stack Nat -> Stack Nat -> Set) ->
 --          (S' : Pair Nat (Stack Nat) -> Stack Nat -> Set) ->
 --          ((x : Nat) (xs : Stack Nat) -> S (Cons x xs) ⊆ S' (x , xs)) ->
 --          ((x : Nat) (xs : Stack Nat) -> S' (x , xs) ⊆ S (Cons x xs)) ->          
 --          Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
 --            (\g -> (spec · S') ⊑ g) ->
 --          Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · S) ⊑ f)
 --  popStep S S' H1 H2 (g , proof) =
 --    (\xs -> pop xs >>= g) , {!!}


 --  derivation : Σ (Stack Nat -> M (Stack Nat)) (\f -> addSpec ⊑ f)
 --  derivation =  {!!}

 --  feasible : {a : Set} -> {b : a -> Set} ->
 --    (f : (x : a) -> M (b x)) -> Set
 --  feasible {a} f = (x : a) -> wp f (\_ _ -> ⊥) x == ⊥

 --  infeasible : {a : Set} -> {b : a -> Set} ->
 --    (f : (x : a) -> M (b x)) -> Set
 --  infeasible f = feasible f -> ⊥

