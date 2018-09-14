{-#  OPTIONS --type-in-type  #-}

module Expr where

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

  data I (a : Set) : Set1 where
    Done : a -> I a
    Spec : (a -> Set) -> I a

  M : Set -> Set1
  M a = Partial (I a)

  isCode : ∀ {a} -> M a -> Set
  isCode (Pure (Done x)) = ⊤
  isCode (Pure (Spec x)) = ⊥
  isCode (Step Abort x) = ⊤

  
  done : ∀ {a} -> (m : M a) -> isCode m -> Partial a
  done (Pure (Done x)) p = Pure x
  done (Pure (Spec x)) ()
  done (Step Abort k) p = Step Abort λ ()

  fromCode : ∀ {a} -> Partial a -> M a
  fromCode (Pure x) = Pure (Done x)
  fromCode (Step Abort x) = Step Abort \()

  spec : ∀ {a} -> (P : a -> Set) -> M a
  spec P = Pure (Spec P)

  existsC : (a : Set) (b : a -> Set) -> Set
  existsC a b = Not ((x : a) -> Not (b x))

  wpI : {a : Set} -> {b : a -> Set} -> (P : (x : a) -> b x -> Set) -> (x : a) -> I (b x) -> Set
  wpI P i (Done o)  = P i o
  wpI {a} {b} P i (Spec Q)  =
    Pair
      (existsC (b i) Q)
      (Q ⊆ P i)

  wpM : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpM f = wp f · mustPT · wpI


  record _⊑_ {a : Set} {b : a -> Set} (f g : (x : a) -> M (b x)) : Set1 where
    constructor refinement
    field
      proof : (∀ P -> wpM f P ⊆ wpM g P)

  ⊑-refl : ∀ {a} {b : a -> Set} -> (f : (x : a) -> M (b x)) -> f ⊑ f
  ⊑-refl f = refinement \P x H -> H

  ⊑-trans : ∀ {a} {b : a -> Set} -> {f g h : (x : a) -> M (b x)} -> f ⊑ g -> g ⊑ h -> f ⊑ h
  ⊑-trans (record { proof = step1 }) (record { proof = step2 }) =
    refinement \P H x -> step2 P H (step1 P H x)

  infixr 2 _⟨_⟩_
  _⟨_⟩_ : forall {a : Set} {b : a -> Set}
    (f : (x : a) -> M (b x)) -> {g h : (x : a) -> M (b x)} -> (f ⊑ g) -> (g ⊑ h) -> f ⊑ h
  _⟨_⟩_ f {g} {h} step1 step2 = ⊑-trans {f = f} {g = g} {h = h} step1 step2

  _■ : forall {a : Set} {b : a -> Set} (f : (x : a) -> M (b x)) -> f ⊑ f
  _■ f = ⊑-refl f

  Stack = List

  pop : ∀ {a} -> Stack a -> Partial (Pair a (Stack a))
  pop Nil = abort
  pop (Cons x xs) = return (x , xs)

  PopSpec : Stack Nat -> (Pair Nat (Stack Nat)) -> Set
  PopSpec xs (y , ys) = xs == Cons y ys

  popSpec : Stack Nat -> M (Pair Nat (Stack Nat))
  popSpec xs = spec (PopSpec xs)

  popCorrect : popSpec ⊑ (fromCode · pop)
  popCorrect = refinement \ { P Nil (fst , snd) → fst (λ x ())
                            ; P (Cons x xs) (fst , snd) → snd (x , xs) Refl}

  data AddSpec : Stack Nat -> Stack Nat -> Set where
    AddThem : ∀ {x1 x2 : Nat} {xs : Stack Nat} -> AddSpec (Cons x1 (Cons x2 xs)) (Cons (x1 + x2) xs)

  addSpec : Stack Nat -> M (Stack Nat)
  addSpec (xs) = spec (AddSpec xs)

  add : Stack Nat -> M (Stack Nat)
  add xs =
    pop xs >>= \{ (x1 , xs) -> 
    pop xs >>= \{ (x2 , xs) ->
    return (Done (Cons (x1 + x2) xs))}}

  addCorrect : addSpec ⊑ add
  addCorrect = refinement prf
    where
    prf : (P : Stack Nat -> Stack Nat -> Set) -> wpM addSpec P ⊆ wpM add P
    prf P Nil (fst , snd) = fst \xs -> λ ()
    prf P (Cons x Nil) (fst , snd) = fst λ x₁ () 
    prf P (Cons x (Cons x₁ xs)) H = Pair.snd H (Cons _ xs) AddThem

 -- Can we do calculation in this style?

  explicitDerivation : addSpec ⊑ add
  explicitDerivation =
    addSpec
      ⟨ step1 ⟩
    (\xs -> pop xs >>= \ { (x1 , xs) -> spec (AddSpec (Cons x1 xs))})
      ⟨ step2 ⟩
    (\xs -> pop xs >>= \ { (x1 , xs) ->
            pop xs >>= \ { (x2 , xs) ->
            spec (AddSpec (Cons x1 (Cons x2 xs)))
                         }})
      ⟨ step3 ⟩
    add ■
      where
        step1 : addSpec ⊑ (\xs -> pop xs >>= \ { (x1 , xs) -> Pure (Spec (AddSpec (Cons x1 xs)))})
        step1 = refinement \ { P Nil (fst , snd) → fst λ x () ; P (Cons x xs) H → H}
        step2 : (\xs -> pop xs >>= \ { (x1 , xs) -> spec (AddSpec (Cons x1 xs))})
                ⊑
                (\xs -> pop xs >>= \ { (x1 , xs) ->
                        pop xs >>= \ { (x2 , xs) ->
                        spec (AddSpec (Cons x1 (Cons x2 xs)))}})
        step2 = refinement \ { P Nil ()
                             ; P (Cons x Nil) (fst , snd) → fst \x ()
                             ; P (Cons x (Cons x₁ xs)) H → H}
        step3 : (\xs -> pop xs >>= \ { (x1 , xs) ->
                        pop xs >>= \ { (x2 , xs) ->
                        spec (AddSpec (Cons x1 (Cons x2 xs)))}})
                ⊑ add
        step3 = refinement \ { P Nil () ; P (Cons x Nil) ()
                             ; P (Cons x1 (Cons x2 xs)) (fst , snd) →
                                 snd (Cons (x1 + x2) xs) AddThem }

  -- Rephrasing things a bit...


  Σ : (a : Set) -> (b : a -> Set) -> Set
  Σ = Sigma

  popM : Stack Nat -> M (Pair Nat (Stack Nat))
  popM xs = pop xs >>= λ x → Pure (Done x)

  _>=>_ : ∀ {a b c} -> (I a -> M b) -> (I b -> M c) -> (I a -> M c)
  _>=>_ c1 c2 = \x ->  c1 x >>= c2

  popIt : (S : Stack Nat -> Stack Nat -> Set) ->
          Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
            (\g -> 
              (P : Stack Nat -> Stack Nat -> Set) ->
              wpM (spec · S) P ⊆ wpM (\xs -> pop xs >>= g) P) ->
          Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · S) ⊑ f)
  popIt S (g , H) = (\xs -> pop xs >>= g) , refinement H

  popPrePost : 
    (S : Stack Nat -> Stack Nat -> Set) ->
    (g : Pair Nat (Stack Nat) -> M (Stack Nat)) ->
    
    (P : Stack Nat -> Stack Nat -> Set)
    wpM (spec · S) P ⊆ wpM (\xs -> pop xs >>= g) P) ->    

  returnStep : ∀ {P : Stack Nat -> Stack Nat -> Set} ->
    ((xs : Stack Nat) -> P xs xs) ->
    Σ (Stack Nat -> M (Stack Nat)) (\f -> (\x -> spec (P x)) ⊑ f)    
  returnStep H = (\xs -> Pure (Done xs)) , refinement λ { P ys (fst , snd) → snd ys (H ys)}

  popStep : ∀ {P : Stack Nat -> Stack Nat -> Set} ->
    -- if there exists a continuation f
    Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
      (\f ->
      -- such that it the following spec is refined by pop >>= f
      (\xs -> spec \ys ->
          -- if there exists a result of pop
          Sigma (Pair Nat (Stack Nat))
          -- that behaves like pop and satisfies P
          \ { (z , zs) → Pair (Cons z zs == xs) (P (Cons z zs) ys) })
          ⊑ (\xs -> pop xs >>= f)) ->
    -- then we can refine P into code
    Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · P) ⊑ f)
  popStep {P} (f , refinement proof) =
    (λ xs → pop xs >>= f) ,
      refinement λ { Q Nil wp → {!!}
                   ; Q (Cons x ys) wp →
                        proof Q (Cons x ys)
                          ((λ contra → contra (Cons x ys) ((x , ys) , (Refl , {!!})))
                          , λ { zs ((q , qs) , (fst , snd)) → Pair.snd wp zs {!!}}) }


  derivation : Σ (Stack Nat -> M (Stack Nat)) (\f -> addSpec ⊑ f)
  derivation =  {!!}

  feasible : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> Set
  feasible {a} f = (x : a) -> wp f (\_ _ -> ⊥) x == ⊥

  infeasible : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> Set
  infeasible f = feasible f -> ⊥

