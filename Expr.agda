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
      {!!}
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


  strengthenSpec : {a : Set} {b : a -> Set} (S S' : (x : a) -> b x -> Set) ->
    ((x : a) -> S' x ⊆ S x) ->
    (λ x → Pure (Spec (S x))) ⊑ (\x -> Pure (Spec (S' x)))
  strengthenSpec S S' H = refinement λ {P x (h1 , h2) → {!!} , λ bx s'bx → h2 bx (H _ _ s'bx)}


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


  returnStep : ∀ {P : Stack Nat -> Stack Nat -> Set} ->
    ((xs : Stack Nat) -> P xs xs) ->
    Σ (Stack Nat -> M (Stack Nat)) (\f -> (\x -> spec (P x)) ⊑ f)    
  returnStep H = (\xs -> Pure (Done xs)) , refinement λ { P ys (fst , snd) → snd ys (H ys)}

  popStep : (S : Stack Nat -> Stack Nat -> Set) ->
          (S' : Pair Nat (Stack Nat) -> Stack Nat -> Set) ->
          ((x : Nat) (xs : Stack Nat) -> S (Cons x xs) ⊆ S' (x , xs)) ->
          ((x : Nat) (xs : Stack Nat) -> S' (x , xs) ⊆ S (Cons x xs)) ->          
          Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
            (\g -> (spec · S') ⊑ g) ->
          Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · S) ⊑ f)
  popStep S S' H1 H2 (g , proof) =
    (\xs -> pop xs >>= g) , {!!}


  derivation : Σ (Stack Nat -> M (Stack Nat)) (\f -> addSpec ⊑ f)
  derivation =  {!!}

  feasible : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> Set
  feasible {a} f = (x : a) -> wp f (\_ _ -> ⊥) x == ⊥

  infeasible : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> Set
  infeasible f = feasible f -> ⊥


module State (s : Set) where
  open Free hiding (_⊑_)

  data C : Set where
    Get : C
    Put : s -> C
    Spec : {output : Set} -> (s -> Set) -> (Pair output s -> Set) -> C

  R : C -> Set
  R Get = s
  R (Put _)  = ⊤
  R (Spec {b} _ _) = b -- we claim Spec produces a value of type b

  State : Set -> Set
  State = Free C R

  get : State s
  get = Step Get return
  put : s -> State ⊤
  put x = Step (Put x) (λ _ → return tt)
  spec : {a : Set} -> (s -> Set) -> (Pair a s -> Set) -> State a
  spec pre post = Step (Spec pre post) return

  -- TODO: replace spec with spec' everywhere?
  spec' : {a : Set} -> {b : Set} -> (Pair a s -> Set) -> (Pair b s -> Set) -> a -> State b
  spec' pre post x = spec (\t -> pre (x , t)) post

  isCode : {a : Set} -> State a -> Set
  isCode (Pure _) = ⊤
  isCode (Step Get k) = (state : s) -> isCode (k state)
  isCode (Step (Put _) k) = isCode (k tt)
  isCode (Step (Spec x₁ x₂) k) = ⊥

  isCodeBind : {a b : Set} -> (x : State a) -> (f : a -> State b) -> isCode x -> ((t : a) -> isCode (f t)) -> isCode (x >>= f)
  isCodeBind (Pure x) f xIs fIs = fIs x
  isCodeBind (Step Get k) f xIs fIs state = isCodeBind (k state) f (xIs state) fIs
  isCodeBind (Step (Put x) k) f xIs fIs = isCodeBind (k tt) f xIs fIs
  isCodeBind (Step (Spec pre post) k) f () fIs

  -- define a relation on initial states and stateful computations, where the postcondition holds in the final state
  -- TODO: seems legit but check that it works
  holds : {b : Set} -> (P : Pair b s -> Set) -> s -> (State b -> Set)
  holds P init (Pure x) = P (x , init)
  holds P init (Step Get k) = holds P init (k init)
  holds P init (Step (Put next) k) = holds P next (k tt)
  holds {f} P init (Step (Spec {i} pre post) k) = Pair (pre init) -- The specification holds if the initial value satisfies the precondition...
    ((val : i) -> (x : s) -> -- and for all intermediate values and states...
      post (val , x) -> -- such that the postcondition holds...
        holds P x (k val)) -- the continuation makes P hold

  wpState : {a : Set} -> {b : Set} -> (f : a -> State b) -> (P : Pair b s -> Set) -> (Pair a s -> Set)
  wpState {a} f P (arg , init) = wp f (\_ -> holds P init) arg

  -- give the current value and update it with the function
  modify : (s -> s) -> State s
  modify f = get >>= λ x → put (f x) >>= (λ _ → return x)

  -- the interaction of holds with bind
  holdsBind : {a : Set} -> {b : Set} -> (P : Pair b s -> Set) -> (t : s) -> (x : State a) -> (f : a -> State b) -- given f and x
    -> holds (wpState f P) t x -- if the wp of f holds after x,
    -> holds P t (x >>= f) -- then x >>= f satisfies P on input state x
  holdsBind P t (Pure x) f xHolds = xHolds
  holdsBind P t (Step Get k) f xHolds = holdsBind P t (k t) f xHolds
  holdsBind P t (Step (Put t') k) f xHolds = holdsBind P t' (k tt) f xHolds
  holdsBind P t (Step (Spec pre post) k) f (fst , snd) = fst , (λ x x₁ x₂ → holdsBind P x₁ (k x) f (snd x x₁ x₂))

  -- If we have a Spec, then for any P, its precondition is implied by the wp.
  holdsSpecPre : {a : Set} -> {b : Set} -> (pre : Pair a s -> Set) -> (post P : Pair b s -> Set)
    -> wpState (spec' pre post) P ⊆ pre
  holdsSpecPre _ _ _ _ (preHolds , _) = preHolds
  -- If we have Spec pre post, then for any postcondition P that is implied by post, the wp is equivalent to pre.
  holdsSpecPost : {a : Set} -> {b : Set} -> (pre : Pair a s -> Set) -> (post P : Pair b s -> Set)
    -> post ⊆ P
    -> pre ⊆ wpState (spec' pre post) P
  holdsSpecPost pre post P postImplies x preHolds = preHolds , (λ val x₁ → postImplies (val , x₁))

module TreeLabeling where
  open Free hiding (_⊑_)
  open State

  -- we have to put this here so we don't have s as an obligatory variable
  record _⊑_ {s : Set} {a : Set} {b : Set} (f g : a -> State s b) : Set1 where
    constructor refinement
    field
      proof : (∀ P -> wpState s f P ⊆ wpState s g P)

  record Preorder {a : Set} (R : a -> a -> Set) : Set where
    constructor preorder
    field
      pre-refl : (∀ {x} -> R x x)
      pre-trans : (∀ {x y z} -> R x y -> R y z -> R x z)
  open Preorder

  pre-⊑ : ∀ {a b c} -> Preorder (_⊑_ {a} {b} {c})
  pre-⊑ = preorder
    (refinement (λ P x₁ z → z))
    (λ p q → refinement (λ P x₁ z₁ → _⊑_.proof q P x₁ (_⊑_.proof p P x₁ z₁)))

  infixr 2 _⟨_⟩_
  _⟨_⟩_ : forall {a s : Set} {b : Set}
    (f : (x : a) -> State s b) -> {g h : (x : a) -> State s b} -> (f ⊑ g) -> (g ⊑ h) -> f ⊑ h
  _⟨_⟩_ f {g} {h} step1 step2 = (pre-trans pre-⊑) {f} {g} {h} step1 step2

  _∎ : forall {a s : Set} {b : Set} (f : (x : a) -> State s b) -> f ⊑ f
  _∎ f = pre-refl pre-⊑ {f}

  -- For proofs it is more useful to run dependent programs, but for case-analysis we want direct monadic values.
  run' : {s : Set} -> {b : Set} -> (prog : State s b) -> isCode s prog -> s -> Pair b s
  run' (Pure x) prf init = x , init
  run' (Step Get k) prf init = run' (k init) (prf init) init
  run' (Step (Put next) k) prf init = run' (k tt) prf next
  run' (Step (Spec pre post) k) () init

  run : {a s : Set} -> {b : Set} -> (prog : a -> State s b) -> ((t : a) -> isCode s (prog t)) -> Pair a s -> Pair b s
  run prog prf (x , init) = run' (prog x) (prf x) init

  -- completeness and soundness of wpState for code
  -- wpState is sound: it gives a precondition
  soundness : {a s : Set} -> {b : Set} -> (prog : a -> State s b) -> (prf : (x : a) -> isCode s (prog x)) -- if we have code,
    -> (P : Pair b s -> Set) -- and a postcondition,
    -> (i : Pair a s) -> wpState s prog P i -> P (run prog prf i) -- then wpState gives a precondition for P
  soundness {a} {s} {b} prog prf P (x , t) wpHolds = soundness' (prog x) (prf x) P t wpHolds
    where
      soundness' : (prog : State s b) -> (prf : isCode s prog) -> (P : Pair b s -> Set) -> (t : s) -> holds s P t prog -> P (run' prog prf t)
      soundness' (Pure _) _ _ _ hold = hold
      soundness' (Step Get k) prf P t hold = soundness' (k t) (prf t) P t hold
      soundness' (Step (Put x) k) prf P t hold = soundness' (k tt) prf P x hold
      soundness' (Step (Spec _ _) _) () _ _ _

  -- wpState is complete: it gives a condition that is weaker than all preconditions
  completeness' : {s : Set} -> {b : Set} -> (prog : State s b) -> (prf : isCode s prog)
    -> (pre : s -> Set) -> (post : Pair b s -> Set)
    -> (t : s) -> pre t -> post (run' prog prf t)
    -> holds s post t prog
  completeness' (Pure _) _ _ _ _ _ postHold = postHold
  completeness' (Step Get k) prf pre post t preHold postHold = completeness' (k t) (prf t) (λ _ → post (run' (k t) (prf t) t))
      post t postHold postHold
  completeness' (Step (Put x) k) prf pre post t preHold postHold = completeness' (k tt) prf (λ _ → post (run' (k tt) prf x)) post x
    postHold postHold
  completeness' (Step (Spec _ _) _) () _ _ _ _ _

  completeness : {a s : Set} -> {b : Set} -> (prog : a -> State s b) -> (prf : (x : a) -> isCode s (prog x)) -- if we have code,
    -> (pre : Pair a s -> Set) -> (post : Pair b s -> Set) -- and a specification
    -> ((i : Pair a s) -> pre i -> post (run prog prf i)) -- and for all preconditioned values, the postcondition holds for running
    -> pre ⊆ wpState s prog post -- then it is stronger than the weakest precondition
  completeness {a} {s} {b} prog prf pre post specRun (x , t) preHolds
    = completeness' (prog x) (prf x) (\t -> pre (x , t)) post t preHolds (specRun (x , t) preHolds)
 
  -- maar met run heb je non-isCode weggelaten, dus hier kunnen we relateren met spec
  refinePrePost : {a s : Set} -> {b : Set} -> (prog : a -> State s b) -> (prf : (x : a) -> isCode s (prog x)) -- if we have code
    -> (pre : Pair a s -> Set) -> (post : Pair b s -> Set) -- and a specification
    -> ((i : Pair a s) -> pre i -> post (run prog prf i)) -- and for all preconditioned values, the postcondition holds
    -> spec' s pre post ⊑ prog -- then the code refines the specification
  refinePrePost {a} {s} {b} prog prf pre post postAfterRun = refinement prePost
    where
      rPP' : (prog : State s b) -> (prf : isCode s prog) -- if we have code
        -> (pre : s -> Set) -> (post : Pair b s -> Set) -- and a specification
        -> ((t : s) -> pre t -> post (run' prog prf t)) -- and for all preconditioned values, the postcondition holds
        -> (P : Pair b s -> Set) -> (t : s) -> holds s P t (spec s pre post) -> holds s P t prog
      rPP' prog prf pre post postAfterRun P t (fst , snd)
        = completeness' prog prf pre P t fst (snd (Pair.fst (run' prog prf t)) (Pair.snd (run' prog prf t)) (postAfterRun t fst))
      -- rPP' prog prf pre post postAfterRun P t (fst , snd) = {!!}
      prePost : (P : Pair b s -> Set) -> (x : Pair a s) -> wpState s (spec' s pre post) P x -> wpState s prog P x
      prePost P (x , t) wpSpec = rPP' (prog x) (prf x) (\t' -> pre (x , t')) post (λ t₁ → {! postAfterRun (x , t₁) !}) P t wpSpec
      -- prog prf pre post postAfterRun P x hold = completeness prog prf pre P (λ i preH → {!postAfterRun i preH!}) x (holdsSpecPre s pre post P x hold)

  data Tree (s : Set) : Set where
    Leaf : s -> Tree s
    Branch : Tree s -> Tree s -> Tree s

  -- the number of leaves in the tree
  size : {s : Set} -> Tree s -> Nat
  size (Leaf _) = 1
  size (Branch l r) = size l + size r

  flatten : {s : Set} -> Tree s -> List s
  flatten (Leaf x) = Cons x Nil
  flatten (Branch l r) = (flatten l) ++ (flatten r)

  -- TODO: is this a useful definition?
  range : Nat -> List Nat
  range 0 = Nil
  range (Succ n) = range n ++ (Cons n Nil)

  splitRange : (p q : Nat) -> (range p ++ map (_+_ p) (range q)) == range (p + q)
  splitRange = {!!}

  -- basic tree labelling function, but we don't prove it works!
  labelTree : {a : Set} -> Tree a -> State Nat (Tree Nat)
  labelTree (Leaf x) = (modify Nat Succ) >>= λ n → return (Leaf n)
  labelTree (Branch l r) = labelTree l >>= \l' -> labelTree r >>= \r' -> return (Branch l' r')

  labelPre : Nat -> Set
  labelPre n = n == 0
  labelPost : Pair (Tree Nat) Nat -> Set
  labelPost (t , n) = Pair (flatten t == range (size t)) (n == size t)
  labelSpec : {a : Set} -> Tree a -> State Nat (Tree Nat)
  labelSpec x = spec Nat labelPre labelPost

  -- If we can prove there is a refinement, and the refinement is code, then we have an implementation.
  implementation : {a s : Set} -> {b : Set} -> ((t : a) -> State s b) -> Set
  implementation {a} {s} {b} spec = Sigma ((t : a) -> State s b) (\prog -> Pair ((t : a) -> isCode s (prog t)) (spec ⊑ prog))

  -- We already have the function, so let's prove it works.
  labelRefinement : {a : Set} -> implementation (labelSpec {a})
  labelRefinement {a} = labelTree , (itIsCode , refinePrePost labelTree itIsCode (λ x → Pair.snd x == 0) labelPost provePost)

    where
      itIsCode : {a : Set} -> (t : Tree a) -> isCode Nat (labelTree t)
      itIsCode (Leaf x) = λ state → tt
      -- TODO: can we make this better?
      -- Maybe a combinator that gives Either (isCode prog) (continueHere continuation),
      -- such that isCode p implies isCode (continuation p)
      itIsCode (Branch l r) = isCodeBind Nat (labelTree l) (\l' -> labelTree r >>= \r' -> return (Branch l' r')) (itIsCode l)
        λ t → isCodeBind Nat (labelTree r) (λ z → Pure (Branch t z)) (itIsCode r) (λ t₁ → tt)

      inBranches : (l r : Tree a) -> (n : Nat) -> Branch (Pair.fst (run labelTree itIsCode (l , n))) (Pair.fst (run labelTree itIsCode (r , (n + size l)))) == Pair.fst (run labelTree itIsCode (Branch l r , n))
      inBranches l r n = {!!}

      preserveSize : (i : Pair (Tree a) Nat) -> size (Pair.fst i) == size (Pair.fst (run labelTree itIsCode i))
      preserveSize (Leaf x , _) = Refl
      preserveSize (Branch l r , _) = {!!}

      proveRange : (i : Pair (Tree a) Nat) -> flatten (Pair.fst (run labelTree itIsCode i)) == map (_+_ (Pair.snd i)) (range (size (Pair.fst i)))
      proveRange (Leaf x , n) = cong (λ k → Cons k Nil) (plus-zero n)
      proveRange (Branch l r , n) =
        let lt = run labelTree itIsCode (Branch l r , n)
            ll = run labelTree itIsCode (l , n)
            lr = run labelTree itIsCode (r , (n + size l))
        in flatten (Pair.fst lt)
          =⟨ sym (cong flatten (inBranches l r n)) ⟩= flatten (Branch (Pair.fst ll) (Pair.fst lr))
          =⟨ Refl ⟩= (flatten (Pair.fst ll) ++ flatten (Pair.fst lr))
          =⟨ cong (flip _++_ (flatten (Pair.fst lr))) (proveRange (l , n)) ⟩= (map (_+_ n) (range (size l)) ++ flatten (Pair.fst lr))
          =⟨ cong (_++_ (map (_+_ n) (range (size l)))) {!!} ⟩= {!!}
          =⟨ cong (_++_ (map (_+_ n) (range (size l)))) {!!} ⟩= {!!}
          =⟨ cong (_++_ (map (_+_ n) (range (size l)))) (cong {!!} {!!}) ⟩= (map (_+_ n) (range (size l)) ++
                                                                   map (λ z → n + (size l + z)) (range (size r)))
          =⟨ cong (_++_ (map (_+_ n) (range (size l)))) (sym (map-functorial (_+_ (size l)) (_+_ n))) ⟩= (map (_+_ n) (range (size l)) ++ map (_+_ n) (map (_+_ (size l)) (range (size r))))
          =⟨ map-concat {l = range (size l)} {l' = map (_+_ (size l)) (range (size r))} (_+_ n) ⟩= map (_+_ n) (range (size l) ++ map (_+_ (size l)) (range (size r)))
          =⟨ cong (map (_+_ n)) (splitRange (size l) (size r)) ⟩= map (_+_ n) (range (size l + size r))
          =∎
          {- =⟨ sym (cong flatten (inBranches l r n)) ⟩= flatten (Branch (Pair.fst ll) (Pair.fst lr))
          =⟨ Refl ⟩= (flatten (Pair.fst ll) ++ flatten (Pair.fst lr))
          =⟨ cong (map (_+_ n)) (splitRange (size l) (size r)) ⟩= map (_+_ n) (range (size l + size r))
          -}

      provePost : (i : Pair (Tree a) Nat) -> Pair.snd i == 0 -> labelPost (run labelTree itIsCode i)
      provePost (Leaf x , .0) Refl = Refl , Refl
      provePost (Branch l r , .0) Refl =
        {!!} ,
        (run labelTree itIsCode (Branch l r , 0) .Pair.snd =⟨ {!!} ⟩= size (run labelTree itIsCode (Branch l r , 0) .Pair.fst) =∎)
        --trans (trans (sym (cong flatten (inBranches l r 0))) {!!})
        --(trans (splitRange (size l) (size r)) (cong range (preserveSize (Branch l r , 0)))) , {!!}

      -- We try to prove inductively that the refinement holds.
      -- This doesn't work because the termination checker doesn't believe us...
      {-
      itRefines : (x : Pair (Tree a) Nat) -> (P : Pair (Tree Nat) Nat → Set) → wpState Nat labelSpec P x -> wpState Nat labelTree P x
      itRefines (t@(Leaf _) , .0) P (Refl , post)
        = let (labelled , label) = run labelTree itIsCode (t , 0)
          in post labelled label (Refl , Refl)
      itRefines (t@(Branch l r) , .0) P (Refl , post)
        = let iRr n l' = itRefines (r , n) {!wpState Nat ? ?!} {!!}
          in holdsBind Nat P 0 (labelTree l) (\l' -> labelTree r >>= \r' -> return (Branch l' r'))
            (itRefines (l , 0) (wpState Nat (λ l' → labelTree r >>= (λ r' → return (Branch l' r'))) P)
              (Refl , \l' n x → holdsBind Nat P n (labelTree r) (λ r' → return (Branch l' r')) (iRr n l')))
       -}


