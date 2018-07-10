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

  isSucc : Nat -> Set
  isSucc Zero = ⊥
  isSucc (Succ n) = ⊤

  postulate
    totalDiv : Nat -> (m : Nat) -> {p : isSucc m} -> Nat  

  div : Nat -> Nat -> Maybe Nat
  div n Zero = nothing
  div n (Succ k) = just (totalDiv n (Succ k))


  ⟦_⟧ : Expr -> Maybe Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    div v1 v2

  data _⇓_ : Expr -> Nat -> Set where
    Base : ∀ {x} -> Val x ⇓ x
    Step : ∀ {x y l r} -> l ⇓ x -> r ⇓ (Succ y) ->
           Div l r ⇓ totalDiv x (Succ y)

  SafeDiv : Expr -> Set
  SafeDiv (Val x) = (Val x) ⇓ Zero -> ⊥
  SafeDiv (Div e e₁) = Triple (e₁ ⇓ Zero -> ⊥) (SafeDiv e) (SafeDiv e₁)

  wp : {a b : Set} ->
    (a -> Maybe b) -> (b -> Set) -> (a -> Set)
  wp f P x = lift P (f x)

  correct : (e : Expr) -> SafeDiv e -> wp ⟦_⟧ (e ⇓_) e
  correct (Val x) nz = Base
  correct (Div l r) (nz1 , nz2 , nz3) with ⟦ l ⟧ | ⟦ r ⟧ | correct l nz2 | correct r nz3
  correct (Div l r) (nz1 , nz2 , nz3) | Pure x | Pure Zero | p | q = magic (nz1 q)
  correct (Div l r) (nz1 , nz2 , nz3) | Pure x | Pure (Succ y) | p | q = Step p q
  correct (Div l r) (nz1 , nz2 , nz3) | Pure x | Step Nothing x₁ | p | ()
  correct (Div l r) (nz1 , nz2 , nz3) | Step Nothing x | y | p | q = p

  correctWP : (e : Expr) -> SafeDiv e -> wp ⟦_⟧ (e ⇓_) e
  correctWP e nz = correct e nz

  _⊆_ : {l : Level} {a : Set l} ->
    (R1 R2 : a -> Set l) -> Set l
  _⊆_ {a = a} R1 R2 =
    (x : a) -> R1 x -> R2 x 

  -- Assign predicate transformer semantics to a relation
  wpR : ∀ {a b : Set} -> (R : a -> b -> Set) -> (b -> Set) -> (a -> Set)
  wpR {a} {b} R P x = R x ⊆ P 

  _⊑_ : {a b : Set} ->
    (PT1 PT2 : (b -> Set) -> (a -> Set)) -> Set₁
  _⊑_ {a} {b} PT1 PT2 = (P : b -> Set) -> PT1 P ⊆ PT2 P


  -- correct2 : wpR (_⇓_)  ⊑ wp ⟦_⟧ 
  -- correct2 P (Val x) H = H x Base
  -- correct2 P (Div l r) H with
  --     inspect ⟦ l ⟧ | correct2 P l {!!}
  --   | inspect ⟦ r ⟧ | correct2 P r {!!}
  -- correct2 P (Div l r) H | Pure vl with-≡ eql | cl | Pure vr with-≡ eqr | cr rewrite eql | eqr
  --   with inspect (div vl vr)
  -- ... | Pure v with-≡ eq rewrite eq = H v {!!}
  -- ... | Step Nothing _ with-≡ eq rewrite eq = {!v!}  
  -- correct2 P (Div l r) H | Pure x with-≡ eql | cl | Step Nothing _ with-≡ eqr | cr rewrite eqr
  --   = magic cr
  -- correct2 P (Div l r) H | Step Nothing x with-≡ eql | cl | vr with-≡ eqr | cr rewrite eql
  --   = magic cl

  correct2' : wpR (_⇓_)  ⊑ wp ⟦_⟧ 
  correct2' P (Val x) H = H x Base
  correct2' P (Div l r) H with ⟦ l ⟧ | ⟦ r ⟧
  ... | sl | sr = {!how can we rule out that the division fails?!}

  lemma : ∀ {P : Nat -> Set} {x y v1 v2} ->
    x == v1 -> Succ y == v2 -> lift P (div v1 v2) -> P (totalDiv x (Succ y))
  lemma {P} {x} {y} {.x} {.(Succ y)} Refl Refl H = H

  wpLemma : (e : Expr) (v : Nat) -> ⟦ e ⟧ == just v -> wp ⟦_⟧ (\n -> n == v) e
  wpLemma e v H with ⟦ e ⟧
  wpLemma e .x Refl | Pure x = Refl
  wpLemma e v () | Step Nothing x

  correct3 : wp ⟦_⟧ ⊑  wpR (_⇓_)
  correct3 P (Val x) H .x Base = H
  correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr) with inspect ⟦ l ⟧ | inspect ⟦ r ⟧
  correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step {x} {y} evl evr)
    | Pure vl with-≡ eql | Pure vr with-≡ eqr rewrite eql | eqr =
    let ihl = correct3 (\n -> n == vl) l (wpLemma l vl eql) x evl
        ihr = correct3 (\n -> n == vr) r (wpLemma r vr eqr) _ evr
    in lemma ihl ihr H
  correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr)
    | Pure x with-≡ eql | Step Nothing x₁ with-≡ eqr rewrite eql | eqr = magic H
  correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr)
    | Step Nothing x with-≡ eql | Pure x₁ with-≡ eqr rewrite eql = magic H
  correct3 P (Div l r) H .(totalDiv _ (Succ _)) (Step evl evr)
    | Step Nothing x with-≡ eql | Step Nothing x₁ with-≡ eqr rewrite eql = magic H
    



  liftEq : (e : Expr) -> (v : Nat) -> ⟦ e ⟧ == Pure v ->  lift (\n -> n == v) ⟦ e ⟧
  liftEq e v eq rewrite eq = Refl

  data Spec (a b : Set) : Set₁ where
    [_,_] : (pre : a -> Set) -> (post : (x : a) -> pre x -> b -> Set) -> Spec a b

  refines : ∀ {a b} -> Spec a b -> Spec a b -> Set
  refines {a} {b} [ pre1 , post1 ] [ pre2 , post2 ] =
    Sigma ((x : a) -> pre1 x -> pre2 x)
          (λ c → (x : a) (H : pre1 x) (y : b) -> post2 x (c x H) y -> post1 x H y)

  wpsemantics : ∀ {a b} -> Spec a b -> (b -> Set) -> (a -> Set)
  wpsemantics {a} {b} [ pre , post ] P = \x ->
    Sigma (pre x) \H -> (y : b) -> post x H y -> P y
  
  refinementCorrect : ∀ {a b} -> (s1 s2 : Spec a b) ->
    refines s1 s2 -> (P : b -> Set) (x : a) -> wpsemantics s1 P x ->  wpsemantics s2 P x
  refinementCorrect [ pre1 , post1 ] [ pre2 , post2 ] (preC , postC ) P x (pre , post) =
     (preC x pre) , λ y H → post y (postC x pre y H)


  ruleOfConsequence : {a b : Set} (c : Maybe a) (f : a -> Maybe b) ->
    (P : b -> Set) -> (lift (\x -> wp f P x) c) -> lift P (c >>= f)
  ruleOfConsequence (Pure x) f H P with f x
  ruleOfConsequence (Pure x) f H P | Pure x₁ = P
  ruleOfConsequence (Pure x) f H () | Step Nothing x₁
  ruleOfConsequence (Step Nothing x) f H ()    

  step : {a b : Set} {c : Maybe a} {f : a -> Maybe b} ->
    {P : b -> Set} -> (lift (\x -> wp f P x) c) -> lift P (c >>= f)
  step {a} {b} {c} {f} {P} = ruleOfConsequence c f P

--  wp : {a b : Set} ->
--    (a -> Maybe b) -> (b -> Set) -> (a -> Set)
--  wp f P x = lift P (f x)


  correct4 : (e : Expr) -> SafeDiv e -> lift (e ⇓_) ⟦ e ⟧
  correct4 (Val x) sd = Base
  correct4 (Div l r) (fst , snd , thd) =
    step {c = ⟦ l ⟧}
    {!step {c = ⟦ r ⟧} ?!}

                    -- step {! ⟦ l ⟧ !} (\ v1 ->
                    -- ⟦ r ⟧ >>= \ v2 ->
                    -- div v1 v2 ) (\v -> Div l r ⇓ v) H


