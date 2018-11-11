{-# OPTIONS --type-in-type #-}

module PropSpec where

-- Spec, but now we allow for a type of propositions that is not Set.

open import Prelude hiding (_⟨_⟩_)
open import Preorder

open IsMonad
open Preorder.Preorder

-- PropSpec Set should be isomorphic to Mix
-- The meaning of PropSpec prop C R b is:
--  prop : type of propositions
--  C : choices to take in computation
--  R : return type of a choice
--  b : return type of the computation
data PropSpec (prop : Set₁) (C : Set) (R : C -> Set) (b : Set) : Set where
  Pure : b -> PropSpec prop C R b
  Step : (c : C) (k : R c -> PropSpec prop C R b) -> PropSpec prop C R b
  Spec : {b' : Set} ->
    (pre : prop) (post : b' -> prop) ->
    (k : b' -> PropSpec prop C R b) -> PropSpec prop C R b

infixl 20 _>>=_
_>>=_ : {prop : Set₁} {C : Set} {R : C -> Set} ->
  {b : Set} {c : Set} ->
  PropSpec prop C R b -> (b -> PropSpec prop C R c) -> PropSpec prop C R c
Pure x >>= f = f x
Step c k >>= f = Step c λ z → k z >>= f
Spec pre post k >>= f = Spec pre post λ z → k z >>= f

return : {prop : Set₁} {b : Set} {C : Set} {R : C -> Set} ->
  b -> PropSpec prop C R b
return y = Pure y
spec : {prop : Set₁} {b : Set} {C : Set} {R : C -> Set} ->
  (P : prop) (Q : b -> prop) ->
  PropSpec prop C R b
spec P Q = Spec P Q return

PTs : (prop : Set₁) -> (C : Set) (R : C -> Set) -> Set
PTs prop C R = (c : C) -> (P : R c -> prop) -> prop

record Propositional (a : Set) : Set where
  constructor propositional
  infixr 20 _=>_
  field
    forAll : (C : Set) → (C → a) → a
    _=>_ : a → a → a
    _∧_ : a → a → a
    prove : a → Set

    prove-forAll : (C : Set) → (x : C → a) →
      ((c : C) → prove (x c)) ⇔ prove (forAll C x)
    implies-reflexive : (x : a) →
      prove (x => x)
    implies-transitive : (x y z : a) →
      prove (x => y) → prove (y => z) → prove (x => z)

    -- TODO: can we split this up into simpler parts?
    lemma : ∀ {b} {pre pre' : a} {post post' : b → a}
          {wp : (b → a) → a} →
        prove (pre => pre') →
        prove (forAll b (λ x → pre => (post' x => post x))) →
        ((P : b → a) → prove (((pre' ∧ forAll b (λ z → post' z => P z)) => wp P))) →
        prove (forAll (b → a) (λ P → (((pre ∧ forAll b (λ z → post z => P z)) => wp P))))
    lemma' : ∀ {b} {pre : a}
      {post P : b → a} {y : b} →
      prove (pre => post y) →
      prove ((pre ∧ (forAll b (λ z → post z => P z))) => P y)
open Propositional {{...}} public

wpProp : {prop : Set₁} {{Prop : Propositional prop}} {b : Set} ->
  {C : Set} {R : C -> Set} ->
  ((c : C) → (P : R c → prop) → prop) →
  (Q : b -> prop) ->
  PropSpec prop C R b -> prop
wpProp PT Q (Pure y) = Q y
wpProp PT Q (Step c k) = PT c (λ y → wpProp PT Q (k y))
wpProp PT Q (Spec {c} pre post k) = pre ∧ (forAll c λ z → post z => wpProp PT Q (k z))

isCodePropSpec : {prop : Set₁} {C : Set} {R : C -> Set} ->
  {b : Set} -> PropSpec prop C R b -> Set
isCodePropSpec (Pure y) = ⊤
isCodePropSpec {R = R} (Step c k) = (r : R c) -> isCodePropSpec (k r)
isCodePropSpec (Spec pre post k) = ⊥

isCodeBind : {prop : Set₁} {C : Set} {R : C -> Set} ->
  {b c : Set} -> (mx : PropSpec prop C R b) -> (f : b -> PropSpec prop C R c) ->
  isCodePropSpec mx -> ((y : b) -> isCodePropSpec (f y)) ->
  isCodePropSpec (mx >>= f)
isCodeBind (Pure x₂) f x x₁ = x₁ x₂
isCodeBind (Step c k) f x x₁ = λ r → isCodeBind (k r) f (x r) x₁
isCodeBind (Spec pre post k) f x x₁ = x

runPropSpec : {prop : Set₁} {C : Set} {R : C -> Set} ->
  {tyO : Set -> Set} -> IsMonad tyO -> (handler : (c : C) -> tyO (R c))
  {b : Set} -> (prog : PropSpec prop C R b) -> isCodePropSpec prog ->
  tyO b
runPropSpec m h (Pure y) tt = pure m y
runPropSpec m h (Step c k) prf = bind m (h c) λ z → runPropSpec m h (k z) (prf z)
runPropSpec m h (Spec pre post k) ()

record Refine {prop : Set₁} {{Prop : Propositional prop}} {C : Set} {R : C -> Set} (PT : PTs prop C R)
  {b : Set} (f g : PropSpec prop C R b) : Set₁ where
  constructor refinement
  field
    proof : prove (forAll (b -> prop) λ P → wpProp PT P f => wpProp PT P g)

pre-Refine : {prop : Set₁} {{Prop : Propositional prop}} {b : Set} {C : Set} {R : C -> Set} {PT : PTs prop C R} -> Preorder (Refine PT {b = b})
pre-Refine {prop} {{Prop}} {b} {C} {R} {PT} =
  Preorder.preorder (λ {x} → refinement (reflexive x)) λ {x} {y} {z} x=>y y=>z → refinement (transitive x y z x=>y y=>z)
  where
  reflexive : ∀ (x : PropSpec prop C R b) →
    prove (forAll (b → prop) (λ P → wpProp PT P x => wpProp PT P x))
  reflexive x = _⇔_.onlyIf (prove-forAll (b → prop) (λ P → wpProp PT P x => wpProp PT P x)) λ c → implies-reflexive (wpProp PT c x)
  transitive : (x y z : PropSpec prop C R b) →
    Refine PT x y → Refine PT y z →
    Propositional.prove Prop
    (Propositional.forAll Prop (b → prop)
    (λ P → wpProp PT P x => wpProp PT P z))
  transitive x y z (refinement x=>y) (refinement y=>z) = _⇔_.onlyIf
    (prove-forAll (b → prop) (λ P → wpProp PT P x => wpProp PT P z)) λ c → implies-transitive (wpProp PT c x) (wpProp PT c y) (wpProp PT c z) (_⇔_.if (prove-forAll (b → prop) (λ P → wpProp PT P x => wpProp PT P y)) x=>y c) (_⇔_.if (prove-forAll (b → prop) (λ P → wpProp PT P y => wpProp PT P z)) y=>z c)
record Impl {prop : Set₁} {{Prop : Propositional prop}} {C : Set} {R : C -> Set} (PT : PTs prop C R)
  {bx : Set} (spec : PropSpec prop C R bx) : Set₁ where
  constructor impl
  field
    prog : PropSpec prop C R bx
    code : isCodePropSpec prog
    refines : Refine {{Prop}} PT spec prog

doSharpen : {prop : Set₁} {{Prop : Propositional prop}} →
  {C : Set} {R : C -> Set} {PT : PTs prop C R} ->
  {b : Set} -> {pre pre' : prop} {post post' : b → prop} ->
  prove (pre => pre') ->
  prove (forAll b λ x → pre => post' x => post x) ->
  Impl PT (spec pre' post') -> Impl PT (spec pre post)
doSharpen {prop} {C} {R} {PT} {b} {pre} {pre'} {post} {post'} preI postI (impl prog code (refinement proof)) = impl
  prog
  code
  (refinement (lemma preI postI proof'))
  where
  proof' : (P : b → prop) → prove ((pre' ∧ (forAll b (λ z → (post' z) => (P z)))) => wpProp PT P prog)
  proof' = _⇔_.if (prove-forAll (b → prop) (λ P → (pre' ∧ (forAll b (λ z → (post' z) => (P z)))) => wpProp PT P prog)) proof

doReturn : {prop : Set₁} {{Prop : Propositional prop}} →
  {C : Set} {R : C -> Set} {PT : PTs prop C R} ->
  {b : Set} -> {pre : prop} {post : b → prop} ->
  (y : b) -> prove (pre => post y) ->
  Impl PT (spec pre post)
doReturn {prop} {b = b} {pre} {post} y prf = impl (Pure y) tt (refinement (_⇔_.onlyIf (prove-forAll (b → prop) (λ P → (pre ∧ forAll b λ z → post z => P z) => P y)) λ c → {!lemma' prf!}))
