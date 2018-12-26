{-# OPTIONS --type-in-type #-}
module StateModify where

open import Prelude
open import SliceSpec

data C (s : Set) : Set where
  Modify : (s -> s) -> C s
R : (s : Set) → C s -> Set
R s (Modify f) = s

StateM : Set → Set → Set
StateM s = Slice s (C s) (R s)

modify : {s : Set} -> (s -> s) -> StateM s s
modify f = Step (Modify f) Pure

getM : {s : Set} -> StateM s s
getM = modify (\t -> t)
putM : {s : Set} -> s -> StateM s ⊤
putM t' = Step (Modify (\_ -> t')) (\_ -> Pure tt)
specM : {a s : Set} -> {b : Set} -> (Pair a s -> Set) -> (Pair a s -> Pair b s -> Set) -> a -> StateM s b
specM pre post x
  = spec (\t -> pre (x , t) ) (\t y t' -> post (x , t) (y , t'))

holdsM : {a s : Set} -> StateM s a -> (a → s -> Set) -> s -> Set
holdsM (Pure x) P t = P x t
holdsM (Step (Modify f) k) P t = holdsM (k t) P (f t)
holdsM {s = s} (Spec {c} pre post k) P t = Pair (pre t)
  ((z : c) -> (t' : s) -> post t z t' -> holdsM (k z) P t')

runStateM : {s a : Set} -> (prog : StateM s a) -> isCodeSlice prog
  -> s -> Pair a s
runStateM (Pure x) prf t = x , t
runStateM (Step (Modify f) k) prf t = runStateM (k t) (prf t) (f t)
runStateM (Spec _ _ _) ()

module Modify<->GetPut where
  open import State

  Modify->GetPut : {a s : Set} -> StateM s a -> State s a
  Modify->GetPut (Pure x) = Pure x
  Modify->GetPut (Step (Modify f) k) = State.modify f >>= λ x → Modify->GetPut (k x)
  Modify->GetPut (Spec {b} pre post k) = Spec pre post \y -> Modify->GetPut (k y)

  equivalentM->GP : {a s : Set} -> (prog : StateM s a) -> (P : a → s -> Set) ->
    (t : s) -> (holdsM prog P t) ⇔ (ptState P (Modify->GetPut prog) t)
  equivalentM->GP (Pure x) P t = iff (λ z → z) (λ z → z)
  equivalentM->GP (Step (Modify f) k) P t = iff
    (_⇔_.if (equivalentM->GP (k t) P (f t)))
    (_⇔_.onlyIf (equivalentM->GP (k t) P (f t)))
  equivalentM->GP (Spec pre post k) P t = iff
    (λ z → Pair.fst z , λ x t' pH → _⇔_.if (equivalentM->GP (k x) P t') ((² z) t' x pH))
    (λ z → Pair.fst z , λ t' x pH → _⇔_.onlyIf (equivalentM->GP (k x) P t') ((² z) x t' pH))

  GetPut->Modify : {a s : Set} -> State s a -> StateM s a
  GetPut->Modify (Pure x) = Pure x
  GetPut->Modify (Step Get k) = Step (Modify (λ z → z)) \z -> GetPut->Modify (k z)
  GetPut->Modify (Step (Put x) k) = Step (Modify (λ z → x)) \_ -> GetPut->Modify (k tt)
  GetPut->Modify (Spec pre post k) = Spec pre post \z -> GetPut->Modify (k z)

  equivalentGP->M : {a s : Set} -> (prog : State s a) -> (P : a → s -> Set) ->
    (t : s) -> (ptState P prog t) ⇔ (holdsM (GetPut->Modify prog) P t)
  equivalentGP->M (Pure x) P t = iff (λ z → z) (λ z → z)
  equivalentGP->M (Step Get k) P t = iff (_⇔_.if (equivalentGP->M (k t) P t)) (_⇔_.onlyIf (equivalentGP->M (k t) P t))
  equivalentGP->M (Step (Put x) k) P t = iff (_⇔_.if (equivalentGP->M (k tt) P x)) (_⇔_.onlyIf (equivalentGP->M (k tt) P x))
  equivalentGP->M (Spec pre post k) P t = iff
    (λ z → Pair.fst z , λ t' x pH → _⇔_.if (equivalentGP->M (k x) P t') ((² z) x t' pH))
    (λ z → Pair.fst z , λ x t' pH → _⇔_.onlyIf (equivalentGP->M (k x) P t') ((² z) t' x pH))
