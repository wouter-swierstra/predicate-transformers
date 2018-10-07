{-# OPTIONS --type-in-type #-}

module Nondet where

open import Prelude hiding (_⟨_⟩_)
open import Preorder
open import Maybe
open import Spec
open import Vector

-- The type of nondeterministic computation:
-- at each step, we might give up, or choose between two alternatives.
data C : Set where
  Fail : C
  Split : C
R : C -> Set
R (Fail) = ⊥
R (Split) = Bool
L : Set -> Set
L = Mix C R

-- The constructors from `Just do it!'
fail : {a : Set} -> L a
fail = Step Fail magic
_[]_ : {a : Set} -> L a -> L a -> L a
p [] q = Step Split \c -> if c then p else q

-- Classical equivalents of Either.
-- A very weak form of Either.
WeakEither : Set -> Set -> Set
WeakEither L R = ¬ (Pair (¬ L) (¬ R))
-- A slightly stronger form of Either than WeakEither.
Alternatively : Set -> Set -> Set
Alternatively L R = (¬ L) -> R

toWeak : {a b : Set} -> Either a b -> WeakEither a b
toWeak (Inl x) x₁ = Pair.fst x₁ x
toWeak (Inr x) x₁ = Pair.snd x₁ x
toAlternatively : {a b : Set} -> Either a b -> Alternatively a b
toAlternatively (Inl x) negX = magic (negX x)
toAlternatively (Inr x) negX = x
Alternatively->WeakEither : {a b : Set} -> Alternatively a b -> WeakEither a b
Alternatively->WeakEither alt (nX , nY) = nY (alt nX)

-- There are two straightforward ways of interpreting nondeterministic success:
-- either we require that all of the alternatives succeed,
-- or that it is not the case that all alternatives fail.
-- (We need non-constructive any since the constructive disjunction gives a completely deterministic evaluation.)
allPT : PTs C R
allPT Fail P = ⊤
allPT Split P = Pair (P False) (P True)
anyPT : PTs C R
anyPT Fail P = ⊥
anyPT Split P = WeakEither (P False) (P True)

ptAll : {a : Set} (P : a -> Set) -> L a -> Set
ptAll = ptMix allPT
ptAny : {a : Set} (P : a -> Set) -> L a -> Set
ptAny = ptMix anyPT

ptAnyBool : {a : Set} (P : a -> Bool) -> (prog : L a) -> isCode prog -> Bool
ptAnyBool P (Pure x) tt = P x
ptAnyBool P (Step Fail k) prf = False
ptAnyBool P (Step Split k) prf = ptAnyBool P (k False) (prf False) || ptAnyBool P (k True) (prf True)
ptAnyBool P (Spec pre post k) ()

{-
-- TODO: why doesn't this unify?
ptAnySo : {a : Set} (P : a -> Bool) ->
  (prog : L a) -> (prf : isCode prog) ->
  So (ptAnyBool P prog prf) ⇔ ptAny (\x -> So (P x)) prog
ptAnySo P (Pure x) prf = iff (λ z → z) (λ z → z)
ptAnySo P (Step Fail k) prf = iff (λ z → z) (λ z → z)
ptAnySo P (Step Split k) prf with ptAnyBool P (k False) (prf False)
ptAnySo P (Step Split k) prf | True = iff (λ _ → tt) λ x x₁ → (¹ x₁) (_⇔_.onlyIf (ptAnySo P (k False) (prf False)) {!tt!})
ptAnySo P (Step Split k) prf | False with ptAnyBool P (k True) (prf True)
ptAnySo P (Step Split k) prf | False | True = iff (λ _ → tt) λ x x₁ → (² x₁) (_⇔_.onlyIf (ptAnySo P (k True) (prf True)) {!tt!})
ptAnySo P (Step Split k) prf | False | False = iff (λ x → x ((_⇔_.if (ptAnySo P {!(k False)!} {!(prf False)!})) , (_⇔_.if (ptAnySo P {!k True!} {!prf True!})))) λ ()
ptAnySo P (Spec pre post k) ()
-}

wpAll : {a : Set} {b : a -> Set} -> Post a b -> ((x : a) -> L (b x)) -> Pre a
wpAll = wpMix allPT
wpAny : {a : Set} {b : a -> Set} -> Post a b -> ((x : a) -> L (b x)) -> Pre a
wpAny = wpMix anyPT

-- Running a nondeterministic computation just gives a list of options.
-- This is independent of whether we want all or any result.
handleList : (c : C) -> List (R c)
handleList Fail = Nil
handleList Split = Cons False (Cons True Nil)
runList : {a : Set} -> (prog : L a) -> isCode prog -> List a
runList = run IsMonad-List handleList

-- So how do we specify soundness and/or completeness?
-- Since the type of our predicates is (x : a) -> b x -> Set,
-- with no reference to List,
-- in fact we will have to lift predicates to predicates about lists.
-- In this lifting, we essentially do the same as in allPT / anyPT:
-- either lift it to applying to all, or to any.
-- Then we specify that the semantics are sound for lifted predicates.
-- TODO: this feels like it is quite redundant,
-- since lift does the same as anyPT.

decideAny : {a : Set} -> (P Q : Bool) ->
  WeakEither (So P) (So Q) ->
  Either (So P) (So Q)
decideAny P Q x with P
decideAny P Q x | True = Inl tt
decideAny P Q x | False with Q
decideAny P Q x | False | True = Inr tt
decideAny P Q x | False | False = Inl (x ((λ x₁ → x₁) , (λ x₁ → x₁)))

-- We can also try to `lower' the output of runList,
-- i.e. if we prove ptAny P prog, then we have P (head (filter P (runList prog))).
-- TODO: This feels like a good correctness criterion for `any',
-- can we formalize why this is the case?
{-
anyCorrect : {a : Set} -> (P : a -> Bool) ->
  (prog : L a) -> (prf : isCode prog) ->
  ptAny (\x -> So (P x)) prog ->
  Sigma a (\x -> So (P x))
anyCorrect P (Pure x) tt h = x , h
anyCorrect P (Step Fail k) prf ()
anyCorrect P (Step Split k) prf h with ptAnyBool P (k False) (prf False)
anyCorrect P (Step Split k) prf h | True = anyCorrect P (k False) (prf False) (_⇔_.onlyIf (ptAnySo P (k False) (prf False)) {!tt!}) -- TODO: why doesn't this unify?
anyCorrect P (Step Split k) prf h | False = anyCorrect P (k True) (prf True) ({!tt!} )
anyCorrect P (Spec _ _ _) ()
-}

-- Refinement of nondeterministic programs, where we just want any result.
module AnyNondet where
  anyRefine : {a : Set} {b : a -> Set} (f g : (x : a) -> L (b x)) -> Set
  anyRefine = Refine anyPT
  anyRefine' : {bx : Set} (f g : L bx) -> Set
  anyRefine' = Refine' anyPT
  anyImpl : {a : Set} {b : a -> Set} (spec : (x : a) -> L (b x)) -> Set
  anyImpl = Impl anyPT
  anyImpl' : {bx : Set} (spec : L bx) -> Set
  anyImpl' = Impl' anyPT

  preSplit : {bx : Set} -> (Bool -> Set) -> (Bool -> bx -> Set) -> Set -> (bx -> Set) -> Pre Bool
  preSplit {bx} P' Q' P Q x = (P -> P' False) -> (P -> P' True) ->
    P' x
  postSplit : {bx : Set} -> (Bool -> Set) -> (Bool -> bx -> Set) -> Set -> (bx -> Set) -> Post Bool (K bx)
  postSplit {bx} P' Q' P Q x y = Pair (Q' x y)
    ((y : bx) -> WeakEither (Q' False y) (Q' True y) -> Q y)

  -- Useful facts about WeakEither.
  weakMap : {a b c d : Set} ->
    (f : a -> c) (g : b -> d) ->
    WeakEither a b -> WeakEither c d
  weakMap f g nnanb (nc , nd) = nnanb ((λ z → nc (f z)) , (λ z → nd (g z)))
  weakInl : {a b : Set} ->
    a -> WeakEither a b
  weakInl x (nx , ny) = nx x
  -- We can take the implication out of a WeakEither (but not into!)
  weakImplication : {a b c : Set} ->
    WeakEither (a -> b) (a -> c) ->
    a -> WeakEither b c
  weakImplication we x = weakMap (\f -> f x) (\g -> g x) we

  refineSplit : {b : Set} ->
    {pre' : Bool -> Set} {post' : Bool -> b -> Set} ->
    {pre : Set} {post : b -> Set} ->
    anyRefine' (spec' pre post)
      (Step Split (spec (preSplit pre' post' pre post) (postSplit pre' post' pre post)))
  Refine'.proof' refineSplit P (pH , postH)
    = weakMap (\snd -> (\p'H _ -> p'H pH) , snd) (\snd -> (\_ p'H -> p'H pH) , snd) (
    weakMap (\pf z arg12 -> pf (² arg12) z (¹ arg12)) (\pf z arg12 -> pf (² arg12) z (¹ arg12)) (
    weakInl (\arg1 z arg2 -> postH z (arg1 z (
    weakInl arg2)))))

  refineUnderSplit : {a : Set} ->
    (prog prog' : Bool -> L a) ->
    (anyRefine prog prog') ->
    (anyRefine' (Step Split prog) (Step Split prog'))
  Refine'.proof' (refineUnderSplit prog prog' (refinement proof)) P w
    = weakMap (λ x₁ → proof (const P) False x₁) (λ x₁ → proof (const P) True x₁) w

  doSplit : {n : Nat} {a b : Set} ->
    {pre' : Bool -> Set} {post' : Bool -> b -> Set} ->
    {pre : Set} {post : b -> Set} ->
    ((b : Bool) -> anyImpl' (spec' (preSplit pre' post' pre post b) (postSplit pre' post' pre post b))) ->
    anyImpl' (spec' pre post)
  doSplit {n} {a} {b} {pre'} {post'} {pre} {post} cases = impl'
    (Step Split \c -> Impl'.prog' (cases c))
    (λ c → Impl'.code' (cases c))
    ((spec' pre post
        ⟨ refineSplit {b} {pre'} {post'} ⟩
      (Step Split (spec (preSplit pre' post' pre post) (postSplit pre' post' pre post)))
        ⟨ refineUnderSplit (spec (preSplit pre' post' pre post) (postSplit pre' post' pre post)) (\c -> Impl'.prog' (cases c)) (refinePointwise (λ x → Impl'.refines' (cases x))) ⟩
      (Step Split \x -> Impl'.prog' (cases x)) ∎) pre-Refine')

module AllNondet where
  allImpl = Impl allPT
  allImpl' = Impl' allPT
  allRefine = Refine allPT
  allRefine' = Refine' allPT

  -- Failure always works since we only consider non-failing computations.
  doFail : {a : Set} ->
    {pre : Set} {post : a -> Set} ->
    allImpl' (spec' pre post)
  Impl'.prog' doFail = fail
  Impl'.code' doFail ()
  Refine'.proof' (Impl'.refines' doFail) P x = tt

  doSplit : {a : Set} ->
    {pre : Set} {post : a -> Set} ->
    (l r : allImpl' (spec' pre post)) ->
    allImpl' (spec' pre post)
  Impl'.prog' (doSplit (impl' progL codeL refinesL) (impl' progR codeR refinesR)) =
    progL [] progR
  Impl'.code' (doSplit (impl' progL codeL refinesL) (impl' progR codeR refinesR)) True = codeL
  Impl'.code' (doSplit (impl' progL codeL refinesL) (impl' progR codeR refinesR)) False = codeR
  Refine'.proof' (Impl'.refines' (doSplit (impl' progL codeL (refinement' proofL)) (impl' progR codeR (refinement' proofR)))) P x = (proofR P x) , (proofL P x)

  -- We need to define the doBind combinator here,
  -- since it relies on correctness of the predicate transformer.
  doBind : {a : Set} {b : Set} ->
    {pre : Set} {intermediate : a -> Set} {post : b -> Set} ->
    (mx : allImpl' (spec' pre intermediate)) ->
    (f : (x : a) -> allImpl' (spec' (intermediate x) post)) ->
    allImpl' (spec' pre post)
  doBind {a} {b} {pre} {intermediate} {post}
    (impl' mxProg mxCode (refinement' mxProof)) fImpl = impl'
    (mxProg >>= fProg)
    (isCodeBind mxProg fProg mxCode fCode)
    (refinement' (lemma mxProg mxProof))
   where
     fProg : (x : a) -> L b
     fProg x = Impl'.prog' (fImpl x)
     fCode : (x : a) -> isCode (fProg x)
     fCode x = Impl'.code' (fImpl x)
     fProof = \x -> Refine'.proof' (Impl'.refines' (fImpl x))
     lemma : (mxProg : L a) -> (mxProof : (P : a -> Set) -> Pair pre ((z : a) -> intermediate z -> P z) -> ptAll P mxProg) -> (P : b -> Set) -> Pair pre ((z : b) -> post z -> P z) -> ptAll P (mxProg >>= fProg)
     lemma (Pure x) mxProof P (fst , snd) = fProof x P (mxProof intermediate (fst , (λ x₁ x₂ → x₂)) , snd)
     lemma (Step Fail k) mxProof P (fst , snd) = tt
     lemma (Step Split k) mxProof P (fst , snd) = lemma (k False) (λ P₁ z → Pair.fst (mxProof P₁ z)) P (fst , snd) , lemma (k True) (λ P₁ z → Pair.snd (mxProof P₁ z)) P (fst , snd)
     lemma (Spec pre' post' k) mxProof P (fst , snd) = (Pair.fst (mxProof intermediate (fst , (λ x x₁ → x₁)))) , λ z x → lemma (k z) (λ P₁ z₁ → Pair.snd (mxProof P₁ z₁) z x) P (fst , snd)

  selectPost : {a : Set} -> Post (List a) (\_ -> Pair a (List a))
  selectPost xs (y , ys) = Sigma (y ∈ xs) \i -> delete xs i == ys

  selectSpec : {a : Set} -> List a -> L (Pair a (List a))
  selectSpec = spec (K ⊤) selectPost

  selectImpl : {a : Set} -> (xs : List a) -> allImpl' (selectSpec {a} xs)
  selectImpl {a} Nil = doFail
  selectImpl {a} (Cons x xs) = doSplit
    (doReturn (x , xs) (λ _ → ∈Head , Refl))
    (doBind (selectImpl xs) λ y,ys →
      doReturn ((Pair.fst y,ys , Cons x (Pair.snd y,ys))) lemma)
    where
    lemma : ∀ {a} {x : a} {xs : List a} {y,ys : Pair a (List a)} →
      Sigma (Pair.fst y,ys ∈ xs) (λ i → delete xs i == Pair.snd y,ys) →
      Sigma (Pair.fst y,ys ∈ Cons x xs)
      (λ i → delete (Cons x xs) i == Cons x (Pair.snd y,ys))
    lemma {a} {x} {xs} {y , ys} (fst , snd) = (∈Tail fst) , cong (Cons x) snd
