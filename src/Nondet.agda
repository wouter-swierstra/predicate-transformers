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
ptAll = wpMix allPT
ptAny : {a : Set} (P : a -> Set) -> L a -> Set
ptAny = wpMix anyPT

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
  anyRefine : {a : Set} (f g : L a) -> Set
  anyRefine = Refine anyPT
  anyImpl : {a : Set} (spec : L a) -> Set
  anyImpl = Impl anyPT

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
    anyRefine (spec pre post)
      (Step Split (\b -> spec (preSplit pre' post' pre post b) (postSplit pre' post' pre post b)))
  Refine.proof refineSplit P (pH , postH)
    = weakMap (\snd -> (\p'H _ -> p'H pH) , snd) (\snd -> (\_ p'H -> p'H pH) , snd) (
    weakMap (\pf z arg12 -> pf (² arg12) z (¹ arg12)) (\pf z arg12 -> pf (² arg12) z (¹ arg12)) (
    weakInl (\arg1 z arg2 -> postH z (arg1 z (
    weakInl arg2)))))

  refineUnderSplit : {a : Set} ->
    (prog prog' : Bool -> L a) ->
    ((b : Bool) → anyRefine (prog b) (prog' b)) ->
    (anyRefine (Step Split prog) (Step Split prog'))
  Refine.proof (refineUnderSplit prog prog' ref) P w
    = weakMap (Refine.proof (ref False) P) (Refine.proof (ref True) P) w
  doSplit : {n : Nat} {a b : Set} ->

    {pre' : Bool -> Set} {post' : Bool -> b -> Set} ->
    {pre : Set} {post : b -> Set} ->
    ((b : Bool) -> anyImpl (spec (preSplit pre' post' pre post b) (postSplit pre' post' pre post b))) ->
    anyImpl (spec pre post)
  doSplit {n} {a} {b} {pre'} {post'} {pre} {post} cases = impl
    (Step Split \c -> Impl.prog (cases c))
    (λ c → Impl.code (cases c))
    ((spec pre post
        ⟨ refineSplit {b} {pre'} {post'} ⟩
      (Step Split (λ c → spec (preSplit pre' post' pre post c) (postSplit pre' post' pre post c)))
        ⟨ refineUnderSplit
            (λ c →
               spec (preSplit pre' post' pre post c)
               (postSplit pre' post' pre post c))
            (λ c → Impl.prog (cases c)) (λ c → Impl.refines (cases c)) ⟩
      (Step Split \x -> Impl.prog (cases x)) ∎) pre-Refine)
    {-
        ⟨ refineUnderSplit (λ c → spec (preSplit pre' post' pre post c) (postSplit pre' post' pre post c)) (\c -> Impl.prog (cases c)) (λ x → Impl.refines (cases x)) ⟩
      -}

module AllNondet where
  allImpl = Impl allPT
  allRefine = Refine allPT

  allSemantics : Semantics C R IsMonad-List
  allSemantics = semantics all' allPT handleList pure' equiv bind'
    where
    pure' : ∀ {a} (P : a → Set) (x : a) → P x ⇔ Pair (P x) ⊤
    pure' P x = iff Pair.fst (λ z → z , tt)
    equiv : ∀ c (P P' : R c → Set) → ((x : R c) → P x ⇔ P' x) → allPT c P ⇔ allPT c P'
    equiv Fail P P' x = ⇔-refl
    equiv Split P P' x = ⇔-pair (x False) (x True)
    bind' : ∀ {a} (P : a → Set) c (k : R c → List a) → allPT c (λ x → all' P (k x)) ⇔ all' P (handleList c >>= k)
    bind' P Fail k = ⇔-refl
    bind' P Split k = ⇔-trans
      (all'-pair P (k False) (k True))
      (⇔-= {Q = all' P} (cong (_++_ (k False)) (++-nil (k True))))

  -- Failure always works since we only consider non-failing computations.
  doFail : {a : Set} ->
    {pre : Set} {post : a -> Set} ->
    allImpl (spec pre post)
  Impl.prog doFail = fail
  Impl.code doFail ()
  Refine.proof (Impl.refines doFail) P x = tt

  doSplit : {a : Set} ->
    {pre : Set} {post : a -> Set} ->
    (l r : allImpl (spec pre post)) ->
    allImpl (spec pre post)
  Impl.prog (doSplit (impl progL codeL refinesL) (impl progR codeR refinesR)) =
    progL [] progR
  Impl.code (doSplit (impl progL codeL refinesL) (impl progR codeR refinesR)) True = codeL
  Impl.code (doSplit (impl progL codeL refinesL) (impl progR codeR refinesR)) False = codeR
  Refine.proof (Impl.refines (doSplit (impl progL codeL (refinement proofL)) (impl progR codeR (refinement proofR)))) P x = (proofR P x) , (proofL P x)

  -- Specialize the doBind combinator via correctness of allPT
  doBindAll : {a : Set} {b : Set} ->
    {pre : Set} {intermediate : a -> Set} {post : b -> Set} ->
    (mx : allImpl (spec pre intermediate)) ->
    (f : (x : a) -> allImpl (spec (intermediate x) post)) ->
    allImpl (spec pre post)
  doBindAll = doBind allPTConserves
    where
    allPTConserves : ∀ c {P P' : R c → Set} → ((x : R c) → P x → P' x) → allPT c P → allPT c P'
    allPTConserves Fail i tt = tt
    allPTConserves Split i (fst , snd) = (i False fst) , (i True snd)

  doBind' : {a : Set} {b : Set} ->
    {pre : Set} {intermediate : a -> Set} {post : b -> Set} ->
    (mx : allImpl (spec ⊤ intermediate)) ->
    (f : (x : a) -> allImpl (spec (intermediate x) (\y -> pre -> post y))) ->
    allImpl (spec pre post)
  doBind' mx f = doIgnorePre (doBindAll mx f)

  selectPost : {a : Set} -> Post (List a) (\_ -> Pair a (List a))
  selectPost xs (y , ys) = Sigma (y ∈ xs) \i -> delete xs i == ys

  selectSpec : {a : Set} -> List a -> L (Pair a (List a))
  selectSpec xs = spec ⊤ (selectPost xs)

  selectImpl : {a : Set} -> (xs : List a) -> allImpl (selectSpec {a} xs)
  selectImpl {a} Nil = doFail
  selectImpl {a} (x :: xs) = doSplit
    (doReturn (x , xs) (λ _ → ∈Head , refl))
    (doBindAll (selectImpl xs) λ y,ys →
      doReturn ((Pair.fst y,ys , Cons x (Pair.snd y,ys))) lemma)
    where
    lemma : ∀ {a} {x : a} {xs : List a} {y,ys : Pair a (List a)} →
      Sigma (Pair.fst y,ys ∈ xs) (λ i → delete xs i == Pair.snd y,ys) →
      Sigma (Pair.fst y,ys ∈ Cons x xs)
      (λ i → delete (Cons x xs) i == Cons x (Pair.snd y,ys))
    lemma {a} {x} {xs} {y , ys} (fst , snd) = (∈Tail fst) , cong (Cons x) snd

{-
  doUsePre : {a : Set} ->
    {C : Set} {R : C -> Set} {PT : PTs C R} ->
    {pre : Set} {post : a -> Set} ->
    (pre -> Impl PT (spec ⊤ post)) -> Impl PT (spec pre post)
  doUsePre x = impl {!!} {!!} {!!}

  selectVecPost : {a : Set} {n : Nat} -> Vec (Succ n) a -> (Pair a (Vec n a)) -> Set
  selectVecPost xs (y , ys) = Sigma (y ∈v xs) \i -> deleteV xs i == ys
  selectVecSpec : {a : Set} {n : Nat} -> Vec (Succ n) a -> L (Pair a (Vec n a))
  selectVecSpec xs = spec ⊤ (selectVecPost xs)
  selectVecImpl : {a : Set} {n : Nat} -> (xs : Vec (Succ n) a) -> allImpl (selectVecSpec xs)
  selectVecImpl {a} {n} xs = doBindAll (selectImpl (Vec->List xs)) \y,ys' ->
    let y , ys' = y,ys'; ys'' = List->Vec ys' in
    doUsePre (\pre -> let ys = resize (lemma1 pre) ys'' in
    doReturn (y , ys) lemma2)
    where
    lemma1 : ∀ {a n} {xs : Vec (Succ n) a} {y,ys' : Pair a (List a)} →
      Sigma (Pair.fst y,ys' ∈ Vec->List xs)
      (λ i → delete (Vec->List xs) i == Pair.snd y,ys') →
      (length (Pair.snd y,ys')) == n
    lemma1 {a} {n} {x :: xs} {.x , .(Vec->List xs)} (∈Head , refl) = Vec->List-length xs
    lemma1 {a} {n} {x :: xs} {fst₁ , .(Cons x (delete (Vec->List xs) fst))} (∈Tail fst , refl) = trans (delete-length fst) (Vec->List-length xs)
    lemma2 : ∀ {a n} {xs : Vec (Succ n) a} {y,ys' : Pair a (List a)}
      {pre : Sigma (Pair.fst y,ys' ∈ Vec->List xs) (λ i → delete (Vec->List xs) i == Pair.snd y,ys')} →
      ⊤ →
      Sigma (Pair.fst y,ys' ∈v xs)
      (λ i → deleteV xs i == resize (lemma1 pre) (List->Vec (Pair.snd y,ys')))
    lemma2 {a} {n} {xs} {x' , .(delete (Vec->List xs) i)} {i , refl} tt = (∈List->∈Vec i) , trans (Vec->List->Vec-eq (deleteV xs (∈List->∈Vec i))) (resize-List->Vec (Vec->List-length (deleteV xs (∈List->∈Vec i))) (lemma1 (i , refl)) (deleteList==deleteVec' xs i))
  -}

  open import Permutation

  permsSpec : {a : Set} {n : Nat} -> Vec n a -> L (Vec n a)
  permsSpec xs = spec ⊤ (\ys -> IsPermutation xs ys)

  -- We need to work with vectors to prove termination.
  permsImpl : {a : Set} {n : Nat} -> (xs : Vec n a) -> allImpl (permsSpec xs)
  permsImpl {n = Zero} vNil = doReturn vNil λ _ → NilPermutation
  permsImpl {n = Succ Zero} xs@(x :: vNil) = -- We need an extra base case here, since selectVecImpl only works on Vec (Succ _).
    doReturn xs λ _ → HeadPermutation (inHead , NilPermutation)
  permsImpl {n = Succ (Succ n)} xs =
    doBindAll (selectVecImpl xs) λ y,ys →
    let (y , ys) = y,ys in
    doBind' (permsImpl ys) \zs ->
    doReturn (vCons y zs) lemma

    where
    lemma : ∀ {a n} {xs : Vec (Succ (Succ n)) a}
      {y,ys : Pair a (Vec (Succ n) a)} {zs : Vec (Succ n) a} →
      IsPermutation (Pair.snd y,ys) zs →
      Sigma (Pair.fst y,ys ∈v xs) (λ i → deleteV xs i == Pair.snd y,ys) →
      IsPermutation xs (vCons (Pair.fst y,ys) zs)
    lemma {a} {n} {x :: .(y' :: ys)} {.x , (y' :: ys)} {z :: zs} perm (inHead , refl) = HeadPermutation (inHead , perm)
    lemma {a} {n} {x :: xs} {y , (y' :: ys)} {z :: zs} (HeadPermutation (y'i , perm)) (inTail yi , p) with split-==-Cons p
    lemma {a} {n} {x :: xs} {y , (.x :: .(deleteV xs yi))} {z :: zs} (HeadPermutation (xi , perm)) (inTail yi , p) | refl , refl = perm-cons xi yi perm
