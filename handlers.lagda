\documentclass[acmsmall, anonymous, review=false]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

%include agda.fmt
%include handlers.fmt

%include preamble.tex

\begin{document}
\title{Algebraic effects: specification and refinement}

\author{Wouter Swierstra}
\email{w.s.swierstra@@uu.nl}
\author{Tim Baanen}
\email{t.baanen@@uu.nl}
\affiliation{
\institution{Universiteit Utrecht}
}

\begin{abstract}
  Pure functions are relatively easy to verify, yet it is much harder
  to reason about programs using effects. In this paper, we present a
  general framework, based on predicate transformer semantics, for
  specifying and calculating effectful programs from their
  specification. \todo{Finalize abstract and title}
\end{abstract}

%include ccs.tex

\maketitle

\section{Introduction}
\label{sec:intro}

One of the key advantages of pure functional programming is
\emph{compositionality}. Pure programs may be tested in isolation;
referential transparency---the ability to freely substitute equals for
equals---enables us to employ equational reasoning to prove two
expressions equal~\cite{wadler-critique}. This has resulted in a rich
field of program calculation in the Bird-Meertens
style~\citep*{algebra-of-programming, pearls}.

Many programs, however, are \emph{not} pure, but instead rely on a
variety of effects, such as mutable state, exceptions,
non-termination, or non-determinism. Unfortunately, it is less clear
how to reason about impure programs in a compositional fashion, as we can
no longer exploit referential transparency to reason about
subexpressions regardless of their context.

In recent years, \emph{algebraic effects} have emerged as a technique
to incorporate effectful operations in a purely functional
language~\cite{plotkin2002notions,pretnar2010logic}.  Algebraic
effects clearly separate the syntax of effectful operations and their
semantics, described by \emph{effect handlers}. In contrast to monad
transformers, different effects may be processed in any given order
using a series of handlers.

This paper explores how to define a predicate transformer semantics
for effectful programs. It presents a constructive framework for deriving
verified effectful programs their specifications, inspired by existing
work on the refinement
calculus~\cite{back2012refinement,morgan1994programming}. We will
sketch the key techniques developed herein, before illustrating them
with numerous examples:

% What is the specification of a program written using algebraic
% effects?  How can we show that a program satisfies a specification? Or
% indeed derive a program from its specification?


\begin{itemize}
\item We show how the syntax of effects may be given by a free monad
  in type theory. The semantics of these effects are given by a
  \emph{handler}, that assigns meaning to the syntactic operations
  provided by the free monad. \todo{Avoid handlers here}
\item Next we show how to assign \emph{predicate transformer
    semantics} to computations arising from Kleisli arrows on such
  free monads. This enables us to specify the desired outcome of an
  effectful computation and assign it a weakest precondition
  semantics.
\item Using these weakest precondition semantics, we can define a
  notion of \emph{refinement} on computations using algebraic
  effects. Finally, we show how to use this refinement relation to
  show a program satisfies its specification, or indeed,
  \emph{calculate} a program from its specification.
\end{itemize}
These principles are applicable to a range of different effects,
including exceptions (Section~\ref{sec:maybe}), state
(Section~\ref{sec:state}), non-determinism
(Section~\ref{sec:non-det}), and general recursion
(Section~\ref{sec:recursion}). Each section is illustrated with
numerous examples, each selected for their portrayal of proof principles
rather than being formidable feats of formalization.


The examples, theorems and proofs have all been formally verified in
the dependently typed programming language Agda~\cite{agda}, but they
techniques translate readily to other proof assistants based on
dependent types such as Idris~\cite{brady} or Coq~\cite{coq}. The sources
associated with our our development are available
online.\footnote{\todo{url}}

\section{Background}
\label{sec:intro}
%if style == newcode
\begin{code}
{-# OPTIONS --type-in-type #-}

module Check where

open import Prelude hiding (map)
open import Level hiding (lift)

postulate
  undefinedTim : {a : Set} -> a

module Free where
\end{code}
%endif

\subsection*{Free monads}
\label{sec:free-monads}

We begin by defining a datatype for free monads in the style
of \citet{hancock-setzer-I, hancock-setzer-II}:
\begin{code}
  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
\end{code}
You may want to think of |C| as being the type of \emph{commands}. A
computation described by the free monad |Free C R| either returns a
result of type |a| or issues a command |c : C|. For each |c : C|,
there is a set of responses |R c|. The second argument of the |Step|
constructor corresponds to the continuation, describing how to proceed
after receiving a response of type |R c|. It is straightforward to
show that the |Free| datatype is indeed a monad:
\begin{code}
  map : (Forall (C R a b)) (a -> b) -> Free C R a -> Free C R b
  map f (Pure x)    = Pure (f x)
  map f (Step c k)  = Step c (\ r -> map f (k r)) 

  return : (Forall (C R a)) a -> Free C R a
  return = Pure

  _>>=_ : (Forall (C R a b)) Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x    >>= f  = f x
  Step c x  >>= f  = Step c (\ r -> x r >>= f)
\end{code}
%if style == newcode
\begin{code}
  infixr 20 _>>=_
  _>>_ : forall {a b C R} -> Free C R a -> Free C R b -> Free C R b
  c1 >> c2 = c1 >>= \_ -> c2
\end{code}
%endif
The examples of effects studied in this paper will be phrased in terms
of such free monads.

\subsection*{Weakest precondition semantics}

Weakest precondition semantics have a rich history, dating back to
Dijkstra's Guarded Command Language~\citeyearpar{gcl}. In this section, we
recall the key notions that we will use throughout the remainder of
the paper.

There are many different ways to specify the behaviour of a function
|f : a -> b|. One might provide a reference implementation, define a
relation |R : a -> b -> Set|, or write contracts and tests cases. In
this paper, we will, however, focus on \emph{predicate transformer
  semantics}. Where these predicate transformers traditionally relate
the state space of an (imperative) program, they can be readily
adapted to the functional setting.

The weakest precondition semantics, given by the function |wp| below,
maps a function |f : a -> b| and a desired postcondition on the
function's output, |b -> Set|, to the weakest precondition |a -> Set|
on the function's input that ensures the postcondition will be
satisfied:
\begin{spec}
  wp : (f : a -> b) -> (b -> Set) -> (a -> Set)
  wp f P = \ x -> P (f x)
\end{spec}

This definition is often too restrictive. In particular, there is no
way to specify that the output is related in a particular way to the
input. This can be addressed easily enough by allowing the function
|f| to be \emph{dependent}, yielding the following definition for
weakest preconditions:
\begin{code}
  wp : (Forall(a : Set)) (implicit(b : a -> Set)) (f : (x : a) -> b x) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wp f P = \ x -> P x (f x)
\end{code}
When working with predicates and predicate transformers, we will
sometimes use the following shorthand notation:
\begin{code}
  _⊆_ : (implicit(a : Set)) (a -> Set) -> (a -> Set) -> Set
  P ⊆ Q = ∀ x -> P x -> Q x  
\end{code}

One reason to use weakest precondition semantics is that they give
rise to a notion of \emph{refinement}:
\begin{code}
  _⊑_ : (implicit(a : Set)) (implicit (b : a -> Set)) (pt1 pt2 : ((x : a) -> b x -> Set) -> (a -> Set)) -> Set
  pt1 ⊑ pt2 = forall P -> pt1 P ⊆ pt2 P
\end{code}
In a pure setting, this refinement relation is not particularly
interesting: the refinement relation corresponds to extensional
equality between functions. The following lemma follows from the
`Leibniz rule' for equality in intensional type theory:

\begin{lemma*}
  For all functions, \emph{|f : a -> b|} and \emph{|g : a -> b|}, the refinement
  \emph{|wp f ^^ ⊑ ^^ wp g|} holds if and only if \emph{|f x == g x|} for all \emph{|x : a|}.
\end{lemma*}

Although these definitions work for arbitrary functions, we have not
yet mentioned effects at all. We will now explore how to use and adapt
these definitions to specify, verify, and calculate effectful programs.

\section{Partiality}
\label{sec:maybe}
%if style == newcode
\begin{code}
module Maybe where
  open import Data.Nat public
    using
      (_+_; _>_; _*_
      )
    renaming
      ( ℕ to Nat
      ; zero to Zero
      ; suc to Succ
      )
  open import Data.Nat.DivMod using (_div_)
  open import Data.Nat.Properties using (*-zeroʳ)        
  open Free      
\end{code}
%endif

We can define the datatype for |Partial| computations, corresponding
to |Maybe| monad, by making the following choice for commands |C| and
responses |R| in our |Free| datatype:
\begin{code}
  data C : Set where
    Abort : C

  R : C -> Set
  R Abort = ⊥

  Partial : Set -> Set
  Partial = Free C R
\end{code}
There is a single command, |Abort|; there is no continuation after
issuing this command, hence the type of valid responses is empty. It is
sometimes convenient to define a smart constructor for failure:
\begin{code}
  abort  : (Forall(a)) Partial a
  abort  = Step Abort (\ ())
\end{code}
A computation of type |Partial a| will either return a value of type
|a| or fail, issuing the |abort| command. With the syntax in place, we
can turn our attention to verifying programs using a suitable
predicate transformer semantics.


\subsection*{Example: division}

We begin by defining a small expression language, closed under
division and natural numbers:

\begin{code}
  data Expr : Set where
    Val : Nat -> Expr
    Div : Expr -> Expr -> Expr
\end{code}

To evaluate these expressions, we can define a \emph{monadic}
interpreter, using the |Partial| monad to handle division-by-zero
errors:

\begin{code}
  ⟦_⟧ : Expr -> Partial Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    v1 ÷ v2
                      where
                      _÷_ : Nat -> Nat -> Partial Nat
                      n ÷ Zero      = abort
                      n ÷ (Succ k)  = return (n div (Succ k))
\end{code}
The division operator from the standard library (|div|) requires an
implicit proof that the divisor is non-zero. In the case when the
divisor is |Zero|, we fail explicitly.

Alternatively, we can specify the semantics of our language using a
\emph{relation}:
\begin{code}
  data _⇓_ : Expr -> Nat -> Set where
    Base : (Forall(x)) Val x ⇓ x
    Step : (Forall(l r v1 v2)) l ⇓ v1 -> r ⇓ (Succ v2) -> Div l r ⇓ (v1 div (Succ v2))
\end{code}
In this definition, we rule out erroneous results by requiring that
the divisor always evaluates to a non-zero value.

How can we relate these two definitions? We can define a weakest
precondition semantics using the |wp| function defined previously
to computations of type |Partial b|:
\begin{code}
  wpPartial : (implicit (a : Set)) (implicit (b : a -> Set)) (f : (x : a) -> Partial (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpPartial f P = wp f (mustPT P)
    where
    mustPT : (Forall(a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> Partial (b x) -> Set
    mustPT P _ (Pure y)          = P _ y
    mustPT P _ (Step Abort _)    = ⊥
\end{code}
To call the |wp| function we defined previously, we need to show how
to transform a predicate |P : b -> Set| to a predicate on partial
results, |Partial b -> Set|.  To do so, we define the auxiary function
|mustPT|; the proposition |mustPT P c| holds when a computation |c| of
type |Partial b| successfully returns a value of type |b| that
satisfies |P|.

As a first attempt, we might define the following predicate
characterizing when evaluation is guaranteed to produce a result:
\begin{code}
  SafeDiv : Expr -> Set
  SafeDiv (Val x)       = (Val x ⇓ Zero) -> ⊥
  SafeDiv (Div e1 e2)   = (e2 ⇓ Zero -> ⊥) × SafeDiv e1 × SafeDiv e2
\end{code}
We can now show that |SafeDiv| is a sufficient condition for our two
notions of evaluation to coincide:
\begin{code}
  correct : SafeDiv ⊆ wpPartial ⟦_⟧ _⇓_
\end{code}
%if style == newcode
\begin{code}
  correct (Val x) h = Base
  correct (Div e1 e2 ) (nz , (h1 , h2)) with ⟦ e1 ⟧ | ⟦ e2 ⟧ | correct e1 h1 | correct e2 h2
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure v1 | Pure Zero | ih1 | ih2 = magic (nz ih2)
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure v1 | Pure (Succ v2) | ih1 | ih2 = Step ih1 ih2
  correct (Div e1 e2) (nz , (h1 , h2)) | Pure x | Step Abort x₁ | ih1 | ()
  correct (Div e1 e2) (nz , (h1 , h2)) | Step Abort x | v2 | () | ih2
\end{code}
%endif
That is, we can \emph{compute} the weakest precondition |wpPartial ⟦_⟧
_⇓_| that guarantees that a partial computation, here the evaluation
|⟦ e ⟧| of some expression |e|, returns a result satisfying the
behaviour specified by the relation |_⇓_|. The |wpPartial| function
assigns a \emph{predicate transformer semantics} to Kleisli arrows;
the above lemma relates the two semantics, expressed as a relation and
an evaluator, for those expressions that satisfy the |SafeDiv|
property.

We may not want to define predicates such as |SafeDiv|
ourselves. Instead, we can define the more general predicate
characterizing the \emph{domain} of a partial function:
\begin{code}
  dom : (implicit(a : Set)) (implicit (b : a -> Set)) ((x : a) -> Partial (b x)) -> (a -> Set)
  dom f = wpPartial f (\ _ _ -> ⊤)
\end{code}
Indeed, we use this notion of domain to show that the two semantics
agree precisely:
\begin{code}
  sound     : dom ⟦_⟧            ^^ ⊆ ^^ wpPartial ⟦_⟧ _⇓_
  complete  : wpPartial ⟦_⟧ _⇓_  ^^ ⊆ ^^ dom ⟦_⟧
\end{code}
%if style == newcode
\begin{code}
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

  aux : (e : Expr) (v : Nat) -> ⟦ e ⟧ ≡ Pure v -> e ⇓ v
  aux e v eq with sound e (inDom e eq) 
  ... | H rewrite eq = H

  wpPartial1 : {e1 e2 : Expr} -> wpPartial ⟦_⟧ _⇓_ (Div e1 e2) -> wpPartial ⟦_⟧ _⇓_ e1
  wpPartial1 {e1} {e2} h with ⟦ e1 ⟧ | inspect ⟦_⟧ e1 | ⟦ e2 ⟧
  wpPartial1 {e1} {e2} () | Pure x | eq | Pure Zero
  wpPartial1 {e1} {e2} h | Pure x | [[[ eq ]]] | Pure (Succ y) = aux e1 x eq
  wpPartial1 {e1} {e2} () | Pure x | eq | Step Abort x₁
  wpPartial1 {e1} {e2} () | Step Abort x | eq | ve2

  wpPartial2 : {e1 e2 : Expr} -> wpPartial ⟦_⟧ _⇓_ (Div e1 e2) -> wpPartial ⟦_⟧ _⇓_ e2
  wpPartial2 {e1} {e2} h with ⟦ e1 ⟧ | inspect ⟦_⟧ e1 | ⟦ e2 ⟧ | inspect ⟦_⟧ e2
  wpPartial2 {e1} {e2} h | Pure x | [[[ eqx ]]] | Pure y | [[[ eqy ]]] = aux e2 y eqy
  wpPartial2 {e1} {e2} () | Pure x | [[[ eq ]]] | Step Abort x₁ | eq2
  wpPartial2 {_} {_} () | Step Abort x | eq1 | se2 | eq2

  complete (Val x) h = tt
  complete (Div e1 e2) h
    with ⟦ e1 ⟧ | inspect ⟦_⟧ e1 | ⟦ e2 ⟧ | inspect ⟦_⟧ e2
      | complete e1 (wpPartial1 {e1} {e2} h)
      | complete e2 (wpPartial2 {e1} {e2} h)
  complete (Div e1 e2) h | Pure x | [[[ eqx ]]] | Pure Zero | [[[ eqy ]]] | p1 | p2
    rewrite eqx | eqy = magic h
  complete (Div e1 e2) h | Pure x | [[[ eqx ]]] | Pure (Succ y) | [[[ eqy ]]] | p1 | p2 = tt
  complete (Div e1 e2) h | Pure x | eq1 | Step Abort x₁ | eq2 | p1 | ()
  complete (Div e1 e2) h | Step Abort x | eq1 | se2 | eq2 | () | p2
\end{code}
%endif
Both proofs proceed by induction on the argument expression; despite
the necessity of a handful of auxiliary lemmas, they are
fairly straightforward.

\subsection*{Refinement}

The weakest precondition semantics on partial computations defined
above gives rise to a refinement relation on Kleisli arrows of the
form |a -> Partial b|. We can characterize this relation by proving
the following lemma.
\begin{lemma*}
  For all functions, \emph{|f : a -> Partial b|} and \emph{|g : a -> Partial b|},
  the refinement relation \emph{|wpPartial f ⊑ wpPartial g|} holds if and only if for all \emph{|x :
  a|}, \emph{|f x == g x|} or \emph{|f x == Abort|}.
\end{lemma*}  
Why care about this refinement relation? Not only can we use it to
relate Kleisli morphisms, but it can also relate a program to a
specification given by a pre- and postcondition, as we shall see
shortly.

\subsection*{Example: \textsc{Add}}

Suppose we are writing an interpreter for a simple stack machine. To
interpret the |ADD| instruction, we replace the top two elements of
the stack with their sum. Of course, this may fail if the stack has
too few elements. This section shows how to prove that the obvious
definition meets its specification.

We begin by defining a notion of specification in terms of a pre- and
postcondition. In general, the specification of a function of type |(x
: a) -> b x| consists of a precondition on |a| and a postcondition
relating inputs that satisfy this precondition and the corresponding outputs:

\begin{code}
  record Spec (a : Set) (b : a -> Set) : Set where
    constructor [[_,_]]
    field
      pre : a -> Set
      post : (x : a) -> b x -> Set
\end{code}
As is common in the refinement calculus literature, we will write |[[
P , Q ]]| for the specification consisting of the precondition |P| and
postcondition |Q|. In many of our examples, the type |b| does not
depend on |x : a|, motivating the following type synonym:
\begin{code}
  SpecK : Set -> Set -> Set
  SpecK a b = Spec a (K b)
\end{code}
This definition uses the combinator K to discard the unused argument
of type |a|.

Using this definition, we can define the following specification for
our addition function:
\begin{code}
  data Add : List Nat -> List Nat -> Set where
    AddStep : (implicit(x1 x2 : Nat)) (implicit(xs : List Nat)) Add (x1 :: x2 :: xs) ((x1 + x2) :: xs)

  addSpec : SpecK (List Nat) (List Nat)
  addSpec = [[ (\ xs -> length xs > 1) , Add ]]
\end{code}
That is, provided we are given a list with at least two elements, we
should replace the top two elements with their sum. Here we describe
the desired postcondition by introducing a new datatype, |Add|,
relating the input and output stacks, but there are many equivalent
ways to formulate the desired property.

How can we relate this specification to an implementation? We have
seen how the |wpPartial| function assigns predicate transformer
semantics to functions---but we do not yet have a corresponding
predicate transform \emph{semantics} for our specifications. The
|wpSpec| function does precisely this:
\begin{code}
  wpSpec : (Forall(a)) (implicit(b : a -> Set)) Spec a b -> (P : (x : a) -> b x -> Set) -> (a -> Set)
  wpSpec [[ pre , post ]] P = \ x -> (pre x) × (post x ⊆ P x)
\end{code}
Given a specification, |Spec a b|, the |wpSpec| function computes the
weakest precondition necessary to satisfy an arbitrary postcondition
|P|: namely, the specification's precondition should hold and its
postcondition must imply |P|.

Using this definition we can precisely formulate our the problem at
hand: can we find a program |add : List a -> Partial (a × List
a)| that refines the specification given by |addSpec|:
\begin{spec}
  correctnessAdd : wpSpec addSpec ⊑ wpPartial add
\end{spec}
Defining such a program and verifying its correctness is entirely
straightforward:
\begin{code}
  pop : (Forall (a)) List a -> Partial (a × List a)
  pop Nil = abort
  pop (x :: xs) = return (x , xs)

  add : List Nat -> Partial (List Nat)
  add xs =
    pop xs >>= \{ (x1 , xs) -> 
    pop xs >>= \{ (x2 , xs) ->
    return ((x1 + x2) :: xs)}}
\end{code}
%if style == newcode
\begin{code}
  correctnessAdd : wpSpec addSpec ⊑ wpPartial add  
  correctnessAdd P Nil (() , _)
  correctnessAdd P (x :: Nil) (Data.Nat.s≤s () , _)
  correctnessAdd P (x :: y :: xs) (_ , H) = H (x + y :: xs) AddStep
\end{code}
%endif
We include this example here to illustrate how to use the refinement
relation to relate a \emph{specification}, given in terms of a pre-
and postcondition, to its implementation. When compared to the
refinement calculus, however, we have not yet described how to mix
code and specifications---\todo{a point we will return to
  later}. Before doing so, however, we will explore several other
effects, their semantics in terms of predicate transformers, and the
refinement relation that arises from these semantics.

\subsection*{Alternatives}
\label{alternative-abort}

The predicate transformers arising from the |wpPartial| function are
not the only possible choice of semantics. In particular, sometimes we
may use the |Abort| command to `short-circuit' a computation and
handle the corresponding exception. This section explores how to adapt
our definitions accordingly.

Suppose have a function that computes the product of the numbers
stored in a list:
\begin{code}
  product : List Nat -> Nat
  product = foldr _*_ 1
\end{code}
If this list contains a zero, we can short circuit the computation and
return zero immediately. To do so, we define the following
computation:
\begin{code}
  fastProduct : List Nat -> Partial Nat
  fastProduct Nil                 = return 1
  fastProduct (Zero :: xs)        = abort
  fastProduct (k :: xs)           = map (_*_ k) (fastProduct xs)
\end{code}
To run this computation, we provide a handler that maps |abort| to
some default value:
\begin{code}
  defaultHandler : (Forall(a)) a -> Partial a -> a
  defaultHandler _ (Pure x)          = x
  defaultHandler d (Step Abort _)    = d
\end{code}

Now the question arises how to assign a suitable predicate transformer
semantics to the |fastProduct| function. We could choose to use the
|wpPartial| function we defined previously; doing so, however, would
require the input list to not contain any zeros. It is clear that we
want to assign a different semantics to our aborting computations. To
do so, we provide the following |wpDefault| function that requires the
desired postcondition |P| holds of the default value when the
computation aborts:
\begin{code}
  wpDefault : (Forall (a b : Set)) (d : b) -> (a -> Partial b) -> (P : a -> b -> Set) -> (a -> Set)
  wpDefault (hidden(a)) (hidden(b)) d f P = wp f defaultPT
    where
    defaultPT : (x : a) -> Partial b -> Set
    defaultPT x (Pure y)        = P x y 
    defaultPT x (Step Abort _)  = P x d
\end{code}
Note that we could generalize this further, allowing for |b| to depend
on |a|---as we do not need this in this example, we will refrain from
doing so.

The |wpDefault| function computes \emph{some} predicate on the
function's input. But how do we know that this predicate is meaningful
in any way? We could compute simply return a trivial predicate that is
always holds. To relate the predicate transformer semantics to the
|defaultHandler| we need to prove a simple soundness result:
\begin{code}
  soundness : (Forall (a b)) (P : a -> b -> Set) -> (d : b) -> (c : a -> Partial b) ->
    forall x -> wpDefault d c P x -> P x (defaultHandler d (c x))
\end{code}
%if style == newcode
\begin{code}
  soundness P d c x H with c x
  soundness P d c x H | Pure y = H
  soundness P d c x H | Step Abort _ = H
\end{code}
%endif
Put simply, this soundness result ensures that whenever the
precondition computed by |wpDefault| holds, the output returned by
running the |defaultHandler| satisfies the desired postcondition.

Now we can finally use our refinement relation to relate the
|fastproduct| function to the original |product| function:
\begin{code}
  correctnessProduct : wp product ⊑ wpDefault 0 fastProduct
\end{code}
%if style == newcode
\begin{code}
  correctnessProduct   P Nil H = H
  correctnessProduct   P (Zero :: xs) H = H
  correctnessProduct   P (Succ x :: xs) H
    with fastProduct xs | correctnessProduct (\xs v -> P (Succ x :: xs) _) xs H
  correctnessProduct   P (Succ x :: xs) H | Pure v | IH  = IH
  correctnessProduct   P (Succ x :: xs) H | Step Abort _ | IH rewrite *-zeroʳ x = IH
\end{code}
%endif

This example shows how to prove soundness of our predicate transformer
semantics with respect to a given handler. Semantics, such as
|wpDefault| and |wpPartial|, compute \emph{some} predicate; it is only
by proving such soundness results that we can ensure that this
predicate is meaningful. Furthermore, this example shows how different
choices of handler may exist for different effects---a point we shall
return to when discussing non-determinism (Section~\ref{sec:non-det}).


\section{Mutable state}
\label{sec:state}

%if style == newcode
\begin{code}
module State (s : Set) where
  open Free
  open Maybe using (SpecK; Spec; [[_,_]]; wpSpec)
\end{code}
%endif

In this section, we will explore how to develop similar predicate
transformer semantics for mutable state, giving rise to a familiar
Hoare logic. In what follows, we will assume a fixed type |s : Set|,
representing the type of the state. As before, we can define the
desired free monad in terms of commands |C| and responses |R|:
\begin{code}
  data C : Set where
    Get : C
    Put : s -> C

  R : C -> Set
  R Get      = s
  R (Put _)  = ⊤

  State : Set -> Set
  State = Free C R
\end{code}
To facilitate writing stateful computations, we can define a pair of
smart constructors:
\begin{code}
  get : State s
  get = Step Get return

  put : s -> State ⊤
  put s = Step (Put s) (\_ -> return tt)
\end{code}
The usual handler for stateful computations maps our free monad,
|State s|, to the state monad:
\begin{code}
  run : (Forall(a)) State a -> s -> a × s
  run (Pure x) s          = (x , s)
  run (Step Get k) s      = run (k s) s
  run (Step (Put x) k) s  = run (k tt) x 
\end{code}
Inspired by the previous section, we can define the following
predicate transformer semantics:
\begin{code}
  statePT : {b : Set} -> s -> (b × s -> Set) -> State b -> Set
  statePT s P (Pure x) = P (x , s)
  statePT s P (Step Get k) = statePT s P (k s)
  statePT _ P (Step (Put s) k) = statePT s P (k tt)
  
  wpState : forall { a b} -> (a -> State b) -> (P : a × s -> b × s -> Set) -> (a × s -> Set)
  wpState f P (x , i) = wp f (\_ -> statePT i (P (x , i))) x
\end{code}
\todo{It might be nicer to change the argument format to |statePT|, giving |statePT'|, so we can use it in the refinement relation.}
%if style == newcode
\begin{code}
  statePT' : {b : Set} -> State b -> (s -> b × s -> Set) -> s -> Set
  statePT' S P i = statePT i (P i) S
\end{code}
%endif
Given any predicate |P| relating the input, initial state, final state
and result, it computes the weakest precondition required of the input
and initial state to ensure |P| holds upon completing the
computation. As we did in the previous section for |wpDefault|, we can
prove soundness of this semantics with respect to the |run| function:
\todo{fix soundness}
\begin{code}
  soundness : {a b : Set} -> (P : a × s -> b × s -> Set) -> (c : a -> State b) ->
    (i : s) -> (x : a) ->
    wpState c P (x , i) -> P (x , i) (run (c x) i)
\end{code}
%if style == newcode           
\begin{code}
  soundness {a} {b} P c i x H = lemma i (c x) H
    where
    lemma : (st : s) -> (statec : State b) -> (statePT st (P (x , i)) statec) -> P (x , i) (run statec st)
    lemma i (Pure y) H = H
    lemma i (Step Get k) H = lemma i (k i) H
    lemma i (Step (Put s) k) H = lemma s (k tt) H
  
\end{code}
%endif

\subsection*{Example: tree labelling}
\label{sec:trees}
%if style == newcode
\begin{code}
module Relabel where
  open Free
  open Maybe using (Spec; SpecK; [[_,_]]; wpSpec)
  open import Data.Nat public
    using
      (_+_; _>_; _*_
      )
    renaming
      ( ℕ to Nat
      ; zero to Zero
      ; suc to Succ
      )
  module StateNat = State Nat
  open StateNat
\end{code}
%endif

To show how to reason about stateful programs using our weakest
precondition semantics, we revisit a classic verification problem
proposed by \citet{hutton2008reasoning}: given a binary tree as input,
relabel this tree so that each leaf has a unique number associated
with it. A typical solution uses the state monad to keep track of the
next unused label. The challenge that \citeauthor{hutton2008reasoning}
pose is to reason about the program, without expanding the definition
of the monadic operations. As we do so, we will show how several
familiar properties of the refinement relation that can be used to
reason about \emph{arbitrary} effects.



We begin by defining the type of binary trees:
\begin{code}
  data Tree (a : Set) : Set where
    Leaf  : a -> Tree a
    Node  : Tree a -> Tree a -> Tree a
\end{code}
%if style == newcode
\begin{code}  
  flatten : ∀ {a} -> Tree a -> List a
  flatten (Leaf x)    = [ x ]
  flatten (Node l r)  = flatten l ++ flatten r

  size : ∀ {a} -> Tree a -> Nat
  size (Leaf x)    = 1
  size (Node l r)  = size l + size r

  seq : Nat -> Nat -> List Nat
  seq i Zero = Nil
  seq i (Succ n) = Cons i (seq (Succ i) n)
\end{code}
%endif
One obvious choice of specification might be the following:
\begin{code}
  relabelSpec1 : (Forall(a)) SpecK (Tree a × Nat) (Tree Nat × Nat)
  relabelSpec1 = [[ K ⊤ , (\ { (t , s) (t' , s') → flatten t' == (seq (s) (size t))}) ]]
\end{code}
The precondition of this specification is trivially true regardless of
the input tree and initial state; the postcondition states that
flattening the resulting tree |t'| produces the sequence of numbers
from |s| to |s + size t|, where |t| is the initial input tree.

We can now define the obvious relabelling function as follows:
%if style == newcode
\begin{code}
  fresh : State Nat
  fresh =  get >>= \ n ->
           put (Succ n) >>
           return n
\end{code}
%endif
\begin{code}         
  relabel : (Forall(a)) Tree a -> State (Tree Nat)
  relabel (Leaf x)    = map Leaf fresh
  relabel (Node l r)  =
    relabel l >>= \ l' ->
    relabel r >>= \ r' ->
    return (Node l' r') 
\end{code}
Here the auxiliary function |fresh| increments the current state and
returns its value.

Next, we would like to show that this definition satisfies the
intended specification. To do so, we can use our |wpState| function to
compute the weakest precondition semantics of the relabelling
function and formulate the desired correctness property:

\begin{code}
  ⟦relabel⟧ : (Forall(a)) (Tree a × Nat -> Tree Nat × Nat -> Set) -> (Tree a × Nat -> Set)
  ⟦relabel⟧ P = wpState (relabel) P

  correctnessRelabel : (Forall(a : Set)) wpSpec (instantiate (relabelSpec1)) ⊑ ⟦relabel⟧
\end{code}
Unfortunately, the direct proof of this statement fails. The induction
hypothesis in the case for the |Node| constructor is too weak. In
particular, it does provide any useful information about the
intermediate state resulting from the traversal of the left subtree.

Fortunately, however, we can define several auxiliary lemmas to find a
suitable proof. Firstly, the refinement relation is both reflexive and
transitive:
\begin{code}
  ⊑-trans  : (implicit (a : Set)) (implicit (b : a -> Set)) (implicit (P Q R : ((x : a) -> b x -> Set) -> (a -> Set))) P ⊑ Q -> Q ⊑ R -> P ⊑ R

  ⊑-refl   : (implicit (a : Set)) (implicit (b : a -> Set)) (implicit (P : ((x : a) -> b x -> Set) -> (a -> Set))) P ⊑ P  
\end{code}
%if style == newcode
\begin{code}
  ⊑-trans {a} {b} {P} {Q} {R} r1 r2 p x y = r2 p x (r1 p x y)
  ⊑-refl {a} {b} {P} p x H = H  
\end{code}
%endif
Furthermore, we can formulate and prove the usual laws for
weakening of preconditions and strengthening of postconditions:
\begin{code} 
  weakenPre  : (implicit(a : Set)) (implicit(b : a -> Set)) (implicit(P P' : a -> Set)) (implicit(Q : (x : a) -> b x -> Set)) P ⊆ P' -> wpSpec [[ P , Q ]] ⊑ wpSpec [[ P' , Q ]]

  strengthenPost     : (implicit(a : Set)) (implicit(b : a -> Set)) (implicit(P : a -> Set)) (implicit(Q Q' : (x : a) -> b x -> Set)) (forall (x : a) -> Q' x ⊆ Q x) -> wpSpec [[ P , Q ]] ⊑ wpSpec [[ P , Q' ]]
\end{code}
%if style == newcode
\begin{code}
  weakenPre H1 p H2 (pre , post) = (H1 H2 pre , post)  
  strengthenPost H1 p H2 (pre , post) = (pre , \ x y → post x (H1 _ x y))  
\end{code}
%endif
While easy to prove, these results are indispensible: they allow
complex refinement proofs to be split into smaller pieces. In our
example, we can strengthen our postcondition as follows:

\begin{code}
  relabelSpec2 : (Forall(a)) SpecK (Tree a × Nat) (Tree Nat × Nat)
  relabelSpec2 = [[ K ⊤ , post ]]
    where
    post : (Forall(a)) Tree a × Nat -> Tree Nat × Nat -> Set
    post (t , s) (t' , s') = (flatten t' == (seq (s) (size t))) ∧ (s + size t == s')
\end{code}
Using the transitivity of the refinement relation and strengthening of
postcondition lemmas, we can now complete the proof that the |relabel|
function satisfies its specification.
%if style == newcode
\begin{code}
  correctnessRelabel = ⊑-trans {Q = wpSpec relabelSpec2} (strengthenPost step1) step2
    where
      open NaturalLemmas
      step1 : ∀ {a} -> (x : Tree a × Nat) -> (Spec.post relabelSpec2 x) ⊆ (Spec.post relabelSpec1 x)
      step1 x y (fst , snd) = fst
      step2 : wpSpec relabelSpec2 ⊑ ⟦relabel⟧
      step2 P (Leaf x , s) (fst , snd) = snd (Leaf s , Succ s) (refl , plus-one s)
      step2 P (Node l r , s) (fst , snd) = undefinedTim
\end{code}
%endif

\todo{Tim: kan jij het bewijs in de sourcode hierboven afmaken?
  Gebruiken we hier de rules of consequence hieronder? En gelden die
  niet voor alle effecten (mits de bijbehorende predicate transformers
  monotoon zijn?)}

\subsection*{Rule of consequence}
\label{sec:consequence}

Unsurprisingly, reasoning about programs written using the state monad
give rise to the typical pre- and postcondition reasoning found in the
verification of imperative programs. It is worth considering some more
general results that we can show about our programs:

%if style == newcode
\begin{code}
  distributePT : {a b : Set} (mx : State a) (f : a -> State b)->
    ∀ i P → statePT i P (mx >>= f) ≡ statePT i (wpState f λ _ → P) mx
  distributePT (Pure x) f i P = refl
  distributePT (Step Get k) f i P = distributePT (k i) f i P
  distributePT (Step (Put x) k) f i P = distributePT (k tt) f x P
\end{code}
%endif
\begin{code}
  monotone : {a : Set} (mx : State a) ->
    (Forall (P Q)) P ⊆ Q -> ∀ i -> statePT i P mx -> statePT i Q mx
  monotone (Pure x) H i H1 = H (x , i) H1
  monotone (Step Get k) H i H1 = monotone (k i) H i H1
  monotone (Step (Put x) k) H i H1 = monotone (k tt) H x H1
\end{code}
\begin{code}
  consequence1 : {a b : Set} (mx my : State a) (f : a -> State b)->
    statePT' mx ⊑ statePT' my ->
    statePT' (mx >>= f) ⊑ statePT' (my >>= f)
  consequence1 mx my f H P i H1 =
    let H1' = coerce (distributePT mx f i (P i)) H1
    in coerce (sym (distributePT my f i (P i))) (H (λ x → wpState f (λ _ → P i)) i H1')

  consequence2 : {a b : Set} (mx : State a) (f g : a -> State b)->
    ((x : a) -> statePT' (f x) ⊑ statePT' (g x)) ->
    statePT' (mx >>= f) ⊑ statePT' (mx >>= g)
  consequence2 (Pure x) f g H P i H1 = H x (λ _ → P i) i H1
  consequence2 (Step Get k) f g H P i H1 = consequence2 (k i) f g (λ x P' i' → H x (λ _ → P' i') i') (λ _ → P i) i H1
  consequence2 (Step (Put x) k) f g H P i H1 = consequence2 (k tt) f g (λ x' P' i' → H x' (λ _ → P' i') i') (λ _ → P i) x H1
\end{code}

\todo{What is the refinement relation arising from wpState?}

\subsection*{Equations}

%if style == newcode
\begin{code}
module Laws (s : Set) where
  open Free
  open Maybe using (SpecK; Spec; [[_,_]]; wpSpec)
  module StateS = State s
  open StateS
  postulate
    a : Set
    k0 : State a
    k1 : s -> State a
    k2 : s -> s -> State a    
    x y : s
\end{code}
%endif


Typically the intended semantics of algebraic effects is given by
means of \emph{equations}, identifying syntactically different
terms. Indeed, the genesis of algebraic effects can be found in the
work by \citet{plotkin2002notions}, that identified a handful of
equations on relating |get| and |put| operations that completely
determined the state monad. How do these equations relate to the
weakest precondition semantics presented here? 

Firstly, we can define the following equivalence relation between
stateful computations:
\todo{fixme}
\begin{spec}
  _≃_ : (Forall(a)) State a  -> State a -> Set
  t1 ≃ t2 = (wpStateR t1 ⊑ wpStateR t2) ∧ (wpStateR t2 ⊑ wpStateR t1)
\end{spec}  
To establish that an equation between two terms |t1| and |t2| holds
with respect to the |wpStateR| semantics, amounts to proving that |t1
≃ t2|. For example, the following four laws follow immediately from
our definitions for all |k|, |x|, and |y|:
%{
%if style == poly
%format k0 = k
%format k1 = k
%format k2 = k
%endif
\begin{spec}
  law1 : k0 ≃ (get >>= \ s -> put s >> k0)
  law2 : (get >>= \ s1 -> get >>= \ s2 -> k2 s1 s2) ≃ (get >>= \ s -> k2 s s)
  law3 : (put y >> (put x >> k0)) ≃ (put x >> k0)
  law4 : (put x >> (get >>= k1)) ≃ (put x >> k1 x)
\end{spec}
%}
%if style == newcode
\begin{spec}
  law1 = (λ P x z → z) , (λ P x z → z)
  law2 = (λ P x z → z) , (λ P x z → z)
  law3 = (λ P x z → z) , (λ P x z → z)
  law4 = (λ P x z → z) , (λ P x z → z)
\end{spec}
%endif
More generally, we can use such an equivalence relation to verify that
the predicate transformer semantics defined respect a set of equations
that are expected to hold for a given algebraic effect.

\section{Nondeterminism}
\label{sec:non-det}

Can we repeat this construction of predicate transformer semantics for
other effects? In this section, we will show how we can define a
weakest precondition semantics for non-deterministic
computations. Once again, we begin by defining a free monad describing
the effects that can be used to describe such
computations:

%if style == newcode
\begin{code}
module Nondeterminism where

  open Free
\end{code}
%endif

\begin{code}
  data C : Set where
    Fail : C
    Choice : C

  R : C -> Set
  R Fail    = ⊥
  R Choice  = Bool
\end{code}
Here we have chosen to define two possible commands: |Fail| and
|Choice|. The |Fail| constructor corresponds to a non-deterministic
computation that will not return any results; conceptually, the
|Choice| constructor takes two arguments and non-deterministically
chooses between them. To model this, the response used in the
continuation of the free monad, |R Choice|, is a |Bool|, indicating
which argument to choose. We can make this more clear by defining the
following shorthands for non-deterministic computations, |ND|, and
its constructors:
\begin{code}
  ND : Set -> Set
  ND = Free C R

  fail : (Forall(a)) ND a
  fail = Step Fail (\ ())

  choice : (Forall(a)) ND a -> ND a -> ND a
  choice c1 c2 = Step Choice (\ b -> if b then c1 else c2)
\end{code}
Next, we turn our attention to defining a suitable predicate
transformer semantics on Kleisli arrows of the form |(x : a) -> ND (b
x)|. There are two canonical ways to do so:

\begin{code}
  wpAll : (Forall (a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> ((x : a) -> ND (b x)) -> (a -> Set)
  wpAll P f = wp f (allPT P)
    where
    allPT : (Forall (a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> ND (b x) -> Set
    allPT P _ (Pure x)         = P _ x
    allPT P _ (Step Fail k)    = ⊥
    allPT P _ (Step Choice k)  = allPT P _ (k True) ∧ allPT P _ (k False)

  wpAny : (Forall (a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> ((x : a) -> ND (b x)) -> (a -> Set)
  wpAny P f = wp f (anyPT P)
    where
    anyPT : (Forall (a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> ND (b x) -> Set
    anyPT P _ (Pure x)         = P _ x
    anyPT P _ (Step Fail k)    = ⊤
    anyPT P _ (Step Choice k)  = anyPT P _ (k True) ∨ anyPT P _ (k False)
\end{code}
These two predicate transformers are dual: |allPT P| holds of a
non-deterministic computation precisely when \emph{all} possible
results satisfy |P|; |anyPt P| holds of a non-deterministic
computation precisely when \emph{some} possible result satisfies |P|.
We can relate both these predicates to the usual `list handler' for
non-determinism and prove appropriate soundness results.

\todo{soundness}


\todo{These predicate transformers give rise to the following refinement relation}

\begin{spec}
  subset1 :   (f g : a -> ND b) -> ((x : a) -> Subset (g x) (f x)) <-> f ⊑ g
  subset2 :   (f g : a -> ND b) -> ((x : a) -> Subset (g x) (f x)) <-> g ⊑ f
\end{spec}

\subsection*{Example: permutations}

\section{General recursion}
\label{sec:recursion}

%if style == newcode
\begin{code}
module Recursion where

  open Free
  open import Data.Nat public
    using
      (_+_; _>_; _*_
      )
    renaming
      ( ℕ to Nat
      ; zero to Zero
      ; suc to Succ
      )

\end{code}
%endif


The description the effects covered so far should be familiar. Giving
a constructive semantics for \emph{general recursion}, however, may
seem quite difficult at first glance. There are a variety of
techniques that account for general recursion in type
theory~\cite{bove_krauss_sozeau_2016}. Inspired
by~\citet{mcbride2015turing}, however, we show how the call graph of a
recursive functions can be described as a free monad, to which we can
in turn, assign predicate transformer semantics.

Suppose we wish to define a recursive function of type |(i : I) -> O
i|, for some input type |I : Set| and output type |O : I -> Set|. If
the recursion is structural, we typically do so by induction on
|I|. If it is not, we may still want to describe the intended function
and its behaviour---deferring any proof of termination for the
moment. We can describe such functions as follows:
\begin{code}
  _~~>_ : (I : Set) (O : I → Set) → Set
  I ~~> O = (i : I) → Free I O (O i)
\end{code}
Once again, we have a Kleisli arrow on the |Free| monad. The choice of
`commands' and `responses', however, are somewhat puzzling at
first. The intuition is that the `effect' we allowed to use amounts to
consulting an oracle, that given an input |i : I| returns the
corresponding output in |O i|.

As before, we define a smart constructor to make such calls:
\begin{spec}
  call : (Forall (I O)) (i : I) → Free I O (O i)
  call x = Step x Pure
\end{spec}
Note that we do \emph{not} define recursive functions---but
rather defines an explicit representation of the call graph of the
function we wish to define.

To illustrate this point, we can define McCarthy's 91-function as follows:
\begin{spec}
  f91 : Nat ~~> K Nat
  f91 i with 100 lt i
  f91 i | yes  _  = return (i - 10)
  f91 i | no   _  = call (i + 11) >>= call
\end{spec}
This definition is not recursive, but merely makes the recursive
structure of the function body, |f91 (f91 (i+11))|, explicit. How can
we reason about such functions? As is typical in the literature on
predicate transformer semantics, we can distinguish \emph{total
  correctness} and \emph{partial correctness}.

\begin{spec}
f91-spec : Nat → Nat → Set
f91-spec i o with 100 lt i
f91-spec i o | yes _ = o == i - 10
f91-spec i o | no _ = o == 91

-- f91-proof : (n : Nat) → partial-correctness (pt f91-spec) f91 n
-- f91-proof = ?
\end{spec}

\todo{Soundness? Total vs partial correctness? Termination?}

\todo{What is the refinement relation? Is there one?}

% There are many different handlers that we can use: generating a
% coinductive trace, unfolding a fixed number of calls, calculating
% Bove-Capretta predicates, or providing a proof of
% well-foundedness. Here, we will take a slightly different approach,
% requiring that all recursive calls satisfy an \emph{invariant} to
% ensure that a given property of the output holds:

% > handle : (Inv : I -> O -> Set) (P : O -> Set) -> Rec O -> Set
% > handle Inv P (Pure x)           = P x
% > handle Inv P (Step (Call x) k)  = (o : O) -> Inv x o -> handle Inv P (k o)

% \todo{Soundness?}

% \subsection*{Example: quickSort}
% \label{quicksort}

% %if style == newcode
% \begin{code}
% module QS where  
%   open Free
% \end{code}
% %endif

% To illustrate how to reason with these invariants, we will show how to
% reason about a function that is not structurally recursive, namely
% |quickSort|. To do so, we import the |General| module, fixing the type
% of our |quickSort| function


% > open General (Pair (Nat -> Bool) (List Nat)) (List Nat)

% \begin{code}  
%     qs : List Nat -> Rec (List Nat)
%     qs Nil = return Nil
%     qs (Cons x xs) =
%        call (<=-dec x , filter (<=-dec x) xs) >>= \lts ->
%        call (>-dec x , filter (>-dec x) xs) >>= \gts ->
%        return (lts ++ ([ x ] ++ gts))

%     data IsSorted : List Nat -> Set where
%       Base : IsSorted Nil
%       Single : ∀ {x} -> IsSorted ([ x ])
%       Step : ∀ {x y ys} -> So (<=-dec x y) -> IsSorted (Cons y ys) ->
%         IsSorted (Cons x (Cons y ys))

%     correct : (xs : List Nat) ->
%       handle (\ { (p , is) o → Pair (IsSorted o) (all p o) }) IsSorted (qs xs)
%     correct Nil = Base
%     correct (Cons x xs) sxs (fst , snd) sys (fst₁ , snd₁) = {!!}
  
% \end{code}

\section{Stepwise refinement}

In the examples we have seen so far, we have typically related a
\emph{complete} program to its specification. Most work on the
refinement calculus, however, allows programs and specifications to
mix freely. Can we achieve something similar in this setting?



\begin{spec}
  data I (a : Set) : Set1 where
    Done : a -> I a
    Spec : Spec T a -> I a

  M : Set -> Set
  M a = Partial (I a)
\end{spec}
A value of type |I a| is either a result of type |a| or a
specification of type |a -> Set|, corresponding to an unfinished part
of our program calculation. The type |M a| then corresponds to
computations that \emph{mix} code and specifications.  We can easily
extend our notion of refinement to work over such a mix of code and
specification:
\begin{spec}
  wpI : (implicit(a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> I (b x) -> Set
  wpI P _ (Done y)  = P _ y
  wpI P x [[ pre , post ]]  = pre ∧ Q ⊆ P x
\end{spec}


We can use this notion of weakest precondition on |I| to define a
notion of weakest precondition for the computations in |M|, that mix
specifications and code:
\begin{spec}
  wpM : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpM f = wp f · mustPT · wpI
\end{spec}
Finally, we can revisit our notion of refinement to use these weakest
precondition semantics:
\begin{spec}  
  _⊑_ : {a : Set} {b : a -> Set} (f g : (x : a) -> M (b x)) -> Set1
  f ⊑ g = ∀ P -> wpM f P ⊆ wpM g P
\end{spec}
This refinement relation lets us compare two (possibly unfinished)
derivation fragments, consisting of a mix of code and specification.

How can we use this? Let's see another example.



\section{Open questions}
\label{sec:questions}


\begin{itemize}
\item How can we use this technology to reason about combinations of
  effects? Eg mixing state and exceptions -- tim's forthcoming paper

  
\item How can we reason about compound computations built with |>>=|
  and |>>|?  There must be some 'law of consequence' that we can
  derive for specific handlers/effects -- is there a more general
  form? What about loops/if?

\item wp (s,q) or wp (s,p) implies wp(s,q or p) -- but not the other
  way around. The implication in the other direction only holds when
  the program is deterministic.

\item Relation with Dijkstra monad?
  
\end{itemize}

Can generalize |Spec| further:

\begin{spec}
  record Spec (a : Set) (b : a -> Set) : Set where
    field
      pre : a -> Set
      post : (x : a) -> pre x -> b x -> Set
\end{spec}

\section{Discussion}
\label{sec:discussion}

\subsection{Related work}
\label{sec:related-work}

% Just do it

% Examples:
% - Dutch National Flag (with recursion)
% - Goat/Wolf/Bridge crossing

% \begin{acks}
% I would like to thank my fans.  
% \end{acks}

\todo{Size doesn't matter}

\DeclareRobustCommand{\tussenvoegsel}[2]{#2}
\bibliography{handlers}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 


