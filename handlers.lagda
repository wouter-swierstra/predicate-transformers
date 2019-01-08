\documentclass[acmsmall, nonacm]{acmart}
\settopmatter{printfolios=false,printccs=false,printacmref=false}

%include agda.fmt
%include handlers.fmt

%include preamble.tex

\begin{document}
\title{Algebraic effects: specification and refinement}

\author{Wouter Swierstra}

\affiliation{
\institution{Universiteit Utrecht}
}
\email{w.s.swierstra@@uu.nl}

\begin{abstract}
  Pure functions are relatively easy to verify, yet it is much harder
  to reason about programs using effects. In this paper, we present a
  general framework, based on predicate transformer semantics, for
  specifying and calculating effectful programs from their
  specification.
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
language~\cite{plotkin2002notions,pretnar2010logic}.
Algebraic effects clearly separate the
syntax of effectful operations and their semantics, described by
\emph{effect handlers}. In contrast to existing approaches such as
monad transformers, different effects may be processed in any given
order using a series of handlers.

This paper explores how to define a predicate transformer semantics
for effectful programs. It presents a general framework for deriving
verified effectful programs their specifications, inspired by existing
work on the refinement
calculus\cite{back2012refinement,morgan1994programming}. We will
sketch the key techniques developed herein, before illustrating them
with numerous examples:

% What is the specification of a program written using algebraic
% effects?  How can we show that a program satisfies a specification? Or
% indeed derive a program from its specification?


\begin{itemize}
\item We show how the syntax of effects may be given by a free monad
  in type theory. The semantics of these effects are given by a
  \emph{handler}, that assigns meaning to the syntactic operations
  provided by the free monad. 
  % We show how we can
  % also describe the behaviour of a program more abstractly by writing
  % handlers that compute a \emph{proposition}, capturing the expected
  % behaviour without having to execute the corresponding effects. These
  % handlers may then be used to transform predicates on the result
  % values of an effectful computation to a predicate on the entire
  % computation.
\item Next we show how to assign \emph{predicate transformer
    semantics} to computations arising from Kleisli arrows on such
  free monads. This enables us to specify the desired outcome of an
  effectful computation and assign it a weakest precondition
  semantics.
\item Using these weakest precondition semantics, we can define a
  notion of \emph{refinement} on computations using algebraic
  effects. Finally, we show how to use this refinement relation to
  calculate a program from its specification.
\end{itemize}
These principles are applicable to a range of different effects,
including exceptions (Section~\ref{sec:maybe}), non-determinism
(Section~\ref{sec:non-det}), state (Section~\ref{sec:state}), and
general recursion (Section~\ref{sec:recursion}).

The examples, theorems and proofs have all been formally verified in
the dependently typed programming language Agda~\cite{agda}, but they
techniques translate readily to other proof assistants based no
dependent types such as Idris~\cite{brady} or Coq~\cite{coq}. The sources
associated with our our development are available
online.\footnote{\todo{url}}

\section{Background}
\label{sec:intro}
%if style == newcode
\begin{code}
{-# OPTIONS --type-in-type #-}

module Check where

open import Prelude
open import Level hiding (lift)

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
  fmap : (Forall (C R a b)) (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x)    = Pure (f x)
  fmap f (Step c k)  = Step c (\ r -> fmap f (k r)) 

  return : (Forall (C R a)) a -> Free C R a
  return = Pure

  _>>=_ : (Forall (C R a b)) Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x    >>= f  = f x
  Step c x  >>= f  = Step c (\ r -> x r >>= f)
\end{code}
% Finally, we will sometimes \emph{fold} over elements of |Free C R a|
% using the following recursion principle:
% \begin{code}
%   fold : (Forall(C R a l)) (implicit(b : Set l)) ((c : C) -> (R c -> b) -> b) -> (a -> b) -> Free C R a -> b
%   fold alg pure (Pure x)    = pure x
%   fold alg pure (Step c k)  = alg c (fold alg pure . k)
% \end{code}
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
  _⊑_ : (f g : (x : a) -> b x) -> Set
  f ⊑ g = forall P -> wp f P ⊆ wp g P
\end{code}
In a pure setting, this refinement relation is not particularly
interesting: the refinement relation corresponds to extensional
equality between functions. The following lemma follows from the
`Leibniz rule' for equality in intensional type theory:

\begin{lemma*}
  For all functions, |f : a -> b| and |g : a -> b|, the refinement
  |f ^^ ⊑ ^^ g| holds if and only if |f x == g x| for all |x : a|.
\end{lemma*}

Although these definitions work for arbitrary functions, we have not
yet mentioned effects at all. We will now explore how to use and adapt
these definitions to specify, verify, and calculate effectful programs.

\section{Partiality}
\label{sec:maybe}
%if style == newcode
\begin{code}
module Maybe where

  open Free hiding (_⊑_)
  postulate
    _div_ : Nat -> Nat -> Nat
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
    mustPT P _ (Pure x)          = P _ x
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
  complete  : wpPartial ⟦_⟧ _⇓_  ^^ ⊆ ^^ dom ⟦_⟧
  sound     : dom ⟦_⟧            ^^ ⊆ ^^ wpPartial ⟦_⟧ _⇓_
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
  For all functions, |f : a -> Partial b| and |g : a -> Partial b|,
  the refinement relation |f ⊑ g| holds if and only if for all |x :
  a|, |f x == g x| or |f x == Abort|.
\end{lemma*}  
Why care about this refinement relation? Not only can we use it to
relate Kleisli morphisms, but it can be extended slightly to relate a
program to a specification given by a pre- and postcondition. We will
illustrate this further with a brief example.

\subsection*{Example: \textsc{Add}}

Suppose we are writing an interpreter for a simple stack machine. To
interpret the |ADD| instruction, we replace the top two elements of
the stack with their sum. Of course, this may fail if the stack has
too few elements. This section shows how to prove that the obvious
definition meets its specification.

We begin by defining the specification. This specification consists of
two parts: the pre- and postcondition.

\begin{code}
  record Spec (a : Set) (b : a -> Set) : Set where
    constructor spec
    field
      pre : a -> Set
      post : (x : a) -> pre x -> b x -> Set
\end{code}

The specification of our intended addition function is
\begin{code}
  data AddSpec : Stack Nat -> Stack Nat -> Set where
    AddStep : (implicit(x1 x2 : Nat)) (implicit(xs : Stack Nat)) AddSpec (x1 :: x2 :: xs) ((x1 + x2) :: xs)

  addSpec : Spec (Stack Nat) (K (Stack Nat))
  addSpec = spec (\xs -> length xs > 1) (\xs _ ys -> AddStack xs ys)
\end{code}
That is, provided we are given a list with at least two elements, we
should replace the top two elements with their sum.

Can we give predicate transformer semantics to our specifications? If
so, we can then try to prove that an implementation refines its
specification.

\begin{code}
  wpSpec : (Forall(a)) (implicit(b : a -> Set)) Spec a b -> (P : (x : a) -> b x -> Set) -> a -> Set
  wpSpec (spec pre post) P = \ x -> Sigma (pre x) (\prex -> post x prex ⊆ P x)
\end{code}

Using this definition we can formulate the verification challenge:
finding a program |add| satisfying the following statement:
\begin{spec}
    addCorrect : ∀ P -> wpSpec addSpec P ⊆ wpPartial add P
\end{spec}
Defining such a program and verifying its correctness is entirely
straightforward:
\begin{code}
  pop : (Forall (a)) Stack a -> Partial (Pair a (Stack a))
  pop Nil = abort
  pop (Cons x xs) = return (x , xs)

  add : Stack Nat -> Partial (Stack Nat)
  add xs =
    pop xs >>= \{ (x1 , xs) -> 
    pop xs >>= \{ (x2 , xs) ->
    return ((x1 + x2) :: xs)}}

  addCorrect : ∀ P -> pt addSpec P ⊆ wpPartial add P
\end{code}
We include this example here to illustrate how to use the refinement
relation to relate a \emph{specification}, given in terms of a pre-
and postcondition, to its implementation. When compared to the
refinement calculus, however, we have not yet described how to mix
code and specifications---\todo{a point we will return to
  later}. Before doing so, however, we will explore several other
effects, their semantics in terms of predicate transformers, and the
refinement relation that arises from these semantics.

% \subsection*{Example: fast multiplication}

% Suppose have a function that computes the product of the numbers
% stored in a list:

% \begin{code}
%   product : List Nat -> Nat
%   product = foldr 1 _*_
% \end{code}

% If this list contains a zero, however, we can short circuit the
% computation and return zero immediately. To do so, we define the
% following computation:

% \begin{code}
%   fastProduct : List Nat -> Partial Nat
%   fastProduct Nil                 = return 1
%   fastProduct (Cons Zero xs)      = abort
%   fastProduct (Cons (Succ k) xs)  = fmap (\ n -> Succ k * n) (fastProduct xs)
% \end{code}
% To run this computation, we provide a handler that maps |abort| to
% the default value |0|:
% \begin{code}
%   zeroHandler : Partial Nat -> Nat
%   zeroHandler (Pure x)          = x
%   zeroHandler (Step Abort _)    = 0
% \end{code}

% We would like to validate that the |product| and composition of
% |zeroHandler| |fastproduct| always compute the same result. We can
% do so directly by proving the following statement:

% \begin{spec}
%   correctness : ∀ xs -> handle Zero (fastProduct xs) == product xs
% \end{spec}
% To illustrate the approach we will take in this paper, however, we
% will explore a slightly more roundabout route. To begin, we can define
% the following predicate transformer, that, given a predicate |P : Nat ->
% Set|, maps this to a predicate on |Partial Nat|:
% \begin{code}
%   zeroPT : (P : Nat -> Set) -> Partial Nat -> Set
%   zeroPT d P (Pure x)          = P x
%   zeroPT d P (Step Abort _)    = P 0
% \end{code}
% This handler is slightly different from typical handlers that aim to
% run a computation written using algebraic effects, as it
% returns returns a \emph{proposition} rather than a \emph{value}. We can now
% reformulate our correctness property in terms of this handler as follows:
% \begin{code}
%   spec : List Nat -> Nat -> Set
%   spec xs n = product xs == n

%   correctness : ∀ xs -> zeroPT (spec xs) (fastProduct xs)
% \end{code}
% Given the specification of our computation, expressed as a relation
% between inputs and outputs, proving this correctness statement shows
% |fastProduct| satisfies its specification.

% At this point, however, there is no guarantee that the
% \emph{proposition} computed by the propositional handler
% |zeroPT| is related in any way to the result returned by our
% |zeroHandler| function. To ensure that |zeroHandler . fastproduct| does indeed
% behave as we expect, we should additionally prove that our
% propositional handler is sound with respect to the |zeroHandler|:

% \begin{spec}
%   soundness : (c : Partial Nat) (P : Nat -> Set) -> zeroPT P c -> P (zeroHandler c) 
% \end{spec}

% This example illustrates some of the key techniques used throughout
% this paper: the |zeroHandler| handles effectful computations; the
% |zeroPT| handler assigns meaning to these computations without
% executing them; the a |soundness| guarantees that it suffices to work
% with the propositions computed by the |zeroPT| handler, rather than
% reason about |zeroHandler| directly.

% Unlike many effectful programs, however, this example is \emph{total}
% and only uses the short-circuiting behaviour of |Partial| for
% efficiency. Let us now consider another example, where we truly want
% to reason about partial functions.


% % \paragraph{Soundness}

% % The |lift| function computes a predicate on computations of type
% % |Partial a|. Yet how can we know that this predicate is meaningful in
% % any way? The type of the |lift| function alone does not guarantee
% % anything about its behaviour. To relate the predicate being computed,
% % we therefore need to show that the our propositional handler is
% % \emph{sound}. 

% % Consider the usual `handler' for |Partial| that returns a default
% % value when encountering a failure:

% % \begin{code}
% %   run : (Forall (a)) a -> Partial a -> a
% %   run d (Pure x)          = x
% %   run d (Step Abort _)  = d
% % \end{code}
% % To prove the soundness of our |lift| function with respect to this
% % handler amounts to proving:
% % \begin{spec}
% %   soundness : (Forall(a)) (d : a) (P : a -> Set) (m : Partial a) -> lift P m -> P (run d m)
% % \end{spec}
% % The proof of this result follows trivially after pattern matching on
% % the monadic computation |m|. Of course, there may be alternative
% % definitions of |lift| that are sound with respect to some other
% % handler---but this depends on the intended semantics of the algebraic
% % effects involved. The crucial observation, however, is that soundness
% % of propositional handlers are always relative to another semantics.


% % \subsection*{Intermezzo: types and predicate transformers}

% % Before studying other effects, it is worth making the construction of
% % specifications more explicit.
% % \begin{itemize}
% % \item A specification on a value of type |A| is a predicate |A ->
% %   Set|;
% % \item A specification of a function of type |A -> B| is a
% %   \emph{predicate transformer} of type |(B -> Set) -> (A -> Set)|.
% % \end{itemize}
% % You may recognise this construction as the contravariant Hom functor
% % on |Set|, i.e., |Hom(_,Set)|. In our example evaluator, we wanted to
% % specify the behaviour of a function of type |Expr -> Partial Nat|. By
% % using the |lift| function, this amounts to a predicate transformer of
% % the form |(Nat -> Set) -> (Expr -> Set)|.

% % This pattern can be extended to many other effects, as we shall
% % explore now.

\section{Mutable state}
\label{sec:state}

We can do something similar for mutable state. We will define a module
parametrized by a type |s|, representing the type of our mutable
state:

\begin{code}
module State (s : Set) where
\end{code}

%if style == newcode
\begin{code}
  open Free  
\end{code}
%endif

As before, we assemble our free monad from the commands |C| and
responses |R|:

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

Once again, we can define a pair of smart constructors to make it
easier to write stateful computations:
\begin{code}
  get : State s
  get = Step Get return

  put : s -> State ⊤
  put s = Step (Put s) (\_ -> return tt)
\end{code}

The usual handler for stateful computations maps our free monad,
|State s|, to the state monad:
\begin{code}
  run : (Forall(a)) State a -> s -> Pair a s
  run (Pure x) s          = (x , s)
  run (Step Get k) s      = run (k s) s
  run (Step (Put x) k) s  = run (k tt) x 
\end{code}
Inspired by the previous sections, we can define the following
predicate transformer semantics:
\begin{code}
  lift : (Forall(a)) (P : Pair a s -> Set) -> State a -> (s -> Set)
  lift P (Pure x) s           = P (x , s)
  lift P (Step Get k) s       = lift P (k s) s
  lift P (Step (Put s') k) s  = lift P (k tt) s'
\end{code}
Given any predicate |P| on the final state and result, it
computes the weakest precondition required of the initial state to
ensure |P| holds upon completing the computation.

Once again, we can prove soundness of this predicate transformer with
respect to the |run| above:

\begin{code}
  soundness : (Forall(a)) (P : Pair a s -> Set) -> (c : State a) -> (i : s) -> lift P c i -> P (run c i)
\end{code}
%if style == newcode           
\begin{code}           
  soundness P (Pure x) i p = p
  soundness P (Step Get x) i lift = soundness P (x i) i lift
  soundness P (Step (Put x) k) i lift with soundness P (k tt)
  ... | ih = ih x lift             
\end{code}
%endif

We oftentimes want to write a specification as a \emph{relation}
between input and output states. To do so, we can partially apply the
predicate |P| before calling |lift|:
\begin{code}
  liftR : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  liftR P c s = lift (uncurry (P s)) c s
\end{code}
Reusing our previous soundness result, we can show that the |liftR|
is sound with respect to the |run| semantics defined above.

\subsection*{Example: tree labelling}
\label{sec:trees}

\todo{Do example}

\subsection*{Rule of consequence}
\label{sec:consequence}



\section{Nondeterminism}
\label{sec:non-det}

Can we repeat this construction of predicate transformer semantics for
other effects? In this section, we will show how we can lift a
predicate |a -> Set| over non-deterministic computations returning
values of type |a|. Once again, we begin by defining a free monad
describing the effects that can be used to describe non-deterministic
computations:

%if style == newcode
\begin{code}
module Nondeterminism where

  -- Define a free monad
  open Free
\end{code}
%endif

\begin{code}
  data C : Set where
    Fail : C
    Choice : C

  R : C -> Set
  R Fail = ⊥
  R Choice = Bool
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

Next, we turn our attention to lifting a predicate of type |a -> Set|
to computations of type |ND a -> Set|. There are two canonical ways to
do so:

> All : (Forall(a)) (P : a -> Set) -> ND a -> Set
> All P (Pure x) = P x
> All P (Step Fail _) = ⊤
> All P (Step Choice c) = Pair (All P (c True)) (All P (c False)) 
> 
> Any : (Forall(a)) (P : a -> Set) -> ND a -> Set
> Any P (Pure x) = P x
> Any P (Step Fail _) = ⊥
> Any P (Step Choice c) = Either (Any P (c True)) (Any P (c False))

The statement |All P nd| holds when |P| holds for \emph{all} possible
values returned by the non-deterministic computation |nd|; the
statement |Any P nd| holds when |P| holds for \emph{any} possible
value returned by the non-deterministic computation |nd|. Both these
functions could also be defined using |fold|, for instance:

\begin{spec}
All' :  (Forall(a)) (P : a -> Set) -> ND a -> Set
All' = fold (\ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) })
\end{spec}

We can relate both these predicates to the usual `list handler' for
non-determinism and prove appropriate soundness results.

% \subsection*{Example}
% \label{example-non-det}

% Using these handlers, we can reason about non-deterministic
% computations. The |guard| function, for example, can be used to prune
% computations to satisfy a given predicate:

% \begin{code}
%   guard : (Forall(a))  (p : a -> Bool) -> a -> ND a
%   guard p x = if p x then return x else fail
% \end{code}
% Subsequently, we can prove that guard will always return results
% satisfying |P|:
% \begin{code}
%   guardCorrect : (Forall(a)) (p : a -> Bool) -> (x : a) -> All (\ x -> So (p x)) (guard p x)
% \end{code}
% %if style == newcode
% \begin{code}
%   guardCorrect p x with inspect (p x)
%   guardCorrect p x | True with-≡ eq rewrite eq = lemma (p x) eq
%     where
%       lemma : (b : Bool) -> b == True -> So b
%       lemma True p = tt
%       lemma False ()
%   guardCorrect p x | False with-≡ eq rewrite eq = tt
% \end{code}
% %endif

% \todo{Bigger example? n-queens?}

\section{General recursion, totally free}
\label{sec:recursion}

% Besides these well-known effects, we can handle \emph{general
%   recursion} in a similar fashion. To do so, we introduce a module
% |General|. The module is parametrized by parametrized by two types |I|
% and |O| and will be used to capture recursive calls to a function of
% type | I -> O|:\footnote{This can be readily generalized to
%   \emph{dependent functions} of type |(i : I) -> O i|, but we will not
%     need this in the examples covered here.}

% \begin{code}
% module General (I : Set) (O : Set) where  
% \end{code}


% %if style == newcode
% \begin{code}
%   open Free  
% \end{code}
% %endif

% To represent such calls, we define a single command, corresponding to
% making a recursive call on an argument |i : I| and receiving a
% response of type |O i|:

% > data C : Set where
% >   Call : I -> C
% >
% > R : C -> Set
% > R (Call x) = O
% >
% > Rec : Set -> Set
% > Rec = Free C R

% Once again, we can define a smart constructor to make it a bit easier
% to define recursive functions.

% > call : I -> Rec O
% > call i = Step (Call i) Pure

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

\section{Incremental refinement}

The problem is that a value of type |Free C R a| is a \emph{complete}
syntax tree, which returns a value or issues the next command --
leaving no room to describe unfinished parts of the program that we
wish to calculate. To achieve this however, we can define the
following two types:

\begin{code}
  data I (a : Set) : Set1 where
    Done : a -> I a
    Spec : (a -> Set) -> I a

  M : Set -> Set1
  M a = Partial (I a)
\end{code}
A value of type |I a| is either a result of type |a| or a
specification of type |a -> Set|, corresponding to an unfinished part
of our program calculation. The type |M a| then corresponds to
computations that \emph{mix} code and specifications.  We can easily
extend our notion of refinement to work over such a mix of code and
specification:
\begin{code}
  wpI : (implicit(a : Set)) (implicit(b : a -> Set)) (P : (x : a) -> b x -> Set) -> (x : a) -> I (b x) -> Set
  wpI P _ (Done y)  = P _ y
  wpI P x (Spec Q)  = Q ⊆ P x
\end{code}
\todo{This is not quite right... Need that there is some
  implementation of Q}



We can use this notion of weakest precondition on |I| to define a
notion of weakest precondition for the computations in |M|, that mix
specifications and code:
\begin{code}
  wpM : {a : Set} -> {b : a -> Set} ->
    (f : (x : a) -> M (b x)) -> ((x : a) -> b x -> Set) -> (a -> Set)
  wpM f = wp f · mustPT · wpI
\end{code}
Finally, we can revisit our notion of refinement to use these weakest
precondition semantics:
\begin{code}  
  _⊑_ : {a : Set} {b : a -> Set} (f g : (x : a) -> M (b x)) -> Set1
  f ⊑ g = ∀ P -> wpM f P ⊆ wpM g P
\end{code}
This refinement relation lets us compare two (possibly unfinished)
derivation fragments, consisting of a mix of code and specification.

How can we use this? Let's see another example.



\section{Open questions}
\label{sec:questions}


\begin{itemize}
\item How can we use this technology to reason about combinations of
  effects? Eg mixing state and exceptions.

  
\item How can we reason about compound computations built with |>>=|
  and |>>|?  There must be some 'law of consequence' that we can
  derive for specific handlers/effects -- is there a more general
  form? What about loops/if?

\item  What is a specification of a program with effects? Can we define
  generalized refinement rules?

\item Relation with equations/equational part of algebraic effects?

\item Connection with relational specifications

\item wp (s,q) or wp (s,p) implies wp(s,q or p) -- but not the other
  way around. The implication in the other direction only holds when
  the program is deterministic.

  
\item Relation with Dijkstra monad?
  
\end{itemize}

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


