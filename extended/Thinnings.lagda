\section{Thinnings}

%if False
\begin{code}
module Thinnings where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

open import DeBruijn
\end{code}
%endif

\begin{definition}[Thinnings]
We may define the thinnings, i.e., the order-preserving embeddings,
our simultaneous renumberings, as follows:

%format <= = "\mathrel{\D{\le}}"
%format _<=_ = "\D{" _ "\!}" <= "\D{\!" _ "}"
%format -^ = "\mathbin{\C{\mathrm{-\hspace*{-0.06in}\raisebox{-0.04in}{\^{}}}}}"
%format _-^_ = "\C{" _ "\!}" -^ "\C{\!" _ "}"
%format ga = "\V{\gamma}"
%format de = "\V{\delta}"
%format ze = "\V{\zeta}"
\begin{code}
module _ {X : Set} where  -- fix a set |X| of \emph{sorts}, e.g., |Type|

  infix 10 _<=_
  infixl 20 _-^_

  data _<=_ : Bwd X ->                       Bwd X -> Set where

    _-^_  :   {-<-} forall {ga de} -> {->-}  ga       <= de
          ->  forall x ->                    ga       <= de -, x

    _-,_  :   {-<-} forall {ga de} -> {->-}  ga       <= de
          ->  forall x ->                    ga -, x  <= de -, x

    []    :                                  []       <= []
\end{code}
\end{definition}

I am careful to speak of our backward lists as \emph{scopes}, rather than
\emph{contexts}, as it is not necessary for them to document the \emph{types}
of the variables for this machinery to work.

We lift the constructors from lists to represent the situation
where parts of the source scope are copied to the target, but we also
introduce |-^| to insert an extra element in the target.

Electronic engineers will notice that a thinning is more or less a vector
of bits, with |-^| for 0 and |-,| for 1, but it is indexed by its
\emph{population} --- the entries marked 1. Expect Boolean operations.

%format io = "\F{\upiota}"
\begin{definition}[identity thinnings, |io|]
Let us observe that identity thinnings exist, copying their scope.

\begin{code}
  io : forall {ga} -> ga <= ga
  io {[]}       = []
  io {ga -, x}  = io {ga} -, x
\end{code}
\end{definition}

\begin{craft}[Implicits]
Agda uses curly braces to mark arguments which are normally suppressed.
In general, it is sensible to adopt the suppression convention
appropriate for the expected \emph{use} sites. Here, the fact that |<=| is a type constructor means
that |ga| will be determined if the type is given in advance.
Often, we then have to use an explicit override at definition sites. 
This sort of thing never happens in Hindley-Milner
languages because any information for which inference is permitted is
guaranteed to be operationally useless. The inference of operationally
useful information represents progress.
\end{craft}

Further, thinnings compose. I write composition diagrammatically.

%format -fake = "\mathbin{\F{\fatsemi}}"
%format _-fake_ = "\F{" _ "\!}" -fake "\F{\!" _ "}"

\begin{definition}[thinning composition, |-fake|]
Thinnings fore and aft compose thus:

%format th = "\V{\theta}"
%format ph = "\V{\phi}"
%format ps = "\V{\psi}"
\begin{code}
  infixl 20 _-fake_

  _-fake_ : {-<-} forall {ga de ze} -> {->-} ga <= de -> de <= ze -> ga <= ze
  th         -fake (ph -^ x)  = th -fake ph -^ x
  (th -^ x)  -fake (ph -, x)  = th -fake ph -^ x
  (th -, x)  -fake (ph -, x)  = th -fake ph -, x
  []         -fake []         = []
\end{code}
\end{definition}

\begin{craft}[Operator Priority and Association]
My habit is to arrange priority and association
so that computation results in net decrease of parentheses.
\end{craft}

\begin{craft}[Laziness and Definitional Equality]
Working in intensional type theories like Agda involves a certain
amount of care with the equational properties of programs --- the typechecker
will run these programs, as defined, on open terms.
So the order of the lines in the above program matters. If the aft-thinning
inserts, there is no call to inspect the fore-thinning. Only if the aft
thinning copies need we ask what the fore-thinning gives us. If the first
line is moved later, the function becomes unnecessarily strict in the
fore-thinning, and definitional equality loses power.
\end{craft}

The reader should note that I will shortly substitute a subtly different
definition of composition for this one. Rest assured that its replacement
will satisfy the above equations.

Before we move on, though, observe that our type of de Bruijn variables,
|ta <<1- Ga| can readily be expressed as the \emph{singleton} thinning,
|[] -, ta <= Ga|. Let us therefore refactor our previous definitions:

\begin{definition}[Singleton Thinning]
Element selection is given by thinning from a singleton source
\begin{code}
_<<-_ : {-<-}forall {X} ->{->-} X -> Bwd X -> Set
x <<- ga = [] -, x <= ga
\end{code}
%if False
\begin{code}
infix 10 _!!-_

data _!!-_ (Ga : Context) : Type -> Set where

  va  : {-<-} forall {ta} -> {->-}     ta <<- Ga
      ->                               Ga !!- ta

  ap  : {-<-} forall {sg ta} -> {->-}  Ga !!- sg ->> ta
      ->                               Ga !!- sg
      ->                               Ga !!- ta

  la  : {-<-} forall {sg ta} -> {->-}  Ga -, sg !!- ta
      ->                               Ga !!- sg ->> ta
\end{code}
%endif
\end{definition}

It is now immediately clear why thinnings have a sensible action on
de Bruijn terms --- thinnings act on de Bruijn variables
\emph{by composition}.

