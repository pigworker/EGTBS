\documentclass[submission,copyright,creativecommons]{eptcs}
\providecommand{\event}{MSFP 2018} % Name of the event you are submitting to
\usepackage{breakurl}              % Not needed if you use pdflatex only.
%\usepackage{underscore}            % Only needed if you use pdflatex.
\usepackage{pig}
\usepackage{stmaryrd}
\usepackage{upgreek}
\usepackage[all]{xy}

\ColourEpigram
\newcommand{\D}[1]{\blue{\ensuremath{\mathsf{#1}}}}
\newcommand{\C}[1]{\red{\ensuremath{\mathsf{#1}}}}
\newcommand{\F}[1]{\green{\ensuremath{\mathsf{#1}}}}
\newcommand{\V}[1]{\purple{\ensuremath{\mathit{#1}}}}

\newcommand{\OPE}{\textbf{OPE}}

\title{Everybody's Got To Be Somewhere}
\author{
  Conor McBride
  \institute{Mathematically Structured Programming Group\\
             Department of Computer and Information Sciences\\
             University of Strathclyde, Glasgow}
  \email{conor.mcbride@@strath.ac.uk}
}
\def\titlerunning{Everybody's Got To Be Somewhere}
\def\authorrunning{C.T. McBride}
%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%format inductive = "\mathkw{inductive}"
%format constructor = "\mathkw{constructor}"
%format pattern = "\mathkw{pattern}"
%format rewrite = "\mathkw{rewrite}"
%format forall = "\forall"
%format . = "."

%if False
\begin{code}
module EGTBS where
\end{code}
%endif

\begin{document}
\maketitle

\begin{abstract}
This literate Agda paper gives a nameless \emph{co}-de-Bruijn representation of
generic (meta)syntax with binding. It owes much to the work of Sato et
al.~\cite{spss:lambda.maps} on representation of variable
binding by mapping variable use sites.  The key to any nameless
representation of syntax is how it indicates the variables we choose
to use and thus, implicitly those we neglect. The business of
\emph{selecting} is what we shall revisit with care in the sequel.
The definition leads to a new construction of hereditary substitution.
\end{abstract}

\section{Basic Equipment}

%format Set = "\D{Set}"
%format Zero = "\D{Zero}"
%format One = "\D{One}"
%format Two = "\D{Two}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
%format Tt = "\F{T\!t}"
%format <> = "\C{\langle\rangle}"
%format Sg = "\D{\Upsigma}"
%format * = "\F{\times}"
%format _*_ = _ * _
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format , = "\C{,}"
%format _,_ = _ , _
%format ! = "\C{!}"
%format !_ = ! _
We shall need finite types |Zero|, |One|, and |Two|, named for their cardinality,
and the reflection of |Two| as a set of evidence for `being |tt|'.
Dependent pairing is by means of the |Sg| type, abbreviated by |*| when non-dependent.
The \emph{pattern synonym} |!_| allows the first component to be determined by
the second: making it a right-associative prefix operator lets us write |! ! expression|
rather than |! (! (expression))|.
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
data    Zero  : Set where
record  One   : Set where constructor <>
data    Two   : Set where tt ff : Two

Tt : Two -> Set
Tt tt  = One
Tt ff  = Zero
\end{code}}
\parbox[t]{3in}{
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field fst : S; snd : T fst
  
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
pattern !_ t = _ , t
\end{code}}
%if False
\begin{code}
infixr 4 !_ _,_ _*_
open Sg
\end{code}
%endif

We shall also need to reason equationally. For all its imperfections in matters of
\emph{extensionality}, it will be convenient to define equality inductively, enabling the |rewrite| construct
in equational proofs.
%format == = "\D{=\!\!=}"
%format _==_ = _ == _
%format refl = "\C{refl}"
\begin{code}
data _==_ {X : Set}(x : X) : X -> Set where refl : x == x
\end{code}
%if False
\begin{code}
{-# BUILTIN EQUALITY _==_ #-}
infixr 6 _==_
\end{code}
%endif


\section{$\OPE_{|K|}$: The Category of Order-Preserving Embeddings}

No category theorist would mistake me for one of their own. However, the key technology
in this paper can be helpfully conceptualised categorically. Category theory is the
study of compositionality for anything, not just sets-and-functions: here, we have an
opportunity to develop categorical structure with an example apart from the usual
functional programming apparatus, as emphasized particularly in the Haskell community. This strikes me as a good opportunity to revisit the basics.

\paragraph{Category (I): Objects and Morphisms.~} A \emph{category} is given by a class of \emph{objects} and a family
of \emph{morphisms} (or \emph{arrows}) indexed by two objects: \emph{source} and
\emph{target}. Abstractly, we may write $\mathbb{C}$ for a given
category, $||\mathbb{C}||$ for its objects, and
$\mathbb{C}(S,T)$ for its morphisms with given source and target,
$S,T\in||\mathbb{C}||$.

The rest of the definition will follow shortly, but let
us fix these notions for our example, the category, $\OPE_{|K|}$, of
\emph{order-preserving embeddings} between variable scopes.
The objects of $\OPE_{|K|}$ are \emph{scopes}, which we may represent
concretely backward (or `snoc') lists giving the \emph{kinds}, |K|, of
variables. (I shall habitually suppress the kind subscript and just write
$\OPE$ for the category.)
I use backward lists, because it is traditional to write contexts to
the left of judgements in typing rules and extend them on the
right. However, I write `scope' rather than `context' as
we are characterizing at least which variables we may refer to, but perhaps
not all the information one would find in a context.
%
%format where = "\mathkw{where}"
%format Bwd = "\D{Bwd}"
%format B0 = "\C{[]}"
%format - = "\C{\mbox{{}-}\!,}"
%format _-_ = _ - _
\newcommand{\apo}{\mbox{'}}
%format <= = "\D{\le}"
%format _<= = _ <=
%format _<=_ = _ <= _
%format oz = "\C{oz}"
%format os = "\C{os}"
%format o' = "\C{o\apo}"
%format _o' = _ o'
%format _os = _ os
%
\vspace*{ -0.2in} \\
\parbox[t]{2.5in}{
\begin{code}
data Bwd (K : Set) : Set where
  _-_  : Bwd K -> K -> Bwd K
  B0   : Bwd K
\end{code}}
%if False
\begin{code}
infixl 7 _-_
\end{code}
%endif
\parbox[t]{3in}{
\begin{spec}
data _<=_ : Bwd K -> Bwd K -> Set where
  _o'  : iz <= jz ->     iz          <=  (jz  -   k)
  _os  : iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  oz   :                     B0      <=       B0
\end{spec}}

The morphisms, |iz <= jz|, of $\OPE$ give an embedding from a source
to a target scope. Colloquially, we may call them
`thinnings', as they dilute the variables of the source scope with
more.  Dually, we may see such a morphism as
expelling variables from the target scope, leaving a particular
selection as the source.  I write the step constructors postfix,
so thinnings (like scopes) grow on the right.

%if False
\begin{code}
data _<=_ {K} : Bwd K -> Bwd K -> Set where
  _o'  : forall {iz jz k} ->  iz <= jz ->     iz          <=  (jz  -   k)
  _os  : forall {iz jz k} ->  iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  oz   :                                          B0      <=       B0
\end{code}
\begin{code}
infixl 8 _o' _os
\end{code}
%endif

Now, where I give myself away as a type theorist is that I do not
consider the notion of `morphism' to make sense without prior source and
target objects. The type |iz <= jz| (which is a little more mnemonic than
$\OPE(|iz|,|jz|)$) is the type of `thinnings from |iz| to
|jz|': there is no type of `thinnings' \emph{per se}.
%if False
By making types explicit about source
and target objects, we can use the type system to ensure that thinnings
fit together properly. Programs, on the other hand, will often leave these
details to the typechecker. None the less, we can recover them whenever we
choose.
%format src = "\F{src}"
%format trg = "\F{trg}"
\begin{code}
src trg : forall {K}{iz jz : Bwd K} -> iz <= jz -> Bwd K
src {iz = iz} th = iz
trg {jz = jz} th = jz
\end{code}
%endif

Let us have an example thinning: here, we embed a scope with three variables
into a scope with five.
\[\begin{array}{r@@{\!\!}c@@{\!\!}lll}
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| & \quad\quad\quad\quad\quad|os| & |: B0 - k0 - k2 - k4 <= B0 - k0 - k1 - k2 - k3 - k4| \\
             &                  & \circ\;|k3| & \quad\quad\quad\quad|o'|\\
|k2|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k2| & \quad\quad\quad|os| \\
             &                  & \circ\;|k1| & \quad\quad|o'|\\
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|& \quad|os|\\
&&& |oz|
\end{array}\]

%format oi = "\F{oi}"
%format <&= = "\F{\fatsemi}"
%format _<&=_ = _ <&= _
%format th = "\V{\theta}"
%format ph = "\V{\phi}"
%format ps = "\V{\psi}"
%format th' = "\V{\theta^\prime}"
%format ph' = "\V{\phi^\prime}"
%format ps' = "\V{\psi^\prime}"
\paragraph{Category (II): Identity and Composition.~} In any category, certain morphisms
must exist. Each object $X\in||\mathbb{C}||$
has an \emph{identity} $\iota_X\in\mathbb{C}(X,X)$, and wherever the
target of one morphism meets the source of another, their \emph{composite}
makes a direct path:
if $f\in\mathbb{C}(R,S)$ and $g\in\mathbb{C}(S,T)$, then $(f;g)\in\mathbb{C}(R,T)$.

For example, every scope has the identity thinning, |oi|, and thinnings compose via |<&=|.
(For functions, it is usual to write $g\cdot f$ for `$g$ \emph{after} $f$' than $f;g$ for
`$f$ \emph{then} $g$', but for thinnings I retain spatial
intuition.)
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.8in}{
\begin{spec}
oi :  kz <= kz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
oi {kz = B0}      = oz
\end{spec}}
\hfill
\parbox[t]{3in}{
\begin{spec}
_<&=_ :  iz <= jz -> jz <= kz -> iz <= kz
th     <&= ph o'  = (th <&= ph) o'
th o'  <&= ph os  = (th <&= ph) o'
th os  <&= ph os  = (th <&= ph) os -- |os| preserves |<&=|
oz     <&= oz     = oz
\end{spec}}
%if False
\begin{code}
oi :  forall {K}{kz : Bwd K} ->
      kz <= kz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
oi {kz = B0}      = oz

_<&=_ :  forall {K}{iz jz kz : Bwd K} ->
         iz <= jz -> jz <= kz -> iz <= kz
th     <&= ph o'  = (th <&= ph) o'
th o'  <&= ph os  = (th <&= ph) o'
th os  <&= ph os  = (th <&= ph) os -- |os| preserves |<&=|
oz     <&= oz     = oz
\end{code}
%endif

By way of example, let us plot specific uses of identity and composition.
\[\begin{array}{r@@{\!\!}c@@{\!\!}l@@{\qquad\qquad}||@@{\qquad\qquad}r@@{\!\!}c@@{\!\!}l@@{\qquad}r@@{\!\!}c@@{\!\!}l@@{\qquad\qquad}r@@{\!\!}c@@{\!\!}l}
&|oi|&& &|th|&& &|ph|&& &|th <&= ph|& \\
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| &
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| &
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| &
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| \\
|k3|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k3| &
&&&          &                  & \circ\;|k3|&         &                  & \circ\;|k3| \\
|k2|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k2| &
&& \circ\;|k2| &          
|k2|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k2| &&& \circ\;|k2| \\
|k1|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k1| &
&&&          &                  & \circ\;|k1|&          &                  & \circ\;|k1| \\
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0| &
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|&
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|&
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|\\
\end{array}\]

\paragraph{Category (III): Laws.~} to complete the definition of a
category, we must say which laws are satisfied by identity and
composition. Composition \emph{absorbs} identity on the left and on
the right. Moreover, composition is \emph{associative}, meaning that
any sequence of morphisms which fit together target-to-source can be
composed without the specific pairwise grouping choices making a
difference. That is, we have three laws which are presented as
\emph{equations}, at which point any type theorist will want to know
what is meant by `equal': I shall always be careful to say.
Our thinnings are first-order, so |==| will serve.
%if False
\begin{code}
infixr 7 _<&=_
infixr 6 _<=_
\end{code}
%endif
With this definition in place, we may then state the laws. I
omit the proofs, which go by functional induction.
%format law-oi<&= = "\F{law-}" oi <&=
%format law-<&=oi = "\F{law-}" <&= oi
%format law-<&=<&= = "\F{law-}" <&= <&=
\[
|law-oi<&= : oi <&= th == th| \qquad
|law-<&=oi : th <&= oi == th| \qquad
|law-<&=<&= : th <&= (ph <&= ps) == (th <&= ph) <&= ps|
\]
%if False
\begin{code}
law-oi<&=   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  oi <&= th == th
law-<&=oi   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  th <&= oi == th
law-<&=<&=  :  forall {K}{iz jz kz lz : Bwd K}  (th : iz <= jz)(ph : jz <= kz)(ps : kz <= lz) ->
                                                                    th <&= (ph <&= ps) == (th <&= ph) <&= ps
law-oi<&= oz = refl
law-oi<&= (th os) rewrite law-oi<&= th = refl
law-oi<&= (th o') rewrite law-oi<&= th = refl

law-<&=oi oz = refl
law-<&=oi (th os) rewrite law-<&=oi th = refl
law-<&=oi (th o') rewrite law-<&=oi th = refl

law-<&=<&= th ph (ps o') rewrite law-<&=<&= th ph ps = refl
law-<&=<&= th (ph o') (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= (th o') (ph os) (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= (th os) (ph os) (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= oz oz oz = refl
\end{code}
%endif

As one might expect, order-preserving embeddings have a strong
antisymmetry property that one cannot expect of categories in general.
The \emph{only} invertible arrows are the identities.
Note that we must match on the proof of |iz == jz| even to claim
that |th| and |ph| are the identity.
%format antisym = "\F{antisym}"
\begin{spec}
antisym :  (th : iz <= jz)(ph : jz <= iz) -> Sg (iz == jz) \ { refl -> th == oi * ph == oi }
\end{spec}
%if False
\begin{code}
antisym :  forall {K}{iz jz : Bwd K}(th : iz <= jz)(ph : jz <= iz) ->
           Sg (iz == jz) \ { refl -> th == oi * ph == oi }
antisym oz oz = refl , refl , refl
antisym (th os) (ph os) with antisym th ph
antisym (.oi os) (.oi os) | refl , refl , refl = refl , refl , refl
antisym (th os) (ph o') with antisym (th o') ph
antisym (th os) (ph o') | refl , () , c
antisym (th o') (ph os) with antisym th (ph o')
antisym (th o') (ph os) | refl , b , ()
antisym (th o') (ph o') with antisym (oi o' <&= th) (oi o' <&= ph)
antisym (th os o') (ph o') | refl , () , c
antisym (th o' o') (ph o') | refl , () , c
\end{code}
%endif


\section{De Bruijn Syntax via $\OPE$}

%format (Cix (k)) = "\F{\overline{\black{" k "}}}"
%format Cix_ = "\F{\overline{\black{\_}}}"
%format Set1 = Set "_1"
%format <- = "\F{\leftarrow}"
%format _<-_ = _ <- _
%format <> = "\C{\langle\rangle}"
%format LamTm = "\D{Lam}"
%format var = "\C{\scriptstyle\#}"
%format $ = "\C{\scriptstyle\$}"
%format _$_ = _ $ _
%format lam = "\C{\uplambda}"
%format ^L = "\F{\uparrow}"
%format _^L_ = _ ^L _
We often see numbers as de Bruijn indices for
variables~\cite{deBruijn:dummies}, perhaps
with some bound enforced by typing, as shown in principle by Bellegarde and
Hook~\cite{bellegarde.hook:substitution.monad}, and in practice by
Bird and Paterson~\cite{bird.paterson:debruijn.nested}, and (for simple types)
by Altenkirch and Reus~\cite{altenkirch.reus:monads.lambda}. To grow the set
of free variables under a binder, use option types or some
`finite set' construction, often called `Fin'. We can use singleton embedding,
%if False
\begin{code}
Cix_ : Set -> Set1
Cix K = Bwd K -> Set

_<-_ : forall {K} -> K -> (Cix K)
\end{code}
%endif
\begin{code}
k <- kz = B0 - k <= kz
\end{code}
and then
give the well scoped but untyped
de Bruijn $\lambda$-terms, readily seen to admit thinning:
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{3.5in}{
\begin{spec}
data LamTm (iz : Bwd One) : Set where
  var  : (x : <> <- iz)  ->         LamTm iz
  _$_  : (f s : LamTm iz) ->        LamTm iz
  lam  : (t : LamTm (iz - <>)) ->   LamTm iz
\end{spec}}
\parbox[t]{2.5in}{
\begin{spec}
_^L_ : LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
\end{spec}}
%if False
\begin{code}
data LamTm (iz : Bwd One) : Set where          -- |LamTm : (Cix One)|
  var  : (x : <> <- iz)  ->         LamTm iz   -- \emph{finds} a variable
  _$_  : (f s : LamTm iz) ->        LamTm iz   -- associates left
  lam  : (t : LamTm (iz - <>)) ->   LamTm iz   -- \emph{binds} a variable
infixl 5 _$_
\end{code}
%endif

Variables are represented by pointing, eliminating redundant choice of names,
but it is only when we point to one variable that we exclude
the others. Thus de Bruijn indexing
effectively uses thinnings to discard unwanted variables as
\emph{late} as possible, in the \emph{leaves} of syntax trees.

Note how the scope index |iz| is the
target of a thinning in |var| and weakened in |lam|.
Hence, thinnings act on terms ultimately
by postcomposition, but because terms keep their thinnings at their leaves,
we must hunt the entire tree to find them.
Now consider the other canonical placement of
thinnings, nearest the \emph{root}, discarding unused variables
as \emph{early} as possible.
%if False
\begin{code}
_^L_ : forall {iz jz} -> LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
infixl 7 _^L_
\end{code}
%endif


\section{Slices of Thinnings}

If we fix the target of thinnings, |(_<= kz)|, we obtain the notion of
\emph{subscopes} of a given |kz|. Fixing a target is a standard way
to construct a new category whose objects are given by
morphisms of the original.
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{4in}{
\paragraph{Slice Category.~} If
$\mathbb{C}$ is a category and $I$ one of its objects, the \emph{slice category}
$\mathbb{C}/I$ has as its objects pairs $(S, f)$, where $S$ is an object
of $\mathbb{C}$ and $f : S \to I$ is a morphism in $\mathbb{C}$. A morphism
in $(S, f) \to (T, g)$ is some $h : S \to T$ such that $f = h;g$.
(The dotted regions in the diagram show the objects in the slice.)
}
\parbox[t]{2in}{
\[\xymatrix{
  S \ar[rr]^h \ar[dr]_f &   & T \ar[dl]^g \\
    & I \ar@@{.}@@(ul,dl)[ul]\ar@@{.}@@(ul,ur)[ul]
        \ar@@{.}@@(ur,dr)[ur]\ar@@{.}@@(ur,ul)[ur]
        &
}\]}

~

That is, the morphisms are \emph{triangles}. A seasoned dependently typed
programmer will be nervous at a definition like the following
(where the |_| after |Sg| asks Agda to compute the type |iz <= jz| of |th|):
%format ->/ = "\F{\to_{\slash}}"
%format _->/_ = _ ->/ _
\begin{spec}
ps ->/ ph = Sg _ \ th -> (th <&= ph) == ps  -- beware of |<&=|!
\end{spec}
because the equation restricts us when it comes to manipulating
triangles. Dependent pattern matching relies on \emph{unification} of
indices, but defined function symbols like |<&=| make unification
difficult, obliging us to reason about the \emph{edges} of the triangles.
It helps at this point to define the \emph{graph} of |<&=| inductively.
%format Tri = "\D{Tri}"
%format t-'' = "\C{t\mbox{{}-}\apo\!\apo}"
%format t's' = "\C{t\apo\!s\apo}"
%format tsss = "\C{tsss}"
%format _t-'' = _ t-''
%format _t's' = _ t's'
%format _tsss = _ tsss
%format tzzz = "\C{tzzz}"
%format tri = "\F{tri}"
%format comp = "\F{comp}"
\vspace*{ -0.2in}\\
\parbox[t]{3.6in}{
\begin{spec}
data Tri : iz <= jz -> jz <= kz -> iz <= kz -> Set where
  _t-''  : Tri th ph ps ->  Tri    th       (ph o')   (ps  o')
  _t's'  : Tri th ph ps ->  Tri (  th  o')  (ph  os)  (ps  o')
  _tsss  : Tri th ph ps ->  Tri (  th  os)  (ph  os)  (ps  os)
  tzzz   :                  Tri        oz        oz        oz
\end{spec}}
\parbox[t]{2.2in}{
\begin{spec}
tri   :  (th : iz <= jz)(ph : jz <= kz) ->
         Tri th ph (th <&= ph)
         
comp  :  Tri th ph ps -> ps == (th <&= ph)
\end{spec}}
%if False
\begin{code}
data Tri {K} : {iz jz kz : Bwd K} -> iz <= jz -> jz <= kz -> iz <= kz -> Set where
  _t-''  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k}    th      (ph o')  (ps o')
  _t's'  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k} (  th o')  (ph os)  (ps o')
  _tsss  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k} (  th os)  (ph os)  (ps os)
  tzzz   : Tri oz oz oz
infixl 8 _t-'' _t's' _tsss
\end{code}
%endif

\noindent
The indexing is entirely in constructor form, which will allow
easy unification. Moreover, all the \emph{data} in a |Tri| structure
comes from its \emph{indices}.
Easy inductions show that |Tri| is precisely the graph of |<&=|.
%if False
\begin{code}
tri   :  forall {K}{iz jz kz : Bwd K}(th : iz <= jz)(ph : jz <= kz) -> Tri th ph (th <&= ph)
comp  :  forall {K}{iz jz kz : Bwd K}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
           Tri th ph ps -> ps == (th <&= ph)

tri    th       (ph  o')  = (tri th ph)  t-''
tri (  th  o')  (ph  os)  = (tri th ph)  t's'
tri (  th  os)  (ph  os)  = (tri th ph)  tsss
tri        oz        oz   =              tzzz

comp (t  t-'')  rewrite comp t  = refl
comp (t  t's')  rewrite comp t  = refl
comp (t  tsss)  rewrite comp t  = refl
comp     tzzz                   = refl
\end{code}
%endif

The example composition given above can be rendered a triangle, as follows:
%format egTri = "\F{egTri}"
\begin{spec}
egTri : Tri {kz = B0 - k0 - k1 - k2 - k3 - k4} (oz os o' os) (oz os o' os o' os) (oz os o' o' o' os)
egTri = tzzz tsss t-'' t's' t-'' tsss
\end{spec}
%if False
\begin{code}
egTri :  forall {K}{k0 k1 k2 k3 k4 : K} ->  Tri {kz = B0 - k0 - k1 - k2 - k3 - k4}
                                            (oz os o' os) (oz os o' os o' os) (oz os o' o' o' os)
egTri = tzzz tsss t-'' t's' t-'' tsss
\end{code}
%endif

We obtain a definition of morphisms in the slice as triangles.
%if False
\begin{code}
_->/_ :  forall {K}{iz jz kz : Bwd K} -> (iz <= kz) -> (jz <= kz) -> Set
\end{code}
%endif
\begin{code}
ps ->/ ph = Sg _ \ th -> Tri th ph ps
\end{code}

A useful property specific to thinnings is that morphisms in the slice category are \emph{unique}.
It is straightforward to formulate this property in terms of triangles with edges in
common, and then to work by induction on the triangles rather than their edges.
As a result, it will be cheap to establish \emph{universal properties} in the slices of
$\OPE$, asserting the existence of unique morphisms: uniqueness comes for free!
%format triU = "\F{triU}"
\begin{spec}
triU : Tri th ph ps -> Tri th' ph ps -> th == th'
\end{spec}
%if False
\begin{code}
triU :  forall {K}{iz jz kz : Bwd K}{th th' : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
        Tri th ph ps -> Tri th' ph ps -> th == th'
triU (t  t-'')  (t'  t-'')  rewrite triU t t'  = refl
triU (t  t's')  (t'  t's')  rewrite triU t t'  = refl
triU (t  tsss)  (t'  tsss)  rewrite triU t t'  = refl
triU     tzzz        tzzz                      = refl
\end{code}
%endif


\section{Functors, a densely prevalent notion}

Haskell makes considerable use of the type class \texttt{Functor}
and its many subclasses, but this is only to scratch the surface: Haskell's functors
are \emph{endo}functors, mapping the `category' of types-and-functions into itself.
Once we adopt the appropriate level of
generality, functoriality sprouts everywhere, and the same structures
can be usefully functorial in many ways.

\newcommand{\Id}{\textbf{I}}
\paragraph{Functor.~} A \emph{functor} is a mapping from a source
category $\mathbb{C}$ to a target category $\mathbb{D}$ which
preserves categorical structure.  To specify a structure, we must give
a function $F_o : ||\mathbb{C}||\to||\mathbb{D}||$ from source objects
to target objects, together with a family of functions
$F_m : \mathbb{C}(S,T)\to \mathbb{D}(F_o(S),F_o(T))$. The preserved
structure amounts to identity and composition: we must have
that $F_m(\iota_X)=\iota_{F_o(X)}$ and that $F_m(f;g)=F_m(f);F_m(g)$.
Note that there is an identity functor $\Id$ (whose actions on objects
and morphisms are the identity) from $\mathbb{C}$ to itself
and that functors compose (componentwise).

E.g., every |k : K| induces a functor (\emph{weakening}) from $\OPE$ to itself
by scope extension, |(_ - k)| on objects and |os| on
morphisms. The very definitions of |oi| and |<&=| show that |os|
preserves |oi| and |<&=|.
%(I am sufficiently old-fashioned
%and pedantic to distinguish weakening --- adding new variables with
%most local scope --- from thinning --- adding new variables anywhere,
%but this is far from universal.)

Before we can have more examples, we shall need some more
categories. Let |Set| be the category whose objects are Agda types in
the |Set| universe and whose morphisms in $|Set|(S, T)$ are
functions of type $S\to T$, with the usual identity and
composition. Consider morphisms equal if they agree
\emph{pointwise}.
As an exercise, find the action on morphisms of
show the |Set| to |Set| functor which is |Bwd| on objects,
and check that $(|LamTm|,|^L|)$ gives a functor from $\OPE$ to |Set|.

Our work takes us in a different direction, profiting from
the richness of dependent types: let us construct new categories by
\emph{indexing}. If |I : Set|, we may then take |I -> Set| to be the
category whose objects are \emph{families} of objects in |Set|,
$|S|, |T| : |I -> Set|$ with morphisms being the corresponding (implicitly
indexed) families of functions:
%format -:> = "\mathrel{\dot{\to}}"
%format _-:>_ = _ -:> _
%if False
\begin{code}
_-:>_ : {I : Set}(S T : I -> Set) -> Set
\end{code}
%endif
\begin{code}
S -:> T = forall {i} -> S i -> T i
\end{code}

Consider
morphisms equal if they map each index to pointwise equal functions.
We may define a functor from |K -> Set| to |Bwd K -> Set| as follows:
%
%format All = "\D{All}"
%format all = "\F{all}"
%if False
\begin{code}
data  All {K}     (P  : K      -> Set) : Bwd K  -> Set where
  B0   :                                      All P B0
  _-_  : forall {kz k} -> All P kz -> P k ->  All P (kz - k)

all  :   forall {K}{P Q : K -> Set} -> (P -:> Q) -> (All P -:> All Q)
all f B0        = B0
all f (pz - p)  = all f pz - f p
\end{code}
%endif
\vspace*{ -0.2in} \\
\parbox[t]{3.5in}{
\begin{spec}
data  All (P : K -> Set) : Bwd K -> Set where
  B0   :                     All P B0
  _-_  : All P kz -> P k ->  All P (kz - k)
\end{spec}}
\parbox[t]{2.3in}{
\begin{spec}
all : (P -:> Q) -> (All P -:> All Q)
all f B0        = B0
all f (pz - p)  = all f pz - f p
\end{spec}}

For a given |K|, |All| acts on objects, giving for each
|k| in a scope, some value in |P k|, thus giving us a notion of
\emph{environment}. The action on morphisms, |all|, lifts \emph{kind-respecting}
operations on values to \emph{scope-respecting} operations on
environments. Identity and composition are readily
preserved. In the sequel, it will be convenient to abbreviate
|Bwd K -> Set| as |(Cix K)|, for types indexed over scopes.

However, |All| gives more functorial structure.
Fixing |kz|, we obtain |\ P -> All P kz|, a functor
from |K -> Set| to |Set|, again with the instantiated |all| acting on
morphisms.
And still, there is more.

\newcommand{\op}[1]{{#1}^{\textrm{op}}}
\paragraph{Opposite Category.~} For a given category $\mathbb{C}$, its
\emph{opposite} category is denoted $\op{\mathbb{C}}$ and
defined thus:
\[
||\op{\mathbb{C}}|| = ||\mathbb{C}|| \qquad
\op{\mathbb{C}}(S,T) = \mathbb{C}(T,S) \qquad
\op{\iota}_X = \iota_X \qquad
f\op{;}g = g;f
\]
Note that a functor from $\op{\mathbb{C}}$ to $\mathbb{D}$ is sometimes
called a \emph{contravariant functor} from $\mathbb{C}$ to $\mathbb{D}$.
%Moreover, a functor from $\op{\mathbb{C}}$ to |Set| is sometimes called a
%\emph{presheaf} on $\mathbb{C}$. That is, |<?=| makes |All P| a presheaf on
%$\OPE$.

For example, $\op{\OPE}(|jz|,|iz|) = |iz <= jz|$ allows us to see the
category of thinnings as the category of \emph{selections}, where we choose
just |iz| from the available |jz|. If we have an environment for all of the
|jz|, we should be able to whittle it down to an environment for just the
|iz| by throwing away the values we no longer need. That is to say,
|All P| is a \emph{functor} from $\op\OPE$ to |Set|, whose action on
morphisms is
%format <?= = "\F{\le\!?}"
%format _<?=_ = _ <?= _
%format <?=_ = <?= _
\begin{spec}
_<?=_ : iz <= jz -> All P jz -> All P iz
oz       <?= B0        = B0
(th os)  <?= (pz - p)  = (th <?= pz) - p
(th o')  <?= (pz - p)  = th <?= pz
\end{spec}
%if False
\begin{code}
_<?=_ : forall {K P}{jz iz : Bwd K}  -> iz <= jz -> All P jz -> All P iz
oz       <?= B0        = B0
(th os)  <?= (pz - p)  = (th <?= pz) - p
(th o')  <?= (pz - p)  = th <?= pz
\end{code}
%endif
%It is not hard to check that the identity selection (selecting all
%elements) acts as the identity on environments, and that composition
%(making a subselection from a selection) is also respected.


\paragraph{Natural Transformation.~} Given functors $F$ and $G$ from
$\mathbb{C}$ to $\mathbb{D}$, a \emph{natural transformation} is a
family of $\mathbb{D}$-morphisms $k_X \in \mathbb{D}(F_o(X),G_o(X))$
indexed by $\mathbb{C}$-objects, $X\in||\mathbb{C}||$, satisfying the
\emph{naturality} condition, which is that for any $h\in\mathbb{C}(S,T)$, we have
$k_S;G_m(h) = F_m(h);k_T$,
amounting to a kind of \emph{uniformity}. It tells us that $k_X$
does not care what $X$ is, but only about the additional structure
imposed by $F$ and $G$.

Parametric polymorphism famously induces
naturality~\cite{Wadler:1989:TF:99370.99404}, in that ignorance of a
parameter imposes uniformity, and the same is true in our more nuanced
setting. We noted that |\ P -> All P kz| is a functor (with action |all|)
from |K -> Set| to |Set|. Accordingly, if |th : iz <= jz| then
|(th <?=_)|is a natural transformation from |\ P -> All P jz| to
|\ P -> All P iz|, which is as much as to say that the definition of
|<?=| is uniform in |P|, and hence that if |f : {k : K} -> P k -> Q k|, then
|all f (th <?= pz)| = |th <?= all f pz|.


Dependently typed programming thus offers us a much richer seam of
categorical structure than the basic types-and-functions familiar
from Haskell (which demands some negotiation of totality even to
achieve that much). For me, at any rate, this represents an opportunity
to make sense of the categorical taxonomy by relating it to concrete
programming examples, and at the same time, organising those programs
and giving healthy indications for \emph{what to prove}.

%if False
A simple consequence is that only the identity has the same source
and target.
%format law-oi = "\F{law-oi}"
\begin{code}
law-oi : forall {K}{kz : Bwd K}(th : kz <= kz) -> th == oi
law-oi th with antisym th th
law-oi .oi | refl , refl , refl = refl
\end{code}
%endif




\section{Things-with-Thinnings (a Monad)}

%format / = "\D{/}"
%format /_ = / _
%format _/_ = _ / _
%format ^ = "\C{\uparrow}"
%format _^_ = _ ^ _
%format support = "\F{support}"
%format thing = "\F{thing}"
%format thinning = "\F{thinning}"
%format map/ = "\F{map/}"

Let us develop the habit of packing terms with an
object in the slice category of thinnings,
selecting the
|support| of the term and discarding unused variables
at the root.
Note that |/| is a functor from |(Cix K)| to itself.
\begin{code}
record _/_ {K}(T : (Cix K))(scope : Bwd K) : Set where -- |(T /_) : (Cix K)|
  constructor _^_
  field {support} : Bwd K; thing : T support; thinning : support <= scope

map/ :  forall {K}{S T : (Cix K)} -> (S -:> T) -> ((S /_) -:> (T /_))
map/ f (s ^ th) = f s ^ th
\end{code}
%if False
\begin{code}
infixl 7 _^_
open _/_
\end{code}
%endif

In fact, the categorical structure of $\OPE$ makes |/| a \emph{monad}.
Let us recall the definition.

\paragraph{Monad.~} A functor $M$ from $\mathbb{C}$ to $\mathbb{C}$ gives
rise to a \emph{monad} $(M,\eta,\mu)$ if we can find a pair of natural
transformations, respectively `unit' (`add an $M$ layer') and `multiplication'
(`merge $M$ layers').
\[
\eta_X : \Id(X) \to M(X)
\qquad\qquad
\mu_X : M(M(X)) \to M(X)
\]
subject
to the conditions that merging an added layer yields the identity
(whether the layer added is `outer' or `inner'), and that
adjacent $M$ layers may be merged pairwise in any order.
\[
  \eta_{M(X)};\mu_X = \iota_{M(X)} \qquad\qquad
  M(\eta_X);\mu_X = \iota_{M(X)} \qquad\qquad
  \mu_{M(X)};\mu_X = M(\mu_X);\mu_X
\]

%format unit/ = "\F{unit/}"
%format mult/ = "\F{mult/}"
%format thin/ = "\F{thin/}"
The categorical structure of thinnings makes |/| a monad. Here,
`adding a layer' amounts to `wrapping with a
thinning'. The proof obligations to make $(|/|,|unit/|,|mult/|)$ a monad are
exactly those required to make $\OPE$ a category in the first place.
In particular, things-with-thinnings are easy to thin further, indeed,
parametrically so. In other words, |(T /)| is uniformly a functor from
$\OPE$ to |Set|.
\\
\parbox{1.5in}{
\begin{spec}
unit/ : T -:> (T /_)
unit/ t = t ^ oi
\end{spec}}
\parbox{2.3in}{
\begin{spec}
mult/ : ((T /_) /_) -:> (T /_)
mult/ ((t ^ th) ^ ph) = t ^ (th <&= ph)
\end{spec}}
\parbox{2.2in}{
\begin{spec}
thin/ : iz <= jz -> T / iz -> T / jz
thin/ th t = mult/ (t ^ th)
\end{spec}}
\\

%if False
\begin{code}
unit/ : forall {K}{T : (Cix K)} -> T -:> (T /_)
unit/ t = t ^ oi
mult/ : forall {K}{T : (Cix K)} -> ((T /_) /_) -:> (T /_)
mult/ ((t ^ th) ^ ph) = t ^ (th <&= ph)
thin/ : forall {K T}{iz jz : Bwd K} -> iz <= jz -> T / iz -> T / jz
thin/ th t = mult/ (t ^ th)
\end{code}
%endif

\newcommand{\Kleisli}[1]{\textbf{Kleisli}(#1)}
%\paragraph{Kleisli Category.~} Every monad $(M,\eta,\mu)$ on
%$\mathbb{C}$ induces a category $\Kleisli(M,\eta,\mu)$ with
%\[
%||\Kleisli{M,\eta,\mu}|| = ||\mathbb{C}|| \qquad
%\Kleisli{M,\eta,\mu}(S,T) = \mathbb{C}(S,M(T)) \qquad
%\iota^{\textbf{K}}_X = \eta_X \qquad
%f;^{\textbf{K}}g = f;M(g);\mu
%\]
%We sometimes call the morphisms in a Kleisli category \emph{Kleisli arrows}.
%
%The Kleisli arrows for |/| are operations with types such as |S -:> (T /_)|
%which \emph{discover dependency}: they turn an |S| over any scope |kz|
%into a |T| known to depend on at most some of the |kz|.

Shortly, we shall give
%exactly such
an operation to discover the
variables in scope on which a term syntactically depends. However,
merely \emph{allowing} a thinning at the root, |LamTm / iz|, yields a poor
representation of terms over |iz|, as we may choose whether to discard
unwanted variables either at root or at leaves. To eliminate redundancy,
we must \emph{insist} that a term's
|support| is \emph{relevant}: if a variable is not discarded by the
|thinning|, it \emph{must} be used in the |thing|. Or as Spike
Milligan put it, `Everybody's got to be somewhere.'.


\section{The Curious Case of the Coproduct in  Slices of $\OPE$}

The |/| construction makes crucial use of objects
in the slice category $\OPE/|scope|$, which exhibit useful additional
structure: they are \emph{bit vectors},
with one bit per variable telling whether it has been selected.
Bit vectors inherit Boolean structure, via the
`Naperian' array structure of vectors~\cite{DBLP:conf/esop/Gibbons17}.

\paragraph{Initial object.~} A category $\mathbb{C}$ has initial object
$0$, if there is a unique morphism in $\mathbb{C}(0,X)$ for every $X$.

We are used to the \emph{empty type} playing this r\^ole for
types-and-functions: empty case analysis gives
the vacuously unique morphism. In $\OPE$, the
empty \emph{scope} plays the same r\^ole, with the
`constant 0' bit vector as unique morphism.
By return of post, we obtain that $(|B0|,|oe|)$ is the initial object in the
slice category |_ <= kz|.%format oe = "\F{oe}"
%format law-oe = "\F{law-}" oe
%format oe/ = oe "\F{\slash}"
%
\vspace*{ -0.2in} \\
\parbox[t]{2.9in}{
\begin{code}
oe : forall {K}{kz : Bwd K} -> B0 <= kz
oe {kz = iz - k}  = oe o'
oe {kz = B0}      = oz
\end{code}
\vspace*{ -0.4in}
\begin{spec}
law-oe :  (th : B0 <= kz) -> th == oe
\end{spec}}
\parbox[t]{2.8in}{
\begin{spec}
oe/ : (th : iz <= kz) -> oe ->/ th
oe/ th with tri oe th
... | t rewrite law-oe (oe <&= th) = oe , t
\end{spec}}
%if False
\begin{code}
law-oe :  forall {K}{kz : Bwd K}
          (th : B0 <= kz) -> th == oe
law-oe oz = refl
law-oe (th o') rewrite law-oe th = refl
\end{code}
\begin{code}
oe/ : forall {K}{iz kz : Bwd K}(th : iz <= kz) -> oe ->/ th
oe/ th with tri oe th
... | t rewrite law-oe (oe <&= th) = oe , t
\end{code}
%endif

We can now make \emph{constants} with empty support,
i.e., noting that no variable is ($\cdot_R$ for) \emph{relevant}.
%format OneR = One "_{R}"
%format <>R = "\F{\langle\rangle}_{R}"
\vspace*{ -0.2in} \\
\parbox[t]{3in}{
\begin{code}
data OneR {K} : (Cix K) where  <> : OneR B0
\end{code}}
\parbox[t]{2in}{
\begin{spec}
<>R : OneR / kz
<>R = <> ^ oe
\end{spec}}
%if False
\begin{code}
<>R : forall {K}{kz : Bwd K} -> OneR / kz
<>R = <> ^ oe
\end{code}
%endif

%In other words, we have found a \emph{terminal} object, namely
%|(OneR /_)|, in |Bwd K -> Set|.

%\paragraph{Terminal object.~} A category $\mathbb{C}$ has terminal object
%$1$, if there is a unique morphism in $\mathbb{C}(X,1)$ for every $X$.

%format *R = "\D{\times}_R"
%format _*R_ = _ *R _
%format ,R = "\F{,}_{R}"
%format _,R_ = _ ,R _
We should expect the constant to be the trivial case of some notion
of \emph{relevant pairing}, induced by \emph{coproducts} in the slice category.
If we have two objects in |(_ <= kz)| representing two subscopes, there should
be a smallest subscope which includes both: pairwise disjunction
of bit vectors.

\paragraph{Coproduct.~} Objects $S$ and $T$ of category $\mathbb{C}$ have
a coproduct object $S + T$ if there are morphisms $l\in \mathbb{C}(S, S + T)$ and
$r\in \mathbb{C}(T, S + T)$ such that every pair
$f\in \mathbb{C}(S, U)$ and $g\in \mathbb{C}(T, U)$ factors
through a unique $h\in \mathbb{C}(S + T, U)$ so that
$f = l;h$ and $g = r;h$. In |Set|, we may take $S + T$ to be
the \emph{disjoint union} of $S$ and $T$, with $l$ and $r$ its injections
and $h$ the \emph{case analysis} whose branches are $f$ and $g$.

However, we are not working in |Set|, but in a slice category.
Any category theorist will tell you that slice categories $\mathbb{C}/I$
inherit \emph{colimit} structure (characterized by universal out-arrows)
from $\mathbb{C}$, as indeed we just saw with the initial object. If $\OPE$
has coproducts, too, we are done!

Curiously, though, $\OPE$ does \emph{not} have coproducts. Taking |K = One|,
let us seek the coproduct of two singletons, $S = T = |B0 - <>|$.
Construct one diagram by taking $U = |B0 - <>|$ and $f = g = |oi|$,
ensuring that our only candidate for $S + T$ is again the
singleton |B0 - <>|, with $l = r = |oi|$, making $h = |oi|$.
Nothing else can sit between $S, T$ and $U$.
Now begin a different diagram, with $U' = |B0 - <> - <>|$,
allowing $f' = |oz os o'|$ and $g' = |oz o' os|$. No $h'$
post-composes $l$ and $r$ (both |oi|, making $h'$ itself)
to yield $f'$ and $g'$ respectively.

Fortunately, we shall get what we need. $\OPE$ may not have coproducts, but its
\emph{slices} do.
%It is not the case that colimit structure in $\mathbb{C}/I$
%arises \emph{only} via inheritance from $\mathbb{C}$.
%format Cover = "\D{Cover}"
%format c's = "\C{c\apo s}"
%format cs' = "\C{cs\apo}"
%format css = "\C{css}"
%format _c's = _ c's
%format _cs' = _ cs'
%format _css = _ css
%format czz = "\C{czz}"
Examine the data.
We have two subscopes of some |kz|, |th : iz <= kz| and |ph : jz <= kz|. Their
coproduct must be some |ps : ijz <= kz|, where our $l$ and $r$ must be
triangles |Tri th' ps th| and |Tri ph' ps ph|, giving us morphisms in
|th ->/ ps| and |ph ->/ ps|, respectively. Intuitively, we should choose |ps|
to be the pointwise disjunction of |th| and |ph|, so that |ijz| is as small
as possible: |th'| and |ph'| will then \emph{cover} |ijz|. The flag, |ov|,
determines whether \emph{overlap} is permitted: this should be |tt| for
coproducts, but |ov = ff| allows the notion of \emph{partition}, too.
\begin{spec}
data Cover {K}(ov : Two) : {iz jz ijz : Bwd K} -> iz <= ijz -> jz <= ijz -> Set where
  _c's  : Cover ov th ph ->  Cover ov (th  o')  (ph  os)
  _cs'  : Cover ov th ph ->  Cover ov (th  os)  (ph  o')
  _css  : Cover ov th ph ->  Cover ov (th  os)  (ph  os)
  czz   :                    Cover ov      oz        oz
\end{spec}
%if False
\begin{code}
data Cover {K}(ov : Two) : {iz jz ijz : Bwd K} -> iz <= ijz -> jz <= ijz -> Set where
  _c's  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th o')  (ph os)
  _cs'  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th os)  (ph o')
  _css  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz}{both : Tt ov} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th os)  (ph os)
  czz   : Cover ov oz oz
infixl 8 _c's _cs' _css
\end{code}
%endif
Note that we have no constructor which allows both |th| and |ph| to
omit a target variable: everybody's got to be somewhere. Let us compute
the coproduct, then check its universal property.
%format cop = "\F{cop}"
\vspace*{ -0.2in} \\
%\noindent
\parbox{4in}{
\begin{code}
cop :  forall {K}{kz iz jz : Bwd K}
       (th : iz <= kz)(ph : jz <= kz) ->
       Sg _ \ ijz -> Sg (ijz <= kz) \ ps ->
       Sg (iz <= ijz) \ th' -> Sg (jz <= ijz) \ ph' ->
       Tri th' ps th * Cover tt th' ph' * Tri ph' ps ph
\end{code}}
\parbox{2in}{
\[\xymatrix{
 |iz| \ar[rrrd]^{|th|} \ar@@{.>}[rd]_{|th'|} &&& \\
 &  |ijz| \ar@@{.>}[rr]^{|ps|}  && |kz| \\ 
 |jz| \ar[rrru]_{|ph|} \ar@@{.>}[ru]^{|ph'|} &&& \\
}\]}
\vspace*{ -0.2in}
\begin{code}
cop (th  o') (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t-''  , c       , tr  t-''
cop (th  o') (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t's'  , c  c's  , tr  tsss
cop (th  os) (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  cs'  , tr  t's'
cop (th  os) (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  css  , tr  tsss
cop      oz       oz   =                                         ! ! ! !     tzzz  ,    czz  ,     tzzz
\end{code}
To show that we have really computed a coproduct, we must show
that any other pair of triangles from |th| and |ph| to
some |ps'| must induce a (unique) morphism from |ps| to |ps'|.
%format copU = "\F{copU}"
\begin{spec}
copU :  Tri th' ps th -> Cover tt th' ph' -> Tri ph' ps ph ->
        forall {ijz'}{ps' : ijz' <= kz} -> th ->/ ps' -> ph ->/ ps' -> ps ->/ ps'
\end{spec}
The construction goes by induction on the triangles which share |ps'|
and inversion of the coproduct.
%if False
\begin{code}
copU :  forall {K}{kz iz jz ijz : Bwd K}
        {th : iz <= kz}{ph : jz <= kz}{ps : ijz <= kz}{th' : iz <= ijz}{ph' : jz <= ijz}->
        Tri th' ps th -> Cover tt th' ph' -> Tri ph' ps ph ->
        forall {ijz'}{ps' : ijz' <= kz} -> th ->/ ps' -> ph ->/ ps' -> ps ->/ ps'
copU (tl t-'') c (tr t-'') (_ , ul t-'') (_ , ur t-'') with copU tl c tr (! ul) (! ur)
... | ! v = ! v t-''
copU (tl t's') () (tr t's') (! ul t-'') (! ur t-'')
copU (tl t-'') c (tr t-'') (! ul t's') (! ur t's') with copU tl c tr (! ul) (! ur)
... | ! v = ! v t's'
copU (tl t's') () (tr t's') (! ul t's') (! ur t's')
copU (tl t's') (c c's) (tr tsss) (! ul t's') (! ur tsss) with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU (tl tsss) (c cs') (tr t's') (! ul tsss) (! ur t's') with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU (tl tsss) (c css) (tr tsss) (! ul tsss) (! ur tsss) with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU tzzz czz tzzz (_ , tzzz) (_ , tzzz) = ! tzzz
\end{code}
%endif
%
The payoff from the coproduct construction is the type of \emph{relevant pairs} ---
the co-de-Bruijn touchstone:
%format *R = "\D{\times}_R"
%format _*R_ = _ *R _
%format ,R = "\C{,}_R"
%format _,R_ = _ ,R _
%format pair = "\C{pair}"
%format outl = "\F{outl}"
%format outr = "\F{outr}"
%format cover = "\F{cover}"
\vspace*{ -0.2in} \\
\parbox[t]{3.4in}{
\begin{spec}
record _*R_ (S T : (Cix K))(ijz : Bwd K) : Set where
  constructor pair
  field  outl   : S / ijz
         outr   : T / ijz
         cover  : Cover tt (thinning outl) (thinning outr)
\end{spec}}
\parbox[t]{2in}{
\begin{spec}
_,R_ : S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) =
  let  ! ps , th' , ph' , _ , c , _ = cop th ph
  in   pair (s ^ th') (t ^ ph') c ^ ps
\end{spec}}

%if False
\begin{code}
record _*R_ {K}(S T : (Cix K))(ijz : Bwd K) : Set where
  constructor pair
  field  outl   : S / ijz
         outr   : T / ijz
         cover  : Cover tt (thinning outl) (thinning outr)

_,R_ : forall {K}{S T : (Cix K)}{kz} -> S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) =
  let  ! ps , th' , ph' , _ , c , _ = cop th ph
  in   pair (s ^ th') (t ^ ph') c ^ ps
\end{code}
%endif

\section{Monoidal Structure of Order-Preserving Embeddings}

To talk about binding, we need scope extension.
We have seen single `snoc', but binding is simultaneous in general.
Concatenation induces monoidal structure on
objects of $\OPE$, extending to morphisms.
%format ++ = "\F{+\!\!+}"
%format _++_ = _ ++ _
%format <++= = ++ "_{" <= "}"
%format _<++=_ = _ <++= _
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.4in}{
\begin{spec}
_++_ : (iz jz : Bwd K) -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
\end{spec}}
%if False
\begin{code}
_++_ : forall {K}(kz jz : Bwd K) -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
infixl 7 _++_
_<++=_ :  forall {K}{iz jz iz' jz' : Bwd K} ->
  iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
\end{code}
%endif
\parbox[t]{3in}{
\begin{spec}
_<++=_ :  iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
\end{spec}}

Moreover, given a embedding into a concatenation, we can split it
into local and global parts.
%format -! = "\F{\dashv}"
%format _-!_ = _ -! _
\begin{spec}
_-!_ :  (jz : Bwd K)(ps : iz <= (kz ++ jz)) -> Sg (Bwd K) \ kz' -> Sg (Bwd K) \ jz' ->
  Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph -> Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps                                               = ! ! ps , oz , refl , refl
(kz - k)  -! (ps os)             with kz -! ps
(kz - k)  -! (.(th <++= ph) os)  | ! ! th , ph , refl , refl  = ! ! th , ph os , refl , refl
(kz - k)  -! (ps o')             with kz -! ps
(kz - k)  -! (.(th <++= ph) o')  | ! ! th , ph , refl , refl  = ! ! th , ph o' , refl , refl
\end{spec}
%if False
\begin{code}
_-!_ : forall {K}{iz kz}(jz : Bwd K)(ps : iz <= (kz ++ jz)) ->
       Sg _ \ kz' -> Sg _ \ jz' -> Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph ->
       Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps                                               = ! ! ps , oz , refl , refl
(kz - k)  -! (ps os)             with kz -! ps
(kz - k)  -! (.(th <++= ph) os)  | ! ! th , ph , refl , refl  = ! ! th , ph os , refl , refl
(kz - k)  -! (ps o')             with kz -! ps
(kz - k)  -! (.(th <++= ph) o')  | ! ! th , ph , refl , refl  = ! ! th , ph o' , refl , refl
\end{code}
%endif

Thus equipped, we can say how to bind some variables. The key is to say
at the binding site which of the bound variables will actually be used:
if they are not used, we should not even bring them into scope.

%format !- = "\D{\vdash}"
%format _!-_ = _ !- _
%format \\ = "\C{\fatbslash}"
%format _\\_ = _ \\ _
%format \\R = "\F{\fatbslash}_R"
%format _\\R_ = _ \\R _
\begin{code}
data _!-_ {K}(jz : Bwd K)(T : (Cix K))(kz : Bwd K) : Set where -- |jz !- T : (Cix K)|
  _\\_ : forall {iz} -> iz <= jz -> T (kz ++ iz) -> (jz !- T) kz

_\\R_ : forall {K T}{kz}(jz : Bwd K) -> T / (kz ++ jz) -> (jz !- T) / kz
jz \\R (t ^ ps) with jz -! ps
jz \\R (t ^ .(th <++= ph)) | ! ! th , ph , refl , refl = (ph \\ t) ^ th
\end{code}

%if False
\begin{code}
infixr 5 _!-_
infixr 6 _\\_
infixr 6 _\\R_
\end{code}
%endif

The monoid of scopes is generated from its singletons. By the time we \emph{use}
a variable, it should be the only thing in scope.
The associated smart constructor computes the thinned representation of variables.
%format VaR = "\D{Va}_R"
%format only = "\C{only}"
%format vaR = "\F{va}_R"
\vspace*{ -0.2in} \\
\parbox[t]{2.5in}{
\begin{spec}
data VaR (k : K) : (Cix K) where
  only : VaR k (B0 - k)
\end{spec}}
\parbox[t]{2.5in}{
\begin{spec}
vaR : k <- kz -> VaR k / kz
vaR x = only ^ x
\end{spec}}
%if False
\begin{code}
data VaR {K}(k : K) : (Cix K) where only : VaR k (B0 - k)

vaR : forall {K}{k}{kz : Bwd K} -> k <- kz -> VaR k / kz
vaR x = only ^ x
\end{code}
%endif

\vspace*{- 0.2in}
%format combK = "\F{\mathbb{K}}"
%format combS = "\F{\mathbb{S}}"
\paragraph{Untyped $\lambda$-calculus.~}
We can now give the $\lambda$-terms for which all \emph{free} variables are
relevant as follows.
Converting de Bruijn to co-de-Bruijn representation is easy with
smart constructors.
E.g., compare de Bruijn terms for the |combK| and |combS| combinators with their co-de-Bruijn form.
%format lamTmR = "\F{lam}_R"
%format LamTmR = LamTm "_R"
%format app = "\C{app}"
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
data LamTmR : (Cix One) where
  var  : VaR <>               -:>  LamTmR
  app  : (LamTmR *R LamTmR)   -:>  LamTmR
  lam  : (B0 - <> !- LamTmR)  -:>  LamTmR 
\end{code}}
\parbox[t]{3in}{
\begin{code}
lamTmR : LamTm -:> (LamTmR /_)
lamTmR (var x)  = map/ var  (vaR x)
lamTmR (f $ s)  = map/ app  (lamTmR f ,R lamTmR s)
lamTmR (lam t)  = map/ lam  (_ \\R lamTmR t) 
\end{code}}
\vspace*{ -0.2in}
\begin{spec}
combK         =  lam (lam (var (oe os o')))
lamTmR combK  =  lam (oz os \\ lam (oz o' \\ var only)) ^ oz

combS         =  lam (lam (lam (var (oe os o' o') $ var (oe os) $ (var (oe os o') $ var (oe os)))))
lamTmR combS  =  lam (oz os \\ lam (oz os \\ lam (oz os \\
  app (pair  (app  (pair (var only ^ oz os o') (var only ^ oz o' os) (czz cs' c's))  ^ oz os o' os)
             (app  (pair (var only ^ oz os o') (var only ^ oz o' os) (czz cs' c's))  ^ oz o' os os)
             (czz cs' c's css)) ))) ^ oz
\end{spec}
Staring bravely, we see that |combK| uses its first argument
to deliver a plainly constant function: the second |lam|
discards its argument. Meanwhile,
|combS| clearly uses all three inputs (`function', `argument',
`environment'): in the application, the function goes
left, the argument goes right, and the environment is shared.


\section{A Universe of Metasyntaxes-with-Binding}

%format Kind = "\D{Kind}"
%format Scope = "\F{Scope}"
%format => = "\C{\Rightarrow}"
%format _=>_ = _ => _
%format scope = "\F{scope}"
%format sort = "\F{sort}"
There is nothing specific to the $\lambda$-calculus about de Bruijn
representation or its co-de-Bruijn counterpart. We may develop the
notions generically for multisorted syntaxes. If the sorts of our
syntax are drawn from set $I$, then we may characterize terms-with-binding
as inhabiting |Kind|s |kz => i|, which specify an extension of the scope
with new bindings |kz| and the sort |i| for the body of the binder.
\begin{code}
record Kind (I : Set) : Set where  inductive; constructor _=>_
                                   field scope : Bwd (Kind I); sort : I
\end{code}
%if False
\begin{code}
infix 6 _=>_
open Kind
\end{code}
%endif
|Kind|s offer higher-order abstraction: a bound variable itself
has a |Kind|, being an object sort parametrized by a scope,
where the latter is, as in previous  sections, a |Bwd| list, with |K| now
fixed as |Kind I|. Object variables have sorts; \emph{meta}-variables have |Kind|s.
E.g., in the $\beta$-rule, $t$ and $s$ are not object variables like $x$
\[
  (\lambda x.\,t[x])\:s \;\leadsto\; t[s]
\]
but
placeholders, $s$ for some term and $t[x]$ for some term
with a parameter which can be and is instantiated, by $x$
on the left and $s$ on the right. The kind of $t$ is |B0 - (B0 => <>) => <>|.

%format Desc = "\D{Desc}"
%format Set1 = Set "_1"
%format RecD = "\C{Rec}_D"
%format SgD = "\C{\Upsigma}_D"
%format OneD = "\C{One}_D"
%format *D = "\C{\times}_D"
%format _*D_ = _ *D _
%format Datoid = "\D{Datoid}"
%format Data = "\F{Data}"
%format decide = "\F{decide}"
%format Zero = "\D{Zero}"
%format Decide = "\D{Decide}"
%format yes = "\C{yes}"
%format no = "\C{no}"
We may give the syntax of each sort as a function mapping sorts to
|Desc|riptions
|D : I -> Desc I|.
\begin{spec}
data Desc (I : Set) : Set1 where
  RecD   : Kind I ->                              Desc I
  OneD   :                                        Desc I
  _*D_   : Desc I -> Desc I ->                    Desc I
  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
\end{spec}
We may ask for a subterm with a given |Kind|, so it can bind
variables by listing their |Kind|s left of |=>|. Descriptions
are closed under unit and pairing.
We may also ask
for terms to be tagged by some sort of `constructor' inhabiting
some |Datoid|, i.e., a set with a decidable equality, given
as follows:
\vspace*{ -0.2in}\\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
data Decide (X : Set) : Set where
  yes  : X ->            Decide X
  no   : (X -> Zero) ->  Decide X
\end{code}}
\parbox[t]{3in}{
\begin{code}
record Datoid : Set1 where
  field  Data    : Set
         decide  : (x y : Data) -> Decide (x == y)
\end{code}}
%if False
\begin{code}
open Datoid

data Desc (I : Set) : Set1 where
  RecD   : Kind I ->                              Desc I
  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
  OneD   :                                        Desc I
  _*D_   : Desc I -> Desc I ->                    Desc I
\end{code}
%endif

\paragraph{Describing untyped $\lambda$-calculus.~} Define a tag enumeration, then a description.
%format LamTag = "\D{LamTag}"
%format LAMTAG = "\F{LAMTAG}"
%format LamD = "\F{Lam}_D"
\vspace*{ -0.2in} \\
\parbox[t]{3in}{
\begin{code}
data LamTag : Set where app lam : LamTag

LAMTAG : Datoid
Data    LAMTAG = LamTag
\end{code}}
\parbox[t]{2.5in}{
\begin{code}
decide  LAMTAG app  app  = yes refl
decide  LAMTAG app  lam  = no \ ()
decide  LAMTAG lam  app  = no \ ()
decide  LAMTAG lam  lam  = yes refl
\end{code}}
\vspace*{ -0.2in}
\begin{code}
LamD : One -> Desc One
LamD <> = SgD LAMTAG \  { app  -> RecD (B0 => <>) *D RecD (B0 => <>)
                        ; lam  -> RecD (B0 - (B0 => <>) => <>) }
\end{code}
Note that we do not and cannot include a tag or description for
the use sites of variables in terms: use of variables in scope
pertains not to the specific syntax, but to the general notion
of what it is to be a syntax.

\paragraph{Interpreting |Desc| as de Bruijn Syntax.~}
%format [! = "\F{\llbracket}"
%format !! = "\F{\mid}"
%format !] = "\F{\rrbracket}"
%format [!_!!_!] = [! _ !! _ !]
%format SpD = "\F{Sp}_D"
Let us give the de Bruijn interpretation of our syntax descriptions.
We give meaning to |Desc| in the traditional manner, interpreting
them as strictly positive operators in some |R| which gives the semantics
to |RecD|. In recursive positions, the scope grows by the bindings demanded by the given |Kind|.
At use sites, higher-kinded variables must be instantiated, just
like $t[x]$ in the $\beta$-rule example: |SpD| computes
the |Desc|ription of the
spine of actual parameters required.
\vspace*{ -0.2in} \\
\parbox[t]{3.7in}{
\begin{code}
[!_!!_!] : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD k   !! R !] kz = R (sort k) (kz ++ scope k)
[! SgD S T  !! R !] kz = Sg (Data S) \ s -> [! T s !! R !] kz
[! OneD     !! R !] kz = One
[! S *D T   !! R !] kz = [! S !! R !] kz * [! T !! R !] kz
\end{code}}
\parbox[t]{2in}{
\begin{spec}
SpD : Bwd (Kind I) -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
\end{spec}}
%Note that we work with scope-indexed sets and an index |kz| giving the
%kinds of the variables in scope. 

%if False
\begin{code}
SpD : forall {I} -> Bwd (Kind I) -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
\end{code}
%endif

Tying the knot, we find that a term is either a variable instantiated
with its spine of actual parameters, or it is a construct of the syntax
for the demanded sort, with subterms in recursive positions.
%format Tm = "\D{Tm}"
%format #$ = "\C{\scriptstyle \#\$}"
%format _#$_ = _ #$ _
%format [ = "\C{[}"
%format ] = "\C{]}"
%format [_] = [ _ ]
\begin{code}
data Tm {I}(D : I -> Desc I)(i : I) kz : Set where -- |Tm D i : (Cix (Kind I))|
  _#$_  : forall {jz} -> (jz => i) <- kz ->  [! SpD jz  !! Tm D !] kz ->  Tm D i kz
  [_]   :                                    [! D i     !! Tm D !] kz ->  Tm D i kz
\end{code}
%if False
\begin{code}
infixr 5 _#$_
\end{code}
%endif

%if False
In this setting, |combK| and |combS| become
%format combKD = combK "_D"
%format combSD = combS "_D"
\begin{spec}
combKD combSD : Tm LamD <> B0
combKD  =  [ lam ,  [ lam , oe os o' #$ <> ] ]
combSD  =  [ lam ,  [ lam ,  [ lam ,  [ app  , [ app , oe os o' o' #$ <> , oe os #$ <> ]
                                             , [ app , oe os o' #$ <> , oe os #$ <> ]
           ]        ]        ]        ]
\end{spec}
%endif

\vspace*{- 0.2in}
%format code = "\F{code}"
%format codes = "\F{codes}"
\paragraph{Interpreting |Desc| as co-de-Bruijn Syntax.~}
Now let us interpret |Desc|riptions in co-de-Bruijn style,
enforcing that all variables in scope are relevant, and that
binding sites expose vacuity. We can compute co-de-Bruijn terms from de Bruijn terms, generically.
%format !]R = "\F{\rrbracket}_R"
%format [!_!!_!]R = [! _ !! _ !]R
%format TmR = Tm "_R"
%format # = "\C{\scriptstyle \#}"
\begin{code}
[!_!!_!]R : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD k   !! R !]R = scope k !- R (sort k)
[! SgD S T  !! R !]R = \ kz -> Sg (Data S) \ s -> [! T s !! R !]R kz
[! OneD     !! R !]R = OneR
[! S *D T   !! R !]R = [! S !! R !]R *R [! T !! R !]R

data TmR {I}(D : I -> Desc I)(i : I) : (Cix (Kind I)) where
  #     : forall {jz} -> (VaR (jz => i) *R  [! SpD jz  !! TmR D !]R)  -:>  TmR D i
  [_]   :                                   [! D i     !! TmR D !]R   -:>  TmR D i

code   : forall {I}{D : I -> Desc I}{i}  ->  Tm D i           -:>  (TmR D i /_)
codes  : forall {I}{D : I -> Desc I} S   ->  [! S !! Tm D !]  -:>  ([! S !! TmR D !]R /_)
code                    (_#$_ {jz} x ts)  = map/ #    (vaR x ,R codes (SpD jz) ts)
code {D = D}{i = i}     [ ts ]            = map/ [_]  (codes (D i) ts)
codes (RecD k)          t                 = scope k \\R code t
codes (SgD S T)         (s , ts)          = map/ (s ,_) (codes (T s) ts)
codes OneD              <>                = <>R
codes (S *D T)          (ss , ts)         = codes S ss ,R codes T ts
\end{code}


\section{Hereditary Substitution for Co-de-Bruijn Metasyntax}

%format Im = "\F{Im}"
%format KB = "\F{KB}"
%format HSub = "\D{HSub}"
%format pass = "\F{pass}"
%format act = "\F{act}"
%format passive = "\F{passive}"
%format active = "\F{active}"
%format parti = "\F{parti}"
%format actBnd = "\F{actBnd}"
%format passTrg = "\F{passTrg}"
%format images = "\F{images}"

Let us develop the appropriate notion of substitution for our metasyntax, \emph{hereditary}
in the sense of Watkins et al.~\cite{DBLP:conf/types/WatkinsCPW03}. Substituting a higher-kinded
variable requires us further to substitute its parameters.

There is some subtlety to the construction of the record type |HSub| of hereditary substitutions.
We may |parti|tion the source scope into |passive| variables, which embed into the target,
and |active| variables for which we have an environment |images| appropriate to their kinds.
The |HSub| type is indexed by a third scope which bounds the active kinds, by way of
ensuring \emph{termination}.
\begin{code}
record HSub {I} D (src trg bnd : Bwd (Kind I)) : Set where
  field  pass act   : Bwd (Kind I)             ; passive  : pass  <= src  ; active  : act <= src
         parti  : Cover ff passive active  ; passTrg  : pass  <= trg  ; actBnd  : act <= bnd
         images     : All (\ k -> (scope k !- TmR D (sort k)) / trg) act
\end{code}

%if False
\begin{code}
open HSub
\end{code}
%endif

Before we see how to perform a substitution, let us consider how to \emph{weaken} one, as we
shall certainly need to push under binders, where we have some |ph : iz <= jz| telling us
which |iz| of the |jz| bound variables are used in the source term. Either way,
bound variables are not substituted, so we add them to the passive
side, at the same time keeping the active side below its bound.
%format wkHSub = "\F{wkHSub}"
%format bindPassive = "\F{bindPassive}"
\begin{spec}
wkHSub :  HSub D src trg bnd -> iz <= jz -> HSub D (src ++ iz) (trg ++ jz) bnd
wkHSub {iz = iz}{jz = jz} h ph = record
  { parti = bindPassive iz ; actBnd = actBnd h ; passTrg = passTrg h <++= ph
  ; images = all (thin/ (oi <++= oe {kz = jz})) (images h) } where
  bindPassive : forall iz -> Cover ff (passive h <++= oi {kz = iz}) (active h <++= oe {kz = iz})
\end{spec}
As in a de Bruijn substitution, we must thin all the images, but the
co-de-Bruijn representation avoids any need to traverse them --- just compose thinnings
at the root.

%format selPart = "\F{selPart}"
%format selHSub = "\F{selHSub}"
%format ps0 = "\V{\psi_0}"
%format ps1 = "\V{\psi_1}"
A second ancillary operation on |HSub| is to cut them down to just what is needed as
variables are expelled from the source context by the thinnings stored in relevant pairs.
We may select from an environment, but we must also refine the partition to cover just
those source variables which remain, hence the |selPart| operation, which is a
straightforward induction.
%if False
\begin{code}
wkHSub :  forall {I}{D : I -> Desc I}{src trg bnd iz jz} ->
          HSub D src trg bnd -> iz <= jz -> HSub D (src ++ iz) (trg ++ jz) bnd
wkHSub {iz = iz}{jz = jz} h ph = record
  { parti = bindPassive iz ; actBnd = actBnd h ; passTrg = passTrg h <++= ph
  ; images = all (thin/ (oi <++= oe {kz = jz})) (images h) } where
  bindPassive : forall iz -> Cover ff (passive h <++= oi {kz = iz}) (active h <++= oe {kz = iz})
  bindPassive B0       = parti h
  bindPassive (iz - _) = bindPassive iz cs'
\end{code}

\begin{code}
mutual
\end{code}
%endif
\begin{spec}
  selHSub :  src <= src' -> HSub D src' trg bnd -> HSub D src trg bnd
  selHSub ps (record { parti = c' ; actBnd = th' ; images = tz' ; passTrg = ph' }) =
    let ! ! ! ! ph , th , c = selPart ps c' in record
      { parti = c ; actBnd = th <&= th' ; images = th <?= tz' ; passTrg = ph <&= ph' }

  selPart :  (ps : kz <= kz') -> Cover ff th' ph' -> Sg _ \ iz -> Sg _ \ jz -> 
    Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph -> Sg (iz <= iz') \ ps0 -> Sg (jz <= jz') \ ps1 -> Cover ff th ph
\end{spec}
%if False
\begin{code}
  selHSub :  forall {I}{D : I -> Desc I}{src src' trg bnd} ->
             src <= src' -> HSub D src' trg bnd -> HSub D src trg bnd
  selHSub ps (record { parti = c' ; actBnd = th' ; images = tz' ; passTrg = ph' }) =
    let ! ! ! ! ph , th , c = selPart ps c' in record
      { parti = c ; actBnd = th <&= th' ; images = th <?= tz' ; passTrg = ph <&= ph' }

  selPart :  forall {K}{iz' jz' kz kz' : Bwd K}{th' : iz' <= kz'}{ph' : jz' <= kz'}
             (ps : kz <= kz') -> Cover ff th' ph' ->
             Sg _ \ iz -> Sg _ \ jz -> Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph ->
             Sg (iz <= iz') \ ps0 -> Sg (jz <= jz') \ ps1 -> Cover ff th ph

  selPart (ps o') (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0    , ps1 o' , c
  selPart (ps o') (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 o' , ps1 , c
  selPart (ps o') (c' css) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 o' , ps1 o' , c
  selPart (ps os) (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 , ps1 os , c c's
  selPart (ps os) (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 os , ps1 , c cs'
  selPart (ps os) (_css {both = ()} _)
  selPart oz czz = ! ! ! ! oz , oz , czz
\end{code}
%endif

%format allLeft = "\F{allLeft}"
%if False
\begin{code}
allLeft : forall {K}{iz kz : Bwd K}{ov}{th : iz <= kz}{ph : B0 <= kz} -> Cover ov th ph -> iz == kz
allLeft (c cs') rewrite allLeft c = refl
allLeft czz = refl
\end{code}
%endif

%format hSub = "\F{hSub}"
%format hSubs = "\F{hSubs}"
%format hSubs/ = "\F{hSubs}_{\F{\slash}}"
%format hered = "\F{hered}"
%if False
\begin{code}
hSub    : forall {I D src trg bnd}{i : I} ->
  HSub D src trg bnd -> TmR D i src              -> TmR D i / trg
hSubs   : forall {I D src trg bnd}(S : Desc I) ->
  HSub D src trg bnd -> [! S !! TmR D !]R src    -> [! S !! TmR D !]R / trg
hSubs/  : forall {I D src trg bnd}(S : Desc I) ->
  HSub D src trg bnd -> [! S !! TmR D !]R / src  -> [! S !! TmR D !]R / trg
hered   : forall {I D jz trg bnd}{i : I} ->
  (jz !- TmR D i) / trg -> B0 - (jz => i) <= bnd -> [! SpD jz !! TmR D !]R / trg -> TmR D i / trg
\end{code}
%endif

The definition of hereditary substitution is a mutual recursion, terminating because the
active scope is always decreasing: |hSub| is the main operation on terms; |hSubs| and |hSubs/|
proceed structurally, in accordance with a syntax description; |hered| invokes |hSub| hereditarily.
\begin{spec}
hSub    :                  HSub D src trg bnd -> TmR D i src              -> TmR D i / trg
hSubs   : (S : Desc I) ->  HSub D src trg bnd -> [! S !! TmR D !]R src    -> [! S !! TmR D !]R / trg
hSubs/  : (S : Desc I) ->  HSub D src trg bnd -> [! S !! TmR D !]R / src  -> [! S !! TmR D !]R / trg
hered   : (jz !- TmR D i) / trg -> B0 - (jz => i) <= bnd -> [! SpD jz !! TmR D !]R / trg -> TmR D i / trg
\end{spec}
When |hSub| finds a variable, |selHSub| will reduce the |parti| to a single choice:
if the variable is passive, embed it in target scope and reattach its substituted spine;
if active, proceed |hered|itarily.
\begin{code}
hSub {D = D}{i = i} h [ ts ] = map/ [_] (hSubs (D i) h ts)
hSub h (# {jz} (pair (only ^ th) ts _)) with selHSub th h | hSubs/ (SpD jz) h ts
... | record { parti = _css {both = ()} _ }                         | ts'
... | record { parti = czz cs' ; passTrg = ph }                     | ts' = map/ # (vaR ph ,R ts')
... | record { parti = czz c's ; actBnd = th' ; images = B0 - im }  | ts' = hered im th' ts'
\end{code}

%format part = "\F{part}"
%format spAll = "\F{spAll}"
To substitute a variable |hered|itarily, find it in the bound: the scope of its
kind becomes the new, \emph{structurally smaller} bound. Helper function |part| partitions
passive free variables from active bound variables, while |spAll| converts the spine to an
environment of images.
\begin{code}
hered                     im                (th' o') ts' = hered im th' ts'
hered {D = D}{trg = trg}  ((ph \\ t) ^ ps)  (th' os) ts' = let ! ! c = part _ _ in 
  hSub (record { parti = c ; actBnd = ph ; images = ph <?= spAll ts' ; passTrg = ps }) t where
    spAll  :  forall {kz} -> [! SpD kz !! TmR D !]R / trg -> All _ kz
    part   :  forall kz iz -> Sg (kz <= (kz ++ iz)) \ th -> Sg (iz <= (kz ++ iz)) \ th' -> Cover ff th th'
\end{code}
%if False
\begin{code}
    spAll {B0}              _                    = B0
    spAll {kz - (jz => i)}  (pair ts' t _ ^ ps)  = spAll (thin/ ps ts') - thin/ ps t
    part kz (iz - _) = let ! ! c = part kz iz in ! ! c c's
    part (kz - _) B0 = let ! ! c = part kz B0 in ! ! c cs'
    part B0 B0 = ! ! czz
\end{code}
%endif

In the structural part of the algorithm, we may exploit our richer usage information
to stop as soon as the active variables have all left scope,
thinning the remaining passive variables with no further traversal. The lemma |allLeft| shows
that if the right of a partition is empty, the left must be full.
\begin{code}
hSubs (RecD k)   h (ph \\ t)     = scope k \\R hSub (wkHSub h ph) t
hSubs (SgD S T)  h (s , ts)      = map/ (s ,_) (hSubs (T s) h ts)
hSubs OneD       h <>            = <>R
hSubs (S *D T)   h (pair s t _)  = hSubs/ S h s ,R hSubs/ T h t 
hSubs/ S h' (ts ^ th) with selHSub th h'
hSubs/ S h' (ts ^ th) | record { parti = c ; images = B0 ; passTrg = ph } rewrite allLeft c = ts ^ ph
hSubs/ S h' (ts ^ th) | h = hSubs S h ts
\end{code}

\bibliographystyle{eptcs}
\bibliography{EGTBS}
\end{document}
