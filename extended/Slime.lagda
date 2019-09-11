
\section{When `Green Slime' is Bad, Avoid It}

%if False
\begin{code}
module Slime where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

open import DeBruijn
open import Thinnings
\end{code}
%endif

We are accustomed to reasoning by \emph{equation}.

%format ~ = "\mathrel{\D{\sim}}"
%format _~_ = "\D{" _ "\!}" ~ "\D{\!" _ "}"
%format r~ = "\C{r\!\!\sim}"

\begin{definition}[Inductive Equality, |~|]
In Agda, we may give an inductive definition of equality,
as follows:
\begin{code}
infix 5 _~_
data _~_ {l}{X : Set l}(x : X) : X -> Set l where
  r~ : x ~ x
\end{code}
The |l| parameter is an arbitrary \emph{level} in the
Russell-style hierarchy: |Set| abbreviates |Set 0|;
|Set 0 : Set 1|, and so on.
%if False
\begin{code}
{-# BUILTIN EQUALITY _~_ #-}
\end{code}
%endif
\end{definition}

The above definition is \emph{intensional}, in that we
can give canonical evidence that |x ~ y| only if |x| and
|y| have the same \emph{implementation}, up to definitional
equality. We shall have trouble because of that, in what is
to follow, but that is not the trouble I mean to discuss in
this section.

Suppose we have an hypothesis |q : th -fake ph ~ ps -, x|.
We ought to be able to deduce that |th| and |ph| are both
made by |(_-, x)|. However, pattern matching on the equality
proof |q| will fail, because it is not clear how to unify
|th -fake ph| with |ps -, x|, unless we are gifted with the
power to run functions backwards, which Agda is not. Our
only option is to \emph{remember} how |-fake| computes, then
match on |ph| and |th|, eliminating the impossible cases
which arise by refuting |q|.

`Green slime' is a colloquialism for expressions involving
recursively defined functions which do not compute to
canonical form. It is toxic to unification, as it unifies
only with variables (purple things). Fortunately, there
are strategies to avoid it.

%format grf = "\F{f}"
%format blF = "\D{F}"
%format bks = "s"
%format bkt = "t"
\begin{craft}[Inductive Relations are Invertible]
It is often useful to replace equations |grf bks ~ bkt|
with relations |blF bks bkt|, where |blF| is defined
inductively to be the \emph{graph} of |f|.
\end{craft}

Let us put this into practice at once!

\begin{definition}[composition triangle]
Reading from the definition of |-fake|, construct its
graph, thus:
%format CTL = "\D{\ulcorner}\,"
%format CTM = "\,\D{\fatsemi}\,"
%format CTR = "\,\D{\urcorner\!\!\sim}\,"
%format (CTri (th) (ph) (ps)) = CTL th CTM ph CTR ps
%format (CTS1 (ph) (ps)) = (CTL _ CTM ph CTR ps)
%format (CTS2 (th) (ps)) = (CTL th CTM _ CTR ps)
%format (CTS3 (th) (ph)) = (CTL th CTM ph CTR _)
%format -^, = "\mathbin{\C{\mathrm{-\hspace*{-0.06in}\raisebox{-0.04in}{\^{}}\hspace*{-0.03in},}}}"
%format _-^,_ = "\C{" _ "\!}" -^, "\C{\!" _ "}"

%if False
\begin{code}
module _ {X : Set} where
\end{code}
\begin{code}
  infixl 20 _-^,_

  data CTri : {-<-} forall {ga de ze : Bwd X} -> {->-} (th : ga <= de)(ph : de <= ze)(ps : ga <= ze) -> Set where

    _-^_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     (CTri th         ph         ps)
           -> forall x ->                                                                                       (CTri th         (ph -^ x)  (ps -^ x))

    _-^,_  : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     (CTri th         ph         ps)
           -> forall x ->                                                                                       (CTri (th -^ x)  (ph -, x)  (ps -^ x))

    _-,_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     (CTri th         ph         ps)
           -> forall x ->                                                                                       (CTri (th -, x)  (ph -, x)  (ps -, x))

    []     :                                                                                                    (CTri []         []         [])

  CTS1 = \ {ga}{de}{ze} ph ps th -> CTri {ga}{de}{ze} th ph ps
  CTS2 = \ {ga}{de}{ze} th ps ph -> CTri {ga}{de}{ze} th ph ps
  CTS3 = CTri
\end{code}
%endif
\begin{spec}
  infixl 20 _-^,_

  data CTL _ CTM _ CTR _ : {-<-} forall {ga de ze : Bwd X} -> {->-} (th : ga <= de)                             (ph : de <= ze)(ps : ga <= ze) -> Set where

    _-^_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     CTL th         CTM ph       CTR ps
           -> forall x ->                                                                                       CTL th         CTM ph -^ x  CTR ps -^ x

    _-^,_  : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     CTL th         CTM ph       CTR ps
           -> forall x ->                                                                                       CTL th -^ x    CTM ph -, x  CTR ps -^ x

    _-,_   : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}                     CTL th         CTM ph       CTR ps
           -> forall x ->                                                                                       CTL th -, x    CTM ph -, x  CTR ps -, x

    []     :                                                                                                    CTL []         CTM []       CTR []
\end{spec}
\end{definition}

And there was nothing green to be seen! The only green things on the right in the
definition of |-fake| were recursive calls to |-fake|, and these we have replaced
by variables.

I call inhabitants of |(CTri th ph ps)|
\emph{composition triangles} exactly because they witness the commutation of the
diagram
\[\xymatrix{
                        & |ze| \\
  |de| \ar[ru]^{|ph|}   &      \\
                        & |ga| \ar[lu]^{|th|}\ar[uu]_{|ps|}\\
}\]
Now let us get our hands on them. You might think that the thing to do is to prove
\[
|(th : ga <= de)(ph : de <= ze) -> (CTri th ph (th -fake ph))|
\]
but that amounts to implementing composition a \emph{third} time, as well as being
pragmatically suboptimal, as I shall explain later. A better move is to reimplement
|-fake| by proving, morally,
\[
|(th : ga <= de)(ph : de <= ze) ->| \;\mbox{`$\exists |ps|.$'}\; |(CTri th ph ps)|
\]
We shall have need of existential quantification!

%format Sg = "\D{\Upsigma}"
\begin{definition}[Dependent Pair Types, Unit Type]
Dependent pair types (|Sg|-types, in the jargon) may be introduced as
\emph{records}, where the
type of the second projection depends on the value of the first. The definition
is polymorphic in the type theoretic hierarchy.
%format Sg = "\D{\Upsigma}"
%format [* = "(\!"
%format :: = ":"
%format ]* = "\!)\mathrel{\D{\times}}"
%format , = "\C{,}"
%format _,_ = "\C{" _ "}" , "\C{" _ "}"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format One = "\D{One}"
%format <> = "\C{\langle\rangle}"
\begin{code}
infixr 5 _,_

record Sg {k l}(S : Set k)(T : S -> Set l) : Set (l \-/ k) where
  constructor _,_
  field  fst  : S
         snd  : T fst
open Sg public     -- brings the projections into scope

syntax Sg S (\ x -> T) = [* x :: S ]* T

record One {l} : Set l where constructor <>
\end{code}
It is convenient to sugar dependent pair types as a binding form,
after the fashion of dependent
function types\footnote{Agda does not let you do precisely this, but \LaTeX{} does
the rest.}.
\end{definition}

Three commonly occurring variations merit abbreviation.
%format * = "\mathbin{\D{\times}}"
%format _*_ = "\D{" _ "\!}" * "\D{\!" _ "}"
%format :* = "\mathbin{\D{\dot\times}}"
%format _:*_ = "\D{" _ "\!}" :* "\D{\!" _ "}"
%format < = "\D{\langle}"
%format > = "\D{\rangle}"
%format <_> = < "\D{\!" _ "\!}" >
\begin{code}
infixr 4 _*_
_*_ : {-<-}forall {k l} ->{->-} Set k -> Set l -> Set (l \-/ k)
S * T = [* _ :: S ]* T
_:*_ : {-<-}forall {k l} ->{->-} {S : Set k}(P Q : S -> Set l) -> (S -> Set l)
(P :* Q) s = P s * Q s
<_> : {-<-}forall {k l}{->-} {S : Set k}(P : S -> Set l) -> Set (l \-/ k)
< P > = [* x :: _ ]* P x
\end{code}
The first of these is ordinary non-dependent pairing. The second is its
pointwise lifting to `predicates': |P :* Q| holds whenever |P| holds and |Q| holds.
The third, prounounced
`possibly |P|' or `something is |P|',
asserts that a `predicate' (i.e., a function to |Set l|) is
somehow satisfied: the domain of the predicate is elided.
Now we can write |< P :* Q >| for `something is both |P| and |Q|'.

\begin{craft}[Mixfix Operator Sections, Pattern Synonyms]
The relation |CTL _ CTM _ CTR _| is given in mixfix form exactly because Agda
supports operator sections --- |(CTS1 ph ps)|, |(CTS2 th ps)| and |(CTS3 th ph)|
--- which are predicates designed to be used with |<_>|. We can write
%format th0 = th sb0
%format th1 = th sb1
%format ph0 = ph sb0
%format ph1 = ph sb1
\[
  |<(CTS3 th0 ph0) :* (CTS3 th1 ph1)>|
\]
to assert the existence of a commuting square. Very often, the existential witness
is not important. Agda provides the means to elide it:
%format & = "\C{\dot{,}}\,"
%format _&_ = "\C{" _ "}" & "\C{" _ "}"
\begin{code}
infixr 6 _&_
pattern _&_ p q = _ , p , q
\end{code}
A \emph{pattern synonym} is essentially a macro which can be used on either side
of the |=| sign: in this case, we ignore the existential witness on the left and
demand its synthesis on the right.
\end{craft}

%format -<= = -fake
%format _-<=_ = _-fake_
%format <-> = "\mathbin{\F{\langle\fatsemi\rangle}}"
%format _<->_ = "\F{" _ "\!}" <-> "\F{\!" _ "}"

\begin{lemma}[constructing composition triangles, |<->|]
If |th| and |ph| are thinnings which meet in the middle, it is possible to
construct their composition triangle. Accordingly,
we may redefine |-fake| to project the existential witness.
\begin{code}
infix 10 _<->_

_<->_ : {-<-} forall {X}{ga de ze : Bwd X} -> {->-} (th : ga <= de)(ph : de <= ze) -> <(CTS3 th ph)>
th       <-> ph -^ x  with _ , v <- th <-> ph  = _ , v -^ x
th -^ x  <-> ph -, x  with _ , v <- th <-> ph  = _ , v -^, x
th -, x  <-> ph -, x  with _ , v <- th <-> ph  = _ , v -, x
[]       <-> []                                = _ , []

_-<=_ : {-<-} forall {X}{ga de ze : Bwd X} -> {->-} ga <= de -> de <= ze -> ga <= ze
th -<= ph = fst (th <-> ph)
\end{code}
\end{lemma}

\begin{craft}[|with| Programs]
The |with| programming notation~\cite{DBLP:journals/jfp/McBrideM04}
%format vep = "\vec{p}"
%format vep1 = vep "_1"
%format vepn = vep "_n"
%format blp = "p"
%format blp1 = blp "_1"
%format blpn = blp "_n"
%format ble = "e"
%format ble1 = ble "_1"
%format blen = ble "_n"
%format vdots = "\vdots"
\begin{spec}
grf vep   with   ble
grf vep1  |      blp1  = ble1
          vdots
grf vepn  |      blpn  = blen
\end{spec}
allows us to extend the left-hand side of a program with an extra column for
the value of |ble|, so we may match patterns anywhere, refining the original
patterns |vep| as well as asking about |ble|. Usefully, |ble| is abstracted
from any types where it occurs, so matching on its value refines types, too.

By defining |-<=| as a projection of |<->|, we make |with th <-> ph| abstract
all occurrences of |-<=| at the same time as it yields up the composition
triangle. The same is true of any program defined as the existential witness
to the possibility of satisfying a specification.

The recently added notation, |with blp <- ble|, allows us to avoid introducing
a new line to the pattern match if there is only \emph{one} case, given by
|blp|.
\end{craft}

\begin{craft}[Invisible Programs]
Agda allows the `don't care' \-/ to be used both in patterns, where it neglects to
ask a question, and in expressions, where it neglects to give an answer. In the
latter case, the missing term must be inferable by unification. In the case of
function graphs, the program already given in the relation determines by its
construction the missing existential witnesses. The composition \emph{function}
has all but disappeared!
\end{craft}

Now, composition triangles give the graph of a function, and functions are
deterministic, accordingly, we should be able to recover the fact that the
inputs determine both the output and the witness.

\begin{lemma}[Uniqueness of Composition Triangles]
For any given inputs |th| and |ph|, there is at most one |ps| and at most one
|v| such that |v : (CTri th ph ps)|.
%if False
\begin{code}
pattern splatr = r~
pattern splatrr = r~ , r~
pattern splatrr,rr = splatrr , splatrr
\end{code}
%endif
%format contraction = "\C{\star}"
%format splatr = contraction
%format splatrr = contraction
%format splatrr,rr = contraction
%format ~-~ = "\mathbin{\F{\sim\!\!\!\fatsemi\!\!\!\sim}}"
%format _~-~_ = "\F{" _ "\!}" ~-~ "\F{\!" _ "}"
%format v0 = v sb0
%format v1 = v sb1
%format ps0 = ps sb0
%format ps1 = ps sb1
%if False
\begin{code}
infix 10 _~-~_
_~-~_  : {-<-} forall {X}{ga de ze : Bwd X}{th : ga <= de}{ph : de <= ze}{ps0 ps1 : ga <= ze} -> {->-}  (v0 : (CTri th ph ps0))(v1 : (CTri th ph ps1))
       ->                                                                                               Sg (ps0 ~ ps1) \ { splatr -> v0 ~ v1 }
v0 -^ x   ~-~ v1 -^ x   with splatrr <- v0 ~-~ v1  = splatrr
v0 -^, x  ~-~ v1 -^, x  with splatrr <- v0 ~-~ v1  = splatrr
v0 -, x   ~-~ v1 -, x   with splatrr <- v0 ~-~ v1  = splatrr
[]        ~-~ []                                   = splatrr
\end{code}
%endif
\begin{spec}
infix 10 _~-~_
_~-~_  : {-<-} forall {X}{ga de ze : Bwd X}{th : ga <= de}{ph : de <= ze}{ps0 ps1 : ga <= ze} -> {->-}  (v0 : (CTri th ph ps0))(v1 : (CTri th ph ps1))
       ->                                                                                               [* (splatr) : ps0 ~ ps1 ]* v0 ~ v1
v0 -^ x   ~-~ v1 -^ x   with splatrr <- v0 ~-~ v1  = splatrr
v0 -^, x  ~-~ v1 -^, x  with splatrr <- v0 ~-~ v1  = splatrr
v0 -, x   ~-~ v1 -, x   with splatrr <- v0 ~-~ v1  = splatrr
[]        ~-~ []                                   = splatrr
\end{spec}
\end{lemma}

\begin{craft}[Dependent Equations]
The equation |v0 ~ v1| may look ill typed, but it is not. The inlined pattern match
in the dependent pair type causes |ps0| to unify with |ps1|. This can be quite a
convenient way to specify `telescopic' equations.
\end{craft}

\begin{craft}[Contraction Pattern, |contraction|]
In typeset code, I
write |contraction| instead of unique patterns which can be
constructed by record expansion followed by at most one step of case
analysis for each field. Matching with |contraction| collapses spaces
to a point. Agda does not yet support this feature. Here, it
abbreviates |r~ , r~|, but it can scale to much larger uninteresting
types.  \end{craft}

We have a notion of thinning, closed under identity and composition. I like to
visualize thinnings as two horizontal sequences of dots. Each dot on the bottom
 is joined to a dot on top by a vertical chord, but there may be dots on top with no
chord incident.
\[\begin{array}{ccccc}
  \bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
  \mid && \mid && \mid \vspace*{-0.17in}\\
  \bullet && \bullet && \bullet \\
\end{array}\]
The identity thinning has all chords present. Composition is vertical pasting,
followed by the contraction of chords which do not reach the bottom.
\[|io| \quad = \quad
  \begin{array}{ccccc}
  \bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
  \mid & \mid & \mid & \mid & \mid \vspace*{-0.17in}\\
  \bullet & \bullet & \bullet & \bullet & \bullet \\
\end{array}
\qquad\qquad\qquad\qquad
\begin{array}{cccccc}
        &\bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
        &\mid && \mid && \mid \vspace*{-0.17in}\\
        &\bullet && \bullet && \bullet \vspace*{-0.17in}\\
  |-<=| &\mid &&&& \mid  \vspace*{-0.17in}\\
        &\bullet &&&& \bullet
\end{array}
\quad = \quad
\begin{array}{ccccc}
  \bullet & \bullet & \bullet & \bullet & \bullet \vspace*{-0.17in}\\
  \mid &&  && \mid \vspace*{-0.17in}\\
  \mid &&  && \mid \vspace*{-0.17in}\\
  \mid &&&& \mid  \vspace*{-0.17in}\\
  \bullet &&&& \bullet
\end{array}
\]
Spatial intuition makes it clear, informally, that identitied are absorbed and that
composition is associative. Let us make that intuition formal.

\begin{lemma}[Degenerate Triangles]
Every thinning |th| induces two degenerate triangles, where |th| and |io| are
composed, yielding |th|.
%format io- = "\F{\upiota\fatsemi}"
%format -io = "\F{\fatsemi\upiota}"
%format _-io = "\F{" _ "}\!" -io
%format io~ = "\F{\upiota\fatsemi\!\!\sim}"
%format ~io = "\F{\sim\!\!\fatsemi\upiota}"
%format _~io = "\F{" _ "}\!" -io
%if False
\begin{code}
module _ {X : Set} where
\end{code}
%endif
\begin{code}
  io-   : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> (CTri io th th)
  io- (th -^ x)  = io- th -^ x
  io- (th -, x)  = io- th -, x
  io- []         = []

  infixl 30 _-io
  _-io  : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> (CTri th io th)
  (th -^ x)  -io = th -io -^, x
  (th -, x)  -io = th -io -, x
  []         -io = []
\end{code}
We may readily extract identity absorption laws in equational form.
\begin{code}
  io~   : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> io -<= th ~ th
  io~ th with _ , v <- io <-> th with splatrr <- v ~-~ io- th = splatr
  _~io  : {-<-}forall {ga de : Bwd X}{->-}  (th : ga <= de) -> th -<= io ~ th
  th ~io with _ , v <- th <-> io with splatrr <- v ~-~ th -io = splatr
\end{code}
\end{lemma}

%format ga0 = ga sb0
%format ga1 = ga sb1
%format ga2 = ga sb2
%format ga3 = ga sb3
%format th01 = th sb01
%format th12 = th sb12
%format th23 = th sb23
%format th02 = th sb02
%format th13 = th sb13
%format th03 = th sb03
Framing the associativity of composition in terms of triangles gives us a choice.
When three arrows compose in sequence, they generate three more, together with four
triangles.
\[\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar@@{.>}[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar@@{.>}[uuurr]_{|th02|}
        \ar@@{.>}[uuuu]^{|th03|} & &  \\
}\]
Associativity amounts to the assertion that, given any two of the three composite
arrows, with the two triangles they generate, the whole diagram can be recovered.
All three results are useful, and they are interderivable, but one must be
proven by induction --- not on \emph{thinnings} but on \emph{triangles}.

\begin{lemma}[Associativity (03)]
\[\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar[uuurr]_{|th02|}
        \ar@@{.>}[uuuu]^{|th03|} & &  \\
}\]
%format assoc03 = "\F{assoc03}"
\begin{code}
  assoc03 : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{th01 : ga0 <= ga1}{th02 : ga0 <= ga2}{th13 : ga1 <= ga3}{th23 : ga2 <= ga3}  -> {->-}  <(CTS2 th01 th02) :* (CTS1 th23 th13)> 
           ->                                                                                                                            <(CTS3 th01 th13) :* (CTS3 th02 th23)>
  assoc03 (v        & w -^ x)   with v' & w' <- assoc03 (v & w)  = v' -^ x   & w' -^ x
  assoc03 (v -^ x   & w -^, x)  with v' & w' <- assoc03 (v & w)  = v' -^ x   & w' -^, x
  assoc03 (v -^, x  & w -, x)   with v' & w' <- assoc03 (v & w)  = v' -^, x  & w' -^, x
  assoc03 (v -, x   & w -, x)   with v' & w' <- assoc03 (v & w)  = v' -, x   & w' -, x
  assoc03 ([]       & [])                                        = []        & []
\end{code}
There are three step cases for an inserted |x|, covering the three stages in the
sequence where it can have been inserted. There is one step case for a copied |x|,
which must have be copied in all three stages.

The more familiar equational form of associativity follows by triangulation.
%format pp = "^{\V{\prime}}"
%format assoc = "\F{assoc}"
%format v012 = v sb012
%format v013 = v sb013
%format v023 = v sb023
%format v123 = v sb123
%format v013' = v013 pp
%format v023' = v023 pp
\begin{code}
  assoc  : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{->-}  (th01 : ga0 <= ga1)(th12 : ga1 <= ga2)(th23 : ga2 <= ga3)
         ->                                            th01 -<= (th12 -<= th23) ~ (th01 -<= th12) -<= th23
  assoc th01 th12 th23 with  th13  , v123 <- th12 <-> th23  | th02  , v012 <- th01 <-> th12
                       with  _     , v013 <- th01 <-> th13  | _     , v023 <- th02 <-> th23 |
        v013' & v023' <- assoc03 (v012 & v123) with splatrr,rr <- v013 ~-~ v013' , v023 ~-~ v023' = splatr
\end{code}
\end{lemma}

We may also derive the other two forms of diagrammatic composition.

\begin{lemma}[Associativity (02, 13)]
\[\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar@@{.>}[uuurr]_{|th02|}
        \ar[uuuu]^{|th03|} & &  \\
}
\qquad\qquad\qquad
\xymatrix{
  |ga3| & &       \\
        & & |ga2| \ar[llu]_{|th23|}\\
        & &       \\
        & & |ga1| \ar[uu]_{|th12|} \ar@@{.>}[uuull]_{|th13|} \\
  |ga0| \ar[rru]_{|th01|}
        \ar[uuurr]_{|th02|}
        \ar[uuuu]^{|th03|} & &  \\
}\]
%format assoc02 = "\F{assoc02}"
%format assoc13 = "\F{assoc13}"
\begin{code}
  assoc02 : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{th01 : ga0 <= ga1}{th03 : ga0 <= ga3}{th12 : ga1 <= ga2}{th23 : ga2 <= ga3}  -> {->-}  <(CTS2 th01 th03) :* (CTS3 th12 th23)>
           ->                                                                                                                            <(CTS3 th01 th12) :* (CTS1 th23 th03)>
  assoc02 {th01 = th01}{th12 = th12} (v013 & v123) with th02 , v012 <- th01 <-> th12 with
     v013' & v023 <- assoc03 (v012 & v123) with splatrr <- v013 ~-~ v013'
    = v012 & v023

  assoc13 : {-<-}forall {ga0 ga1 ga2 ga3 : Bwd X}{th01 : ga0 <= ga1}{th03 : ga0 <= ga3}{th12 : ga1 <= ga2}{th23 : ga2 <= ga3}  -> {->-}  <(CTS3 th01 th12) :* (CTS1 th23 th03)>
           ->                                                                                                                            <(CTS2 th01 th03) :* (CTS3 th12 th23)>
  assoc13 {th12 = th12}{th23 = th23} (v012 & v023) with th13 , v123 <- th12 <-> th23 with
      v013 & v023' <- assoc03 (v012 & v123) with splatrr <- v023 ~-~ v023'
    = v013 & v123
\end{code}
That is, we construct the missing arrow and one of the triangles by composition.
The |assoc03| lemma gives us the other triangle we want and a duplicate of one we
already have. Contracting the duplication makes the triangles we want fit together.
\end{lemma}

We should now able to construct the category of thinnings, if only we knew
what it might mean to construct a category \emph{in type theory}. That is when our troubles
really begin.
