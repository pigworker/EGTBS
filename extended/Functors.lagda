\section{Functors as Arrows}

%if False
\begin{code}
module Functors where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

open import DeBruijn
open import Thinnings
open import Slime
open import Worry
open import Categories
\end{code}
%endif

When does one category tell you about another? When we have a
structure-preserving translation --- a \emph{functor} --- between
them: maps of cities are useful in part because the lines on the map
join up in the same pattern as the streets in the city. What is a functor, in our
setting?

%format Ddot = "\V{D}."
%format D.Obj = Ddot Obj
%format D.Arr = Ddot Arr
%format D.id = Ddot id
%format D.- = Ddot -
%format D.~> = Ddot ~>
%format D.~~ = Ddot ~~
%format D._-_ = Ddot _-_
%format D.coex = Ddot coex
%format D.idco = Ddot idco
%format D.coid = Ddot coid
%format D.coco = Ddot coco
%format Edot = "\V{E}."
%format E.Obj = Edot Obj
%format E.Arr = Edot Arr
%format E.id = Edot id
%format E.- = Edot -
%format E.~> = Edot ~>
%format E.~~ = Edot ~~
%format E._-_ = Edot _-_
%format E.coex = Edot coex
%format E.idco = Edot idco
%format E.coid = Edot coid
%format E.coco = Edot coco
%format Functor = "\F{Functor}"

\begin{definition}[Functor]
Fix a \emph{source} category |C| and a \emph{target} category |D|. Their relative
sizes are unimportant.
\begin{code}
module _ {l k l' k'}(C : Cat l k)(D : Cat l' k') where
  private module C = Cat C ; module D = Cat D
\end{code}
We may construct a |Setoid| of structure-preserving translations from |C| to |D|.
Every |C| object must |Map| to a |D| object, and every |C| arrow must |map| to
a |D| arrow, compatibly with |Map|.
\begin{code}
  Functor : Setoid (l \-/ k \-/ l' \-/ k')
  Functor =
    SG (C.Obj -> D.Obj) \ Map -> 
    (  IM C.Obj \ S -> IM C.Obj \ T -> PI (S C.~> T) \ _ ->
                 D.Arr (Map S) (Map T))
    ||  \ map ->
\end{code}
The use of a comprehension allows us to add the laws that |map| must obey:
it must respect equivalence, and preserve identities and composition.
\begin{code}
        ({S T : C.Obj}{f g : S C.~> T} ->
            f C.~~ g -> map f D.~~ map g)
    *   ({X : C.Obj} ->
            map (C.id {X}) D.~~ D.id {Map X})
    *   ({R S T : C.Obj}(f : R C.~> S)(g : S C.~> T) ->
            map (f C.- g) D.~~ (map f D.- map g))
\end{code}
\end{definition}

Now, we should like Agda to recognize functors --- elements of that |Setoid| ---
when she sees them and to know their source and target categories implicitly.
This calls for `green things in blue packaging'.
%format -F> = "\D{\Rightarrow}"
%format _-F>_ = "\D{" _ "\!}" -F> "\D{\!" _ "}"
%format fun = "\C{fun}"
%format nuf = "\C{nuf}"
%format Map = "\F{Map}"
%format map = "\F{map}"
%format mapex = "\F{mapex}"
%format mapid = "\F{mapid}"
%format mapco = "\F{mapco}"
\begin{code}
  record _-F>_ : Set (l \-/ k \-/ l' \-/ k') where
    constructor fun
    field nuf : El Functor
    Map    = fst nuf 
    map    = fst (snd nuf)
    mapex  = fst (snd (snd nuf))
    mapid  = fst (snd (snd (snd nuf)))
    mapco  = snd (snd (snd (snd nuf)))
  open _-F>_ public
\end{code}
The |-F>| operator becomes infix when the module fixing |C| and |D| is opened.

I have made |Functor| a |Setoid| for a reason: they will shortly be the |Arr|ows of a
|Cat|egory. However, before we can go to work with this definition, we should tool
up for the reasoning within setoids that we shall inevitably face.

\begin{craft}[Equivalence Reasoning for Setoids]
Fix a |Setoid|, |X|, and name its laws.
\begin{code}
module _ {l}{X : Setoid l} where
  private RfX = Rf X ; SyX = Sy X ; TrX = Tr X
\end{code}

We may benefit from `green things in blue packaging' by suppressing more detail
when the setoid at work is fixed. E.g., we can drop the element from the
reflexivity witness.
\begin{code}  
  rS : {-<-} forall {x : El X} -> {->-}  X :> x ~~ x
  rS {x} = eq (RfX x)
\end{code}

Moreover, we can build some combinators which facilitate readable chains of
equational reasoning, showing the steps and the explanations which justify
them.
\begin{code}
  infixr 5 _~[_>~_ _~<_]~_
  infixr 6 _~[SQED]

  _~[_>~_ : {-<-} {y z : El X} -> {->-} forall x -> X :> x ~~ y -> X :> y ~~ z -> X :> x ~~ z
  x ~[ eq q >~ eq q' = eq (TrX _ _ _ q q')
  
  _~<_]~_ : {-<-} {y z : El X} -> {->-} forall x -> X :> y ~~ x -> X :> y ~~ z -> X :> x ~~ z
  x ~< eq q ]~ eq q' = eq (TrX _ _ _ (SyX _ _ q) q')

  _~[SQED] : (x : El X) -> X :> x ~~ x
  x ~[SQED] = eq (RfX x)
\end{code}

Lastly, we have a combinator which allows us to fix the setoid.
\begin{code}
qprf : {-<-} forall {l} -> {->-} (X : Setoid l){x y : El X} -> X :> x ~~ y -> Eq X x y
qprf X = qe
\end{code}
\end{craft}

Let us have some examples.

\begin{definition}[Forgetting Arrows]
Fix a category
\begin{code}
module _ {k l}(C : Cat k l) where
  private module C = Cat C
\end{code}
The discrete category on the objects of |C| has a functor into |C|.
%format FORGET = "\F{FORGET}"
%if False
\begin{code}
  open Cat
\end{code}
%endif
\begin{code}
  FORGET : DISCRETE C.Obj -F> C
  nuf FORGET
    =  (\ X -> X)                -- objects map to themselves
    ,  (\ { splatvr -> C.id })   -- arrows map to identities
    ,  (\ { {_}{_}{splatvr}{splatvr} _ -> eq (Rf (C.Arr _ _) _) })
    ,  rS 
    ,  \ { splatvr splatvr -> 
         C.id           ~< C.idco _ ]~
         C.id C.- C.id  ~[SQED] }
\end{code}
\end{definition}

\begin{definition}[Functions as Functors]
A function |f : S -> T| is trivially a functor between discrete categories.
%format FUN = "\F{FUN}"
\begin{code}
FUN : {-<-}forall {k l}{S : Set k}{T : Set l} ->{->-} (S -> T) -> DISCRETE S -F> DISCRETE T
nuf (FUN f) = f
  , (\ { splatvr -> splatvr }) , (\ { {_}{_}{splatvr}{splatvr} _ -> splateqrv }) , splateqrv , \ { splatvr splatvr -> splateqrv }
\end{code}
\end{definition}

\begin{definition}[Identity |Functor|]
Fix a category |C|.
\begin{code}
module _ {k l : Level}{C : Cat k l} where
  open Cat C
\end{code}
There is a functor from |C| to itself.
%format I = "\F{I}"
\begin{code}
  I : C -F> C
  nuf I  =  (\ X -> X)   -- identity on objects
         ,  (\ f -> f)   -- identity on morphisms
         ,  (\ q -> q)   -- identity is extensional
         ,  rS           -- identity preserves |id|
         ,  \ _ _ -> rS  -- identity preserves |-|
\end{code}
\end{definition}

\begin{lemma}[|Functor|s compose]
Fix three categories.
%format >> = "\F{\mathbf{;}}"
%format _>>_ = "\F{" _ "\!}" >> "\F{\!" _ "}"
\begin{code}
module _ {kC lC kD lD kE lE}{C : Cat kC lC}{D : Cat kD lD}{E : Cat kE lE} where
  private module C = Cat C ; module D = Cat D ; module E = Cat E
\end{code}
\begin{code}
  _>>_ : C -F> D -> D -F> E -> C -F> E
  nuf (F >> G)
    =  (\ X -> Map G (Map F X))    -- compose |Map|s
    ,  (\ f -> map G (map F f))  -- compose |map|s
    ,  (\ q -> mapex G (mapex F q))  -- compose extensionality witnesses
    ,  (   map G (map F C.id)                     ~[ mapex G (mapid F) >~
           map G D.id                             ~[ mapid G >~
           E.id                                   ~[SQED]) 
    ,  \ f g -> 
           map G (map F (f C.- g))                ~[ mapex G (mapco F _ _) >~
           map G (map F f D.- map F g)            ~[ mapco G _ _ >~
           (map G (map F f) E.- map G (map F g))  ~[SQED]
\end{code}
\end{lemma}

We can acquire another example for the price of one useful data structure.

\begin{definition}[Environment]
An \emph{environment} is a scope-indexed sequence of sort-indexed values.
%format Env = "\D{Env}"
\begin{code}
module _ {X : Set} where

  data Env (V : X -> Set) : Bwd X -> Set where
    []    : Env V []
    _-,_  : forall {xz x} -> Env V xz -> V x -> Env V (xz -, x)
\end{code}
\end{definition}

If we flip our thinking about thinnings and see them as the \emph{selection} of a
subscope from a scope, we should be able to make the corresponding selection of
values from an environment. In particular, if a thinning tells us how the support
of a term embeds in its scope, we can whittle an environment down to just those
values that are pertinent to the term.

\begin{lemma}[Selection]
|Env V| is the action on objects of a functor from reversed thinnings to
sets-and-functions.
%format SELECT = "\F{SELECT}"
\begin{spec}
  module _ (V : X -> Set) where
    SELECT : OP (THIN X) -F> SET lzero
    fst (nuf SELECT) = Env V
\end{spec}
\end{lemma}
To prove the lemma, we must construct the rest of the |Functor|. We should
prepare the components separately, then slot them into place.
%format select = "\F{select}"
Its action on morphisms is to copy where the thinning copies and discard
where the thinning inserts.
%format <? = "\F{\leftslice}"
%format _<?_ = "\F{" _ "\!}" <? "\F{\!" _ "}"
\begin{code}
  module _ {V : X -> Set} where

    infixr 25 _<?_
    _<?_ : forall {ga de} -> ga <= de -> Env V de -> Env V ga
    (th -^ x)  <?  (vz -, v)  = th <? vz
    (th -, x)  <?  (vz -, v)  = th <? vz -, v
    []         <?  []         = []
\end{code}
%format io<? = io <?
We may readily show that the identity thinning is the complete selection.
\begin{code}
    io<? : {-<-}forall {ga}{->-}(vz : Env V ga) -> io <? vz ~ vz
    io<? []                         = r~
    io<? (vz -, v) rewrite io<? vz  = r~
\end{code}
The composition law is best shown by induction on the graph.
%format co<? = "\F{\triangle}\!" <?
\begin{code}
    co<? : {-<-} forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->  {->-}  (w : (CTri th ph ps))(vz : Env V _) -> ps <? vz ~ th <? ph <? vz
    co<? (w -^ x)   (vz -, v)  rewrite co<? w vz  = r~
    co<? (w -^, x)  (vz -, v)  rewrite co<? w vz  = r~
    co<? (w -, x)   (vz -, v)  rewrite co<? w vz  = r~
    co<? []         []                            = r~
\end{code}
%if False
\begin{code}
  module _ (V : X -> Set) where
    SELECT : OP (THIN X) -F> SET lzero
    fst (nuf SELECT) = Env V
\end{code}
%endif
We can now complete the jigsaw.
\begin{code}
    snd (nuf SELECT)  = _<?_ , (\ { splateqr -> eq \ _ -> r~ })
                      , eq io<? , (\ ph th -> eq \ vz -> co<? (snd (th <-> ph)) vz)
\end{code}

Note, by the way, that a family of types induces a functor from a discrete
category.
%format FAM = "\F{FAM}"
\begin{code}
FAM : {-<-}forall {k l}{X : Set k} ->{->-} (X -> Set l) -> DISCRETE X -F> SET l
FAM T = FUN T >> FORGET (SET _)
\end{code}

To finish this section, let us construct the category of categories, with
functors for arrows. To start with, we should define the identity functor and
functor composition.

\begin{lemma}[Category of Categories]
Fix sizes for objects and arrows.
\begin{code}
module _ (k l : Level) where
\end{code}
%if False
\begin{code}
  open Cat
\end{code}
%endif
There is a category whose objects are |Cat|egories and whose arrows are |Functor|s
%format CAT = "\F{CAT}"
\begin{code}
  CAT : Cat (lsuc (k \-/ l)) (k \-/ l)
  Obj   CAT = Cat k l
  Arr   CAT C D = Functor C D \\ nuf {C = C}{D = D}
\end{code}
\end{lemma}
To prove this, we must complete the remaining fields.
\begin{enumerate}
\item identity and composition, as above
\begin{code}
  id    CAT = I
  _-_   CAT = _>>_
\end{code}
\item extensionality witness
\begin{code}
  qe (coex  CAT {_}{_}{C} {F}{F'}{G}{G'}
            (eq (r~ , qf , <>)) (eq (r~ , qg , <>)))
    =  r~
    ,  (\ S T f -> qprf (Arr C (Map G (Map F S)) (Map G (Map F T))) (
          map G (map F f)    ~[ mapex G (eq (qf _ _ _)) >~
          map G (map F' f)   ~[ eq (qg _ _ _) >~
          map G' (map F' f)  ~[SQED]))
    ,  <>
\end{code}
\item absorption and associativity -- these are trivial
\begin{code}
  idco  CAT {_}{C} _  = eq (r~ , (\ _ _ _ -> qprf (Arr C _ _) rS) , <>)
  coid  CAT {_}{C} _  = eq (r~ , (\ _ _ _ -> qprf (Arr C _ _) rS) , <>)
  coco  CAT {_}{_}{_}{C} _ _ _
    = eq (r~ , (\ _ _ _ -> qprf (Arr C _ _) rS) , <>)
\end{code}
\end{enumerate}

