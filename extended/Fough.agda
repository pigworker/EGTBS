module Fough where

open import Agda.Primitive renaming (_⊔_ to lmax)

record Setoid l : Set (lsuc l) where
  field
    El : Set l
    Eq : El -> El -> Set l
    Rf : (x : El) -> Eq x x
    Sy : (x y : El) -> Eq x y -> Eq y x
    Tr : (x y z : El) -> Eq x y -> Eq y z -> Eq x z
open Setoid

module PACKQ {l}(X : Setoid l) where

  record _|-_~~_ (x y : El X) : Set l where
    constructor eq
    field
      qe : Eq X x y

  open _|-_~~_ public

  qprf = qe

module _ {l}{X : Setoid l} where

  open PACKQ X

  infixr 5 _~[_>~_ _~<_]~_
  infixr 6 _[SQED]

  _~[_>~_ : forall x {y z} -> _|-_~~_ x y -> _|-_~~_ y z -> _|-_~~_ x z
  x ~[ eq q >~ eq q' = eq (Tr X _ _ _ q q')
  
  _~<_]~_ : forall x {y z} -> _|-_~~_ y x -> _|-_~~_ y z -> _|-_~~_ x z
  x ~< eq q ]~ eq q' = eq (Tr X _ _ _ (Sy X _ _ q) q')

  _[SQED] : forall x -> _|-_~~_ x x
  _[SQED] x = eq (Rf X x)
  
  rS : forall {x} -> _|-_~~_ x x
  rS {x} = eq (Rf X x)

open PACKQ public

module _ {l}{X : Set l} where
  data _~_ (x : X) : X -> Set l where
    r~ : x ~ x

{-# BUILTIN EQUALITY _~_ #-}

module _ {l}(X : Set l) where

  IN : Setoid l
  El IN = X
  Eq IN = _~_
  Rf IN x = r~
  Sy IN x y r~ = r~
  Tr IN x y z r~ q = q

module _ {k l}(S : Set k)(T : S -> Set l) where

  record _><_ : Set (lmax k l) where
    constructor _,_
    field
      fst : S
      snd : T fst
  open _><_ public

  infixr 10 _,_
  infixr 20 _><_

module _ (l : Level) where
  record One : Set l where constructor <>

infixr 20 _*_
_*_ : forall {k l} -> Set k -> Set l -> Set (lmax k l)
S * T = S >< \ _ -> T

infix 22 <_>
<_> : forall {k l}{S : Set k}(T : S -> Set l) -> Set (lmax k l)
< T > = _ >< T

infixr 23 _:*_
_:*_ : forall {k l}{S : Set k}(T U : S -> Set l) -> S -> Set l
(T :* U) s = T s * U s

infixr 11 _&_
pattern _&_ s t = _ , s , t

infixr 9 _/\_
_/\_ : forall {k l}{S : Set k}{T : Set l} -> S -> T -> S * T
s /\ t = s , t

module _ {k l}(S : Set k)(T : S -> Setoid l) where

  PI : Setoid (lmax k l)
  El PI     = (s : S) -> El (T s)
  Eq PI f g = (s : S) -> Eq (T s) (f s) (g s)
  Rf PI f s         = Rf (T s) (f s)
  Sy PI f g q s     = Sy (T s) (f s) (g s) (q s)
  Tr PI f g h p q s = Tr (T s) (f s) (g s) (h s) (p s) (q s)

  IM : Setoid (lmax k l)
  El IM     = {s : S} -> El (T s)
  Eq IM f g = (s : S) -> Eq (T s) (f {s}) (g {s})
  Rf IM f s         = Rf (T s) f
  Sy IM f g q s     = Sy (T s) f g (q s)
  Tr IM f g h p q s = Tr (T s) f g h (p s) (q s)

  SG : Setoid (lmax k l)
  El SG = S >< \ s -> El (T s)
  Eq SG (s0 , t0) (s1 , t1) = (s0 ~ s1) >< \ { r~ -> Eq (T s0) t0 t1 }
  Rf SG (s , t) = r~ , Rf (T s) t
  Sy SG (s0 , t0) (.s0 , t1) (r~ , q) = r~ , Sy (T s0) t0 t1 q
  fst (Tr SG (s0 , t0) (.s0 , t1) (s2 , t2) (r~ , q01) (q , q12)) = q
  snd (Tr SG (s0 , t0) (.s0 , t1) (.s0 , t2) (r~ , q01) (r~ , q12)) = Tr (T s0) t0 t1 t2 q01 q12

module _ {k l}(T : Setoid k)(P : El T -> Set l) where

  EX : Setoid (lmax k l)
  El EX = El T >< P
  Eq EX (t0 , _) (t1 , _) = Eq T t0 t1 * One l
  Rf EX (t , _) = Rf T t , <>
  Sy EX (t0 , _) (t1 , _) (q , <>) = Sy T t0 t1 q , <>
  Tr EX (t0 , _) (t1 , _) (t2 , _) (q01 , <>) (q12 , <>) =
    Tr T t0 t1 t2 q01 q12 , <> 

module _ (k l : Level) where

  record Cat : Set (lsuc (lmax k l)) where
    field
      Obj  : Set k
      Arr  : Obj -> Obj -> Setoid l
    _~>_ : Obj -> Obj -> Set l
    S ~> T = El (Arr S T)
    _~~_ : {S T : Obj}(f g : S ~> T) -> Set l
    _~~_ {S}{T} = _|-_~~_ (Arr S T)
    field
      id   : {T : Obj} -> T ~> T
      _-_  : {R S T : Obj} -> R ~> S -> S ~> T -> R ~> T
      coex : {R S T : Obj}{f f' : R ~> S}{g g' : S ~> T} ->
             f ~~ f' -> g ~~ g' -> (f - g) ~~ (f' - g')
      idco : {S T : Obj}(f : S ~> T) -> (id - f) ~~ f
      coid : {S T : Obj}(f : S ~> T) -> (f - id) ~~ f
      coco : {R S T U : Obj}(f : R ~> S)(g : S ~> T)(h : T ~> U) ->
               (f - (g - h)) ~~ ((f - g) - h)

module _ (l : Level) where
  open Cat

  SET : Cat (lsuc l) l
  Obj  SET = Set l
  Arr  SET S T = PI S \ _ -> IN T
  id   SET x = x
  _-_  SET f g x = g (f x)
  qe (coex SET (eq qf) (eq qg)) x rewrite qf x = qg _
  qe (idco SET f) x = r~
  qe (coid SET f) x = r~
  qe (coco SET f g h) x = r~

module _ {l k l' k'}(C : Cat l k)(D : Cat l' k') where
  private module C = Cat C ; module D = Cat D

  Fun : Setoid (lmax l (lmax k (lmax l' k')))
  Fun = SG (C.Obj -> D.Obj) \ Map -> 
        EX (IM C.Obj \ S -> IM C.Obj \ T ->
            PI (S C.~> T) \ _ -> D.Arr (Map S) (Map T)) \ map ->
        ({S T : C.Obj}{f g : S C.~> T} -> f C.~~ g -> map f D.~~ map g)
      * ({X : C.Obj} -> map (C.id {X}) D.~~ D.id {Map X})
      * ({R S T : C.Obj}(f : R C.~> S)(g : S C.~> T) ->
          map (f C.- g) D.~~ (map f D.- map g))

module _ (l k : Level) where

  CAT : Cat (lsuc (lmax l k)) (lmax l k)
  Cat.Obj CAT = Cat l k
  Cat.Arr CAT = Fun
  Cat.id CAT {C}
    = (\ X -> X) , (\ f -> f)
    , (\ q -> q)
    , rS
    , \ _ _ -> rS
    where open Cat C
  Cat._-_  CAT {C}{D}{E} (F , fm , fx , fi , fc) (G , gm , gx , gi , gc)
    = (\ X -> G (F X)) , (\ a -> gm (fm a))
    , (\ q -> gx (fx q))
    , (gm (fm C.id) ~[ gx fi >~
       gm (D.id)    ~[ gi >~
       E.id          [SQED])
    , \ f g -> 
       gm (fm (f C.- g))         ~[ gx (fc _ _) >~
       gm (fm f D.- fm g)        ~[ gc _ _ >~
       (gm (fm f) E.- gm (fm g))  [SQED]
    where private module C = Cat C ; module D = Cat D ; module E = Cat E
  qe (Cat.coex CAT {C} {D} {E} {F , fm , fz} {F' , fm' , fz'} {G , gm , gx , gz} {G' , gm' , gz'}
     (eq (r~ , qf , <>)) (eq (r~ , qg , <>)))
     = r~
     , (\ S T f -> qe {X = Cat.Arr E (G (F S)) (G (F T))}
       (gm (fm f)    ~[ gx (eq (qf _ _ _)) >~
        gm (fm' f)   ~[ eq (qg _ _ _) >~
        gm' (fm' f)   [SQED]))
     , <>
  qe (Cat.idco CAT {C}{D} (F , fm , fz)) =
    r~ , (\ S T f -> qprf (D.Arr (F S) (F T)) rS) , <>
    where private module C = Cat C ; module D = Cat D
  qe (Cat.coid CAT {C} {D} (F , fm , fz)) =
    r~ , (\ S T f -> qprf (D.Arr (F S) (F T)) rS) , <>
    where private module C = Cat C ; module D = Cat D
  qe (Cat.coco CAT {B} {C} {D} {E} (F , fm , fz) (G , gm , gz) (H , hm , hz))
    = r~
    , (\ S T f -> qprf (Cat.Arr E (H (G (F S))) (H (G (F T)))) rS )
    , <>

module _ {l k l' k' : Level}(C : Cat l k)(D : Cat l' k') where
  private module C = Cat C ; module D = Cat D
  
  _=>_ : Cat (lmax l (lmax k (lmax l' k'))) (lmax l (lmax k k'))
  Cat.Obj _=>_ = El (Fun C D)
  Cat.Arr _=>_ (F , fm , _) (G , gm , _) = 
    EX (IM C.Obj \ X -> D.Arr (F X) (G X)) \ n ->
    {S T : C.Obj}(f : S C.~> T) -> (fm f D.- n {T}) D.~~ (n {S} D.- gm f)
  Cat.id _=>_ {F , fm , _}
    = D.id
    , \ f ->
      fm f D.- D.id   ~[ D.coid _ >~
      fm f            ~< D.idco _ ]~
      (D.id D.- fm f)  [SQED]
  Cat._-_ _=>_ {F , fm , fx , fi , fc} {G , gm , gx , gi , gc} {H , hm , hx , hi , hc}
    (n , na) (p , pa)
    = n D.- p
    , \ f -> 
      fm f D.- (n D.- p)   ~[ D.coco _ _ _ >~
      (fm f D.- n) D.- p   ~[ D.coex (na f) rS >~
      (n D.- gm f) D.- p   ~< D.coco _ _ _ ]~
      n D.- (gm f D.- p)   ~[ D.coex rS (pa f) >~
      n D.- (p D.- hm f)   ~[ D.coco _ _ _ >~
      ((n D.- p) D.- hm f   [SQED])
  qe (Cat.coex _=>_ (eq (nq , <>)) (eq (pq , <>)))
    = (\ X -> qe (D.coex (eq (nq X)) (eq (pq X))))
    , <>
  qe (Cat.idco _=>_ _) = (\ _ -> qe (D.idco _)) , <>
  qe (Cat.coid _=>_ _) = (\ _ -> qe (D.coid _)) , <>
  qe (Cat.coco _=>_ _ _ _) = (\ _ -> qe (D.coco _ _ _)) , <>


module _ {l k : Level}(C : Cat l k)(I : Cat.Obj C) where
  open Cat C

  _/_ : Cat (lmax l k) k
  Cat.Obj _/_ = Obj >< \ X -> X ~> I
  Cat.Arr _/_ (X , f) (Y , g) = EX (Arr X Y) \ h -> (h - g) ~~ f
  Cat.id _/_ = id , idco _
  Cat._-_ _/_ {R , r}{S , s}{T , t} (f , p) (g , q)
    = (f - g)
    , ((f - g) - t ~< coco _ _ _ ]~
       f - (g - t) ~[ coex rS q >~
       f - s ~[ p >~
       r [SQED])
  qe (Cat.coex _/_ (eq (q , <>)) (eq (q' , <>))) = qe (coex (eq q) (eq q')) , <>
  qe (Cat.idco _/_ _) = qe (idco _) , <>
  qe (Cat.coid _/_ _) = qe (coid _) , <>
  qe (Cat.coco _/_ _ _ _) = qe (coco _ _ _) , <>

module BWD (X : Set) where
  data Bwd : Set where
    _-,_ : Bwd -> X -> Bwd
    [] : Bwd
  infixl 30 _-,_

module _ {X : Set} where
  open BWD X

  data _<=_ : Bwd -> Bwd -> Set where
    _-^_ : forall {ga de} -> ga <= de -> forall x -> ga <= (de -, x)
    _-,_ : forall {ga de} -> ga <= de -> forall x -> (ga -, x) <= (de -, x)
    []   : [] <= []
  infixl 30 _-^_

  data <_-_>~_ : forall {ga de ze}(th : ga <= de)(ph : de <= ze)(ps : ga <= ze) -> Set where
    _-^_  : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
            < th - ph >~ ps -> forall x -> < th - ph -^ x >~ ps -^ x
    _-^,_ : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
            < th - ph >~ ps -> forall x -> < th -^ x - ph -, x >~ ps -^ x
    _-,_  : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
            < th - ph >~ ps -> forall x -> < th -, x - ph -, x >~ ps -, x
    []    : < [] - [] >~ []
  infix 25 <_-_>~_
  infixl 30 _-^,_

  io : forall {ga} -> ga <= ga
  io {ga -, x} = io {ga} -, x
  io {[]} = []

  mkCo : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> <(< th - ph >~_)>
  mkCo th         (ph -^ x) = let _ , v = mkCo th ph in _ , v -^ x
  mkCo (th -^ .x) (ph -, x) = let _ , v = mkCo th ph in _ , v -^, x
  mkCo (th -, .x) (ph -, x) = let _ , v = mkCo th ph in _ , v -, x
  mkCo []         []        = _ , []

  _~-~_ : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps0 ps1 : ga <= ze} ->
          (v0 : < th - ph >~ ps0)(v1 : < th - ph >~ ps1) ->
          (ps0 ~ ps1) >< \ { r~ -> v0 ~ v1 }
  (v0 -^ x)  ~-~ (v1 -^ .x)   with r~ , r~ <- v0 ~-~ v1 = r~ , r~
  (v0 -^, x) ~-~ (v1 -^, .x)  with r~ , r~ <- v0 ~-~ v1 = r~ , r~
  (v0 -, x)  ~-~ (v1 -, .x)   with r~ , r~ <- v0 ~-~ v1 = r~ , r~
  []         ~-~ []                                     = r~ , r~

  _-<=_ : forall {ga de ze} -> ga <= de -> de <= ze -> ga <= ze
  th -<= ph = fst (mkCo th ph)

  io- : forall {ga de}(th : ga <= de) -> < io - th >~ th
  io- (th -^ x) = io- th -^ x
  io- (th -, x) = io- th -, x
  io- [] = []

  infixl 30 _-io
  _-io : forall {ga de}(th : ga <= de) -> < th - io >~ th
  th -^ x -io = th -io -^, x
  th -, x -io = th -io -, x
  [] -io = []

  assoc02 : forall {ga0 ga1 ga2 ga3}
              {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
              {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
              <(< th01 -_>~ th03)  :* (< th12 - th23 >~_)> ->
              <(< th01 - th12 >~_) :* (<_- th23 >~ th03)>
  assoc02 (v -^ .x & w -^ x) = let v' & w' = assoc02 (v & w) in v' & w' -^ x
  assoc02 (v -^ .x & w -^, x) = let v' & w' = assoc02 (v & w) in v' -^ x & w' -^, x
  assoc02 (v -^, .x & w -, x) = let v' & w' = assoc02 (v & w) in v' -^, x & w' -^, x
  assoc02 (v -, .x & w -, x) = let v' & w' = assoc02 (v & w) in v' -, x & w' -, x
  assoc02 ([] & []) = [] & []

  assoc03 : forall {ga0 ga1 ga2 ga3}
              {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
              {th02 : ga0 <= ga2}{th13 : ga1 <= ga3} ->
              <(< th01 -_>~ th02)  :* (<_- th23 >~ th13)> ->
              <(< th01 - th13 >~_) :* (< th02 - th23 >~_)>
  assoc03 {th01 = th}{th13 = ph} (v & w) with _ , v' <- mkCo th ph |
    v0 & v1 <- assoc02 (v' & w) | r~ , r~ <- v ~-~ v0 = v' & v1

  assoc13 : forall {ga0 ga1 ga2 ga3}
              {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
              {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
              <(< th01 - th12 >~_)  :* (<_- th23 >~ th03)> ->
              <(< th01 -_>~ th03) :* (< th12 - th23 >~_)>
  assoc13 {th23 = ph}{th12 = th} (v & w) with  _ , v' <- mkCo th ph |
    v0 & v1 <- assoc03 (v & v') | r~ , r~ <- w ~-~ v1 = v0 & v'

  THIN : Cat lzero lzero
  Cat.Obj  THIN = Bwd
  Cat.Arr  THIN ga de = IN (ga <= de)
  Cat.id   THIN = io
  Cat._-_  THIN = _-<=_
  Cat.coex THIN (eq r~) (eq r~) = eq r~
  Cat.idco THIN th with v <- io- th | _ , w <- mkCo io th | r~ , r~ <- v ~-~ w
    = rS
  Cat.coid THIN ph with v <- ph -io | _ , w <- mkCo ph io | r~ , r~ <- v ~-~ w
    = rS
  Cat.coco THIN th ph ps with thph , v <- mkCo th ph | phps , w <- mkCo ph ps |
    _ , v1 <- mkCo thph ps | _ , w1 <- mkCo th phps |
    v2 & w2 <- assoc02 (w1 & w) | r~ , r~ <- v ~-~ v2 | r~ , r~ <- v1 ~-~ w2
    = rS

  THIN/ : Bwd -> Cat lzero lzero
  Cat.Obj (THIN/ de) = <(_<= de)>
  Cat.Arr (THIN/ de) (_ , th0) (_ , th1) = EX (IN _) (<_- th1 >~ th0)
  Cat.id (THIN/ de) = io , io- _
  Cat._-_ (THIN/ de) (th0 , v0) (th1 , v1) with w0 & w1 <- assoc02 (v0 & v1)
    = _ , w1
  qe (Cat.coex (THIN/ de) {f = _ , v0} {._ , w0} {_ , v1} {._ , w1}
    (eq (r~ , <>)) (eq (r~ , <>))) with
    (r~ , r~) , (r~ , r~) <- v0 ~-~ w0 /\ v1 ~-~ w1
    = r~ , <>
  qe (Cat.idco (THIN/ de) {_ , ph} (th , v)) with
    w <- io- th | w' & _ <- assoc02 (io- ph & v) | r~ , r~ <- w ~-~ w'
    = r~ , <>
  qe (Cat.coid (THIN/ de) {T = _ , ph} (th , v)) with
    w <- th -io | w' & _ <- assoc02 (v & io- ph) | r~ , r~ <- w ~-~ w'
    = r~ , <>
  qe (Cat.coco (THIN/ de) (_ , v01) (_ , v12) (_ , v23)) with
    w13  & v13  <- assoc02 (v12 & v23) | w02  & v02  <- assoc02 (v01 & v12) |
    w013 & v013 <- assoc02 (v01 & v13) | w023 & v023 <- assoc02 (v02 & v23) |
    w013' & w023' <- assoc03 (w02 & w13) |
    (r~ , r~) , (r~ , r~) <- w013' ~-~ w013 /\ w023' ~-~ w023
    = r~ , <>
