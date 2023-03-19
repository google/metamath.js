include "mapdh8a.mm"

theorem mapdh8fN
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vw: setvar w
  let cE: class E
  let cZ: class Z
  assume mapdh8a.h: |- H = ( LHyp ` K )
  assume mapdh8a.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh8a.v: |- V = ( Base ` U )
  assume mapdh8a.s: |- .- = ( -g ` U )
  assume mapdh8a.o: |- .0. = ( 0g ` U )
  assume mapdh8a.n: |- N = ( LSpan ` U )
  assume mapdh8a.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh8a.d: |- D = ( Base ` C )
  assume mapdh8a.r: |- R = ( -g ` C )
  assume mapdh8a.q: |- Q = ( 0g ` C )
  assume mapdh8a.j: |- J = ( LSpan ` C )
  assume mapdh8a.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh8a.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh8a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh8e.f: |- ( ph -> F e. D )
  assume mapdh8e.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8e.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8e.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8e.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8e.t: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8e.xy: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdh8e.xt: |- ( ph -> ( N ` { X } ) =/= ( N ` { T } ) )
  assume mapdh8e.yt: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8f.e: |- ( ph -> -. X e. ( N ` { Y , T } ) )

  disjoint V h
  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint .0. h
  disjoint .0. x
  disjoint C h
  disjoint D h
  disjoint D x
  disjoint F h
  disjoint F x
  disjoint I h
  disjoint G h
  disjoint G x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint h ph
  disjoint R h
  disjoint R x
  disjoint Q x
  disjoint T h
  disjoint T x
  disjoint U h
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint I x
  disjoint F w
  disjoint G w
  disjoint I w
  disjoint N w
  disjoint T w
  disjoint U w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint ph w
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  disjoint h w
  disjoint w x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. X , F , T >. ) )

  proof
    wph
    vx
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cF
    cG
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    mapdh8e.f
    mapdh8e.mn
    mapdh8e.eg
    mapdh8e.x
    mapdh8e.y
    mapdh8e.yt
    mapdh8e.t
    mapdh8f.e
    mapdh8a
end
