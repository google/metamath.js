include "cotp.mm"
include "cfv.mm"
include "eqidd.mm"
include "mapdheq4.mm"

theorem mapdh8a
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
  assume mapdh8a.f: |- ( ph -> F e. D )
  assume mapdh8a.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8a.a: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8a.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8a.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8a.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8a.xt: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8a.xn: |- ( ph -> -. X e. ( N ` { Y , T } ) )

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
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. X , F , T >. ) )

  proof
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cX
    cF
    cT
    cotp
    cI
    cfv
    #
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
    cT
    mapdh8a.q
    mapdh8a.i
    mapdh8a.h
    mapdh8a.m
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.j
    mapdh8a.k
    mapdh8a.f
    mapdh8a.mn
    mapdh8a.x
    mapdh8a.y
    mapdh8a.xt
    mapdh8a.xn
    mapdh8a.yz
    mapdh8a.a
    wph
    @0
    eqidd
    mapdheq4
end
