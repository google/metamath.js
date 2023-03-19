include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "dvhlvec.mm"
include "csn.mm"
include "eldifad.mm"
include "lspindp5.mm"
include "prcom.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "cdif.mm"
include "wne.mm"
include "simpr.mm"
include "lspexch.mm"
include "ex.mm"
include "syl5bi.mm"
include "mtod.mm"
include "mapdh8a.mm"

theorem mapdh8b
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
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
  let cF: class F
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
  assume mapdh8b.f: |- ( ph -> G e. D )
  assume mapdh8b.mn: |- ( ph -> ( M ` ( N ` { Y } ) ) = ( J ` { G } ) )
  assume mapdh8b.a: |- ( ph -> ( I ` <. Y , G , w >. ) = E )
  assume mapdh8b.x: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8b.y: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh8b.yz: |- ( ph -> ( N ` { w } ) =/= ( N ` { T } ) )
  assume mapdh8b.xt: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8b.vw: |- ( ph -> ( N ` { Y } ) =/= ( N ` { w } ) )
  assume mapdh8b.e: |- ( ph -> X e. ( N ` { Y , T } ) )
  assume mapdh8b.xn: |- ( ph -> -. X e. ( N ` { Y , w } ) )

  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint .0. h
  disjoint .0. x
  disjoint C h
  disjoint D h
  disjoint D x
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
  disjoint E h
  disjoint E x
  disjoint h w
  disjoint w x
  disjoint F h
  disjoint F x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. w , E , T >. ) = ( I ` <. Y , G , T >. ) )

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
    cG
    cE
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cY
    vw
    cv
    #
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
    mapdh8b.f
    mapdh8b.mn
    mapdh8b.a
    mapdh8b.x
    mapdh8b.y
    mapdh8b.yz
    mapdh8b.xt
    wph
    cY
    @0
    cT
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    cT
    cY
    @0
    cpr
    cN
    cfv
    wcel
    #
    wph
    cT
    cN
    cV
    cU
    cY
    @0
    cX
    mapdh8a.v
    mapdh8a.n
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlvec
    #
    wph
    cY
    cV
    c.0
    csn
    #
    mapdh8b.x
    eldifad
    wph
    @0
    cV
    @6
    mapdh8b.y
    eldifad
    #
    wph
    cT
    cV
    @6
    mapdh8b.xt
    eldifad
    #
    mapdh8b.e
    mapdh8b.xn
    lspindp5
    @3
    cY
    cT
    @0
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wph
    @4
    @2
    @10
    cY
    @1
    @9
    cN
    @0
    cT
    prcom
    fveq2i
    eleq2i
    wph
    @11
    @4
    wph
    @11
    wa
    cN
    cV
    cU
    cY
    cT
    c.0
    @0
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    wph
    cU
    clvec
    wcel
    @11
    @5
    adantr
    wph
    cY
    cV
    @6
    cdif
    wcel
    @11
    mapdh8b.x
    adantr
    wph
    cT
    cV
    wcel
    @11
    @8
    adantr
    wph
    @0
    cV
    wcel
    @11
    @7
    adantr
    wph
    cY
    csn
    cN
    cfv
    @0
    csn
    cN
    cfv
    wne
    @11
    mapdh8b.vw
    adantr
    wph
    @11
    simpr
    lspexch
    ex
    syl5bi
    mtod
    mapdh8a
end
