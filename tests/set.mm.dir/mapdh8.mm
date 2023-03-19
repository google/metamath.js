include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "fvexd.mm"
include "mapdhval0.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "chlt.mm"
include "wcel.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "mapdh8j.mm"
include "pm2.61dane.mm"

theorem mapdh8
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
  let cZ: class Z
  let cG: class G
  let cE: class E
  let vw: setvar w
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
  assume mapdh8h.f: |- ( ph -> F e. D )
  assume mapdh8h.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8i.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8i.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8i.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh8i.xy: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdh8i.xz: |- ( ph -> ( N ` { X } ) =/= ( N ` { Z } ) )
  assume mapdh8i.yt: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8i.zt: |- ( ph -> ( N ` { Z } ) =/= ( N ` { T } ) )
  assume mapdh8.t: |- ( ph -> T e. V )

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
  disjoint Z h
  disjoint Z x
  disjoint I x
  disjoint V h
  disjoint G h
  disjoint G x
  disjoint E h
  disjoint E x
  disjoint h w
  disjoint w x
  assert |- ( ph -> ( I ` <. Y , ( I ` <. X , F , Y >. ) , T >. ) = ( I ` <. Z , ( I ` <. X , F , Z >. ) , T >. ) )

  proof
    wph
    cY
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    cZ
    cX
    cF
    cZ
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    wceq
    cT
    c.0
    wph
    cT
    c.0
    wceq
    #
    wa
    cY
    @1
    c.0
    cotp
    #
    cI
    cfv
    #
    cZ
    @5
    c.0
    cotp
    #
    cI
    cfv
    #
    @3
    @7
    wph
    @10
    @12
    wceq
    @8
    wph
    @10
    cQ
    @12
    wph
    vx
    cV
    c.0
    csn
    cdif
    #
    cvv
    cC
    cD
    cQ
    cR
    cU
    vh
    @1
    cI
    cJ
    cM
    c.mi
    cN
    cY
    c.0
    mapdh8a.q
    mapdh8a.i
    mapdh8a.o
    mapdh8i.y
    wph
    @0
    cI
    fvexd
    mapdhval0
    wph
    vx
    @13
    cvv
    cC
    cD
    cQ
    cR
    cU
    vh
    @5
    cI
    cJ
    cM
    c.mi
    cN
    cZ
    c.0
    mapdh8a.q
    mapdh8a.i
    mapdh8a.o
    mapdh8i.z
    wph
    @4
    cI
    fvexd
    mapdhval0
    eqtr4d
    adantr
    @8
    @3
    @10
    wceq
    wph
    @8
    @2
    @9
    cI
    cT
    c.0
    cY
    @1
    oteq3
    fveq2d
    adantl
    @8
    @7
    @12
    wceq
    wph
    @8
    @6
    @11
    cI
    cT
    c.0
    cZ
    @5
    oteq3
    fveq2d
    adantl
    3eqtr4d
    wph
    cT
    c.0
    wne
    #
    wa
    #
    vx
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cF
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
    cZ
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
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @14
    mapdh8a.k
    adantr
    wph
    cF
    cD
    wcel
    @14
    mapdh8h.f
    adantr
    wph
    cX
    csn
    cN
    cfv
    #
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    @14
    mapdh8h.mn
    adantr
    wph
    cX
    @13
    wcel
    @14
    mapdh8i.x
    adantr
    wph
    cY
    @13
    wcel
    @14
    mapdh8i.y
    adantr
    wph
    cZ
    @13
    wcel
    @14
    mapdh8i.z
    adantr
    wph
    @16
    cY
    csn
    cN
    cfv
    #
    wne
    @14
    mapdh8i.xy
    adantr
    wph
    @16
    cZ
    csn
    cN
    cfv
    #
    wne
    @14
    mapdh8i.xz
    adantr
    wph
    @17
    cT
    csn
    cN
    cfv
    #
    wne
    @14
    mapdh8i.yt
    adantr
    wph
    @18
    @19
    wne
    @14
    mapdh8i.zt
    adantr
    @15
    cT
    cV
    wcel
    #
    @14
    wa
    cT
    @13
    wcel
    wph
    @20
    @14
    mapdh8.t
    anim1i
    cT
    cV
    c.0
    eldifsn
    sylibr
    mapdh8j
    pm2.61dane
end
