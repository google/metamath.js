include "cotp.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "crio.mm"
include "cdif.mm"
include "adantr.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "mapdhval2.mm"
include "wreu.mm"
include "chlt.mm"
include "mapdpg.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "mapdhval0.mm"
include "lcd0vcl.mm"
include "pm2.61ne.mm"

theorem mapdhcl
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
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
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.h: |- H = ( LHyp ` K )
  assume mapdh.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh.v: |- V = ( Base ` U )
  assume mapdh.s: |- .- = ( -g ` U )
  assume mapdhc.o: |- .0. = ( 0g ` U )
  assume mapdh.n: |- N = ( LSpan ` U )
  assume mapdh.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh.d: |- D = ( Base ` C )
  assume mapdh.r: |- R = ( -g ` C )
  assume mapdh.j: |- J = ( LSpan ` C )
  assume mapdh.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhc.f: |- ( ph -> F e. D )
  assume mapdh.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdhcl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdhc.y: |- ( ph -> Y e. V )
  assume mapdh.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  disjoint .0. h
  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint U h
  disjoint .- h
  assert |- ( ph -> ( I ` <. X , F , Y >. ) e. D )

  proof
    wph
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    #
    cD
    wcel
    cX
    cF
    c.0
    cotp
    #
    cI
    cfv
    #
    cD
    wcel
    cY
    c.0
    cY
    c.0
    wceq
    #
    @1
    @3
    cD
    @4
    @0
    @2
    cI
    cY
    c.0
    cX
    cF
    oteq3
    fveq2d
    eleq1d
    wph
    cY
    c.0
    wne
    #
    wa
    #
    @1
    cY
    csn
    cN
    cfv
    #
    cM
    cfv
    vh
    cv
    #
    csn
    cJ
    cfv
    wceq
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    @8
    cR
    co
    csn
    cJ
    cfv
    wceq
    wa
    #
    vh
    cD
    crio
    #
    cD
    @6
    vx
    cV
    c.0
    csn
    cdif
    #
    cD
    cC
    cD
    cQ
    cR
    vh
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cV
    cX
    cY
    c.0
    mapdh.q
    mapdh.i
    wph
    cX
    @11
    wcel
    @5
    mapdhcl.x
    adantr
    #
    wph
    cF
    cD
    wcel
    @5
    mapdhc.f
    adantr
    #
    @6
    cY
    cV
    wcel
    #
    @5
    wa
    cY
    @11
    wcel
    wph
    @14
    @5
    mapdhc.y
    anim1i
    cY
    cV
    c.0
    eldifsn
    sylibr
    #
    mapdhval2
    @6
    @9
    vh
    cD
    wreu
    @10
    cD
    wcel
    @6
    cC
    cR
    cU
    vh
    cD
    cF
    cH
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
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    mapdh.k
    adantr
    @12
    @15
    @13
    wph
    cX
    csn
    cN
    cfv
    #
    @7
    wne
    @5
    mapdh.ne
    adantr
    wph
    @16
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    @5
    mapdh.mn
    adantr
    mapdpg
    @9
    vh
    cD
    riotacl
    syl
    eqeltrd
    wph
    @3
    cQ
    cD
    wph
    vx
    @11
    cD
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cI
    cJ
    cM
    c.mi
    cN
    cX
    c.0
    mapdh.q
    mapdh.i
    mapdhc.o
    mapdhcl.x
    mapdhc.f
    mapdhval0
    wph
    cC
    cH
    cK
    cQ
    cD
    cW
    mapdh.h
    mapdh.c
    mapdh.d
    mapdh.q
    mapdh.k
    lcd0vcl
    eqeltrd
    pm2.61ne
end
