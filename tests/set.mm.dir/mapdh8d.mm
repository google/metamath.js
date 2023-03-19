include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "cotp.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "chlt.mm"
include "adantr.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "co.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "mapdh8a.mm"
include "cdif.mm"
include "simpr.mm"
include "wn.mm"
include "mapdh8b.mm"
include "eqidd.mm"
include "mapdh8c.mm"
include "eqtr3d.mm"
include "pm2.61dan.mm"

theorem mapdh8d
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
  assume mapdh8d.f: |- ( ph -> F e. D )
  assume mapdh8d.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8b.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8d.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8d.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8d.xt: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8d.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8d.w: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh8d.wt: |- ( ph -> ( N ` { w } ) =/= ( N ` { T } ) )
  assume mapdh8d.ut: |- ( ph -> ( N ` { X } ) =/= ( N ` { T } ) )
  assume mapdh8d.vw: |- ( ph -> ( N ` { Y } ) =/= ( N ` { w } ) )
  assume mapdh8d.xn: |- ( ph -> -. X e. ( N ` { Y , w } ) )

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
  disjoint h w
  disjoint w x
  disjoint I x
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. X , F , T >. ) )

  proof
    wph
    cX
    cY
    cT
    cpr
    cN
    cfv
    wcel
    #
    cY
    cG
    cT
    cotp
    cI
    cfv
    #
    cX
    cF
    cT
    cotp
    cI
    cfv
    #
    wceq
    wph
    @0
    wa
    #
    vw
    cv
    #
    cX
    cF
    @4
    cotp
    cI
    cfv
    #
    cT
    cotp
    cI
    cfv
    @1
    @2
    @3
    vx
    vw
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    @5
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
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    mapdh8a.k
    adantr
    #
    wph
    cG
    cD
    wcel
    @0
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cG
    cD
    mapdh8b.eg
    wph
    vx
    cC
    cD
    cQ
    cR
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
    mapdh8d.f
    mapdh8d.mn
    mapdh8d.x
    wph
    cY
    cV
    c.0
    csn
    #
    mapdh8d.y
    eldifad
    #
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wne
    @11
    @4
    csn
    cN
    cfv
    #
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    @4
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
    wph
    cX
    cV
    @9
    mapdh8d.x
    eldifad
    @10
    wph
    @4
    cV
    @9
    mapdh8d.w
    eldifad
    mapdh8d.xn
    lspindpi
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    adantr
    wph
    @12
    cM
    cfv
    cG
    csn
    cJ
    cfv
    wceq
    #
    @0
    wph
    @16
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
    cG
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    @8
    cG
    wceq
    #
    @16
    @17
    wa
    mapdh8b.eg
    wph
    vx
    cC
    cD
    cQ
    cR
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
    mapdh8d.f
    mapdh8d.mn
    mapdh8d.x
    mapdh8d.y
    @15
    @14
    mapdheq
    mpbid
    simpld
    adantr
    wph
    cY
    cG
    @4
    cotp
    cI
    cfv
    @5
    wceq
    @0
    wph
    vx
    cC
    cD
    cQ
    cR
    @4
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
    mapdh8d.f
    mapdh8d.mn
    mapdh8b.eg
    mapdh8d.x
    mapdh8d.y
    mapdh8d.vw
    mapdh8d.w
    mapdh8d.xn
    mapdh8a
    adantr
    wph
    cY
    cV
    @9
    cdif
    #
    wcel
    #
    @0
    mapdh8d.y
    adantr
    #
    wph
    @4
    @19
    wcel
    @0
    mapdh8d.w
    adantr
    #
    wph
    @13
    cT
    csn
    cN
    cfv
    #
    wne
    @0
    mapdh8d.wt
    adantr
    #
    wph
    cT
    @19
    wcel
    #
    @0
    mapdh8d.xt
    adantr
    #
    wph
    @12
    @13
    wne
    @0
    mapdh8d.vw
    adantr
    #
    wph
    @0
    simpr
    #
    wph
    cX
    cY
    @4
    cpr
    cN
    cfv
    wcel
    wn
    @0
    mapdh8d.xn
    adantr
    #
    mapdh8b
    @3
    vx
    vw
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    @5
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
    @7
    wph
    cF
    cD
    wcel
    #
    @0
    mapdh8d.f
    adantr
    wph
    @11
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    #
    @0
    mapdh8d.mn
    adantr
    @3
    @5
    eqidd
    wph
    cX
    @19
    wcel
    #
    @0
    mapdh8d.x
    adantr
    @21
    @26
    wph
    @12
    @23
    wne
    #
    @0
    mapdh8d.yz
    adantr
    @22
    @24
    wph
    @11
    @23
    wne
    @0
    mapdh8d.ut
    adantr
    @27
    @28
    @29
    mapdh8c
    eqtr3d
    wph
    @0
    wn
    #
    wa
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
    wph
    @6
    @34
    mapdh8a.k
    adantr
    wph
    @30
    @34
    mapdh8d.f
    adantr
    wph
    @31
    @34
    mapdh8d.mn
    adantr
    wph
    @18
    @34
    mapdh8b.eg
    adantr
    wph
    @32
    @34
    mapdh8d.x
    adantr
    wph
    @20
    @34
    mapdh8d.y
    adantr
    wph
    @33
    @34
    mapdh8d.yz
    adantr
    wph
    @25
    @34
    mapdh8d.xt
    adantr
    wph
    @34
    simpr
    mapdh8a
    pm2.61dan
end
