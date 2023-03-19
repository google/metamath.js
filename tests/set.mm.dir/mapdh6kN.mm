include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "simpr.mm"
include "cpr.mm"
include "wn.mm"
include "mapdh6bN.mm"
include "mapdh6cN.mm"
include "wne.mm"
include "simprl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "mapdh6jN.mm"
include "pm2.61da2ne.mm"

theorem mapdh6kN
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
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
  let cZ: class Z
  let cG: class G
  let vw: setvar w
  let cE: class E
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
  assume mapdh.p: |- .+ = ( +g ` U )
  assume mapdh.a: |- .+b = ( +g ` C )
  assume mapdh6k.y: |- ( ph -> Y e. V )
  assume mapdh6k.z: |- ( ph -> Z e. V )
  assume mapdh6k.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )

  disjoint V h
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
  disjoint Z h
  disjoint Z x
  disjoint .+b h
  disjoint I h
  disjoint I x
  disjoint .+ h
  disjoint .+ x
  disjoint G h
  disjoint h w
  disjoint G x
  disjoint E h
  disjoint w x
  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cX
    cF
    cY
    cZ
    c.pl
    co
    cotp
    cI
    cfv
    cX
    cF
    cY
    cotp
    cI
    cfv
    cX
    cF
    cZ
    cotp
    cI
    cfv
    c.pb
    co
    wceq
    cY
    c.0
    cZ
    c.0
    wph
    cY
    c.0
    wceq
    #
    wa
    vx
    cC
    cD
    c.pl
    c.pb
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
    cZ
    mapdh.q
    mapdh.i
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
    #
    @0
    mapdh.k
    adantr
    wph
    cF
    cD
    wcel
    #
    @0
    mapdhc.f
    adantr
    wph
    cX
    csn
    cN
    cfv
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    #
    @0
    mapdh.mn
    adantr
    wph
    cX
    cV
    c.0
    csn
    cdif
    #
    wcel
    #
    @0
    mapdhcl.x
    adantr
    mapdh.p
    mapdh.a
    wph
    @0
    simpr
    wph
    cZ
    cV
    wcel
    #
    @0
    mapdh6k.z
    adantr
    wph
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    #
    @0
    mapdh6k.xn
    adantr
    mapdh6bN
    wph
    cZ
    c.0
    wceq
    #
    wa
    vx
    cC
    cD
    c.pl
    c.pb
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
    cZ
    mapdh.q
    mapdh.i
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
    @1
    @8
    mapdh.k
    adantr
    wph
    @2
    @8
    mapdhc.f
    adantr
    wph
    @3
    @8
    mapdh.mn
    adantr
    wph
    @5
    @8
    mapdhcl.x
    adantr
    mapdh.p
    mapdh.a
    wph
    cY
    cV
    wcel
    #
    @8
    mapdh6k.y
    adantr
    wph
    @8
    simpr
    wph
    @7
    @8
    mapdh6k.xn
    adantr
    mapdh6cN
    wph
    cY
    c.0
    wne
    #
    cZ
    c.0
    wne
    #
    wa
    #
    wa
    #
    vx
    cC
    cD
    c.pl
    c.pb
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
    cZ
    mapdh.q
    mapdh.i
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
    @1
    @12
    mapdh.k
    adantr
    wph
    @2
    @12
    mapdhc.f
    adantr
    wph
    @3
    @12
    mapdh.mn
    adantr
    wph
    @5
    @12
    mapdhcl.x
    adantr
    mapdh.p
    mapdh.a
    wph
    @7
    @12
    mapdh6k.xn
    adantr
    @13
    @9
    @10
    cY
    @4
    wcel
    wph
    @9
    @12
    mapdh6k.y
    adantr
    wph
    @10
    @11
    simprl
    cY
    cV
    c.0
    eldifsn
    sylanbrc
    @13
    @6
    @11
    cZ
    @4
    wcel
    wph
    @6
    @12
    mapdh6k.z
    adantr
    wph
    @10
    @11
    simprr
    cZ
    cV
    c.0
    eldifsn
    sylanbrc
    mapdh6jN
    pm2.61da2ne
end
