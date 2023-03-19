include "co.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "cdif.mm"
include "cpr.mm"
include "wn.mm"
include "simpr.mm"
include "mapdh6iN.mm"
include "wne.mm"
include "eqidd.mm"
include "mapdh6aN.mm"
include "pm2.61dane.mm"

theorem mapdh6jN
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
  let vw: setvar w
  let cG: class G
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
  assume mapdh6i.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh6i.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh6i.z: |- ( ph -> Z e. ( V \ { .0. } ) )

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
  disjoint .+b w
  disjoint F w
  disjoint I w
  disjoint N w
  disjoint .+ w
  disjoint U w
  disjoint h w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint Z w
  disjoint ph w
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
    #
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    c.pb
    co
    wceq
    cY
    csn
    cN
    cfv
    #
    cZ
    csn
    cN
    cfv
    #
    wph
    @2
    @3
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
    @4
    mapdh.k
    adantr
    wph
    cF
    cD
    wcel
    #
    @4
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
    @4
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
    @4
    mapdhcl.x
    adantr
    mapdh.p
    mapdh.a
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
    @4
    mapdh6i.xn
    adantr
    wph
    cY
    @8
    wcel
    #
    @4
    mapdh6i.y
    adantr
    wph
    cZ
    @8
    wcel
    #
    @4
    mapdh6i.z
    adantr
    wph
    @4
    simpr
    mapdh6iN
    wph
    @2
    @3
    wne
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
    @1
    cF
    @0
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
    @5
    @13
    mapdh.k
    adantr
    wph
    @6
    @13
    mapdhc.f
    adantr
    wph
    @7
    @13
    mapdh.mn
    adantr
    wph
    @9
    @13
    mapdhcl.x
    adantr
    mapdh.p
    mapdh.a
    wph
    @11
    @13
    mapdh6i.y
    adantr
    wph
    @12
    @13
    mapdh6i.z
    adantr
    wph
    @10
    @13
    mapdh6i.xn
    adantr
    wph
    @13
    simpr
    @14
    @0
    eqidd
    @14
    @1
    eqidd
    mapdh6aN
    pm2.61dane
end
