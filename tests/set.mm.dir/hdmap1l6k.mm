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
include "hdmap1l6b.mm"
include "hdmap1l6c.mm"
include "wne.mm"
include "simprl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "hdmap1l6j.mm"
include "pm2.61da2ne.mm"

theorem hdmap1l6k
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmap1l6.h: |- H = ( LHyp ` K )
  assume hdmap1l6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1l6.v: |- V = ( Base ` U )
  assume hdmap1l6.p: |- .+ = ( +g ` U )
  assume hdmap1l6.s: |- .- = ( -g ` U )
  assume hdmap1l6c.o: |- .0. = ( 0g ` U )
  assume hdmap1l6.n: |- N = ( LSpan ` U )
  assume hdmap1l6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1l6.d: |- D = ( Base ` C )
  assume hdmap1l6.a: |- .+b = ( +g ` C )
  assume hdmap1l6.r: |- R = ( -g ` C )
  assume hdmap1l6.q: |- Q = ( 0g ` C )
  assume hdmap1l6.l: |- L = ( LSpan ` C )
  assume hdmap1l6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1l6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1l6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1l6.f: |- ( ph -> F e. D )
  assume hdmap1l6cl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1l6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )
  assume hdmap1l6k.y: |- ( ph -> Y e. V )
  assume hdmap1l6k.z: |- ( ph -> Z e. V )
  assume hdmap1l6k.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )


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
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
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
    hdmap1l6.k
    adantr
    wph
    cF
    cD
    wcel
    #
    @0
    hdmap1l6.f
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
    hdmap1l6cl.x
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
    cL
    cfv
    wceq
    #
    @0
    hdmap1l6.mn
    adantr
    wph
    @0
    simpr
    wph
    cZ
    cV
    wcel
    #
    @0
    hdmap1l6k.z
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
    hdmap1l6k.xn
    adantr
    hdmap1l6b
    wph
    cZ
    c.0
    wceq
    #
    wa
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    wph
    @1
    @8
    hdmap1l6.k
    adantr
    wph
    @2
    @8
    hdmap1l6.f
    adantr
    wph
    @4
    @8
    hdmap1l6cl.x
    adantr
    wph
    @5
    @8
    hdmap1l6.mn
    adantr
    wph
    cY
    cV
    wcel
    #
    @8
    hdmap1l6k.y
    adantr
    wph
    @8
    simpr
    wph
    @7
    @8
    hdmap1l6k.xn
    adantr
    hdmap1l6c
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
    cC
    cD
    c.pl
    c.pb
    cQ
    cR
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.p
    hdmap1l6.s
    hdmap1l6c.o
    hdmap1l6.n
    hdmap1l6.c
    hdmap1l6.d
    hdmap1l6.a
    hdmap1l6.r
    hdmap1l6.q
    hdmap1l6.l
    hdmap1l6.m
    hdmap1l6.i
    wph
    @1
    @12
    hdmap1l6.k
    adantr
    wph
    @2
    @12
    hdmap1l6.f
    adantr
    wph
    @4
    @12
    hdmap1l6cl.x
    adantr
    wph
    @5
    @12
    hdmap1l6.mn
    adantr
    wph
    @7
    @12
    hdmap1l6k.xn
    adantr
    @13
    @9
    @10
    cY
    @3
    wcel
    wph
    @9
    @12
    hdmap1l6k.y
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
    @3
    wcel
    wph
    @6
    @12
    hdmap1l6k.z
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
    hdmap1l6j
    pm2.61da2ne
end
