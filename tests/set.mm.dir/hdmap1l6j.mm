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
include "hdmap1l6i.mm"
include "wne.mm"
include "eqidd.mm"
include "hdmap1l6a.mm"
include "pm2.61dane.mm"

theorem hdmap1l6j
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
  assume hdmap1l6i.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1l6i.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume hdmap1l6i.z: |- ( ph -> Z e. ( V \ { .0. } ) )


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
    @4
    hdmap1l6.k
    adantr
    wph
    cF
    cD
    wcel
    #
    @4
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
    @4
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
    @4
    hdmap1l6.mn
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
    @4
    hdmap1l6i.xn
    adantr
    wph
    cY
    @7
    wcel
    #
    @4
    hdmap1l6i.y
    adantr
    wph
    cZ
    @7
    wcel
    #
    @4
    hdmap1l6i.z
    adantr
    wph
    @4
    simpr
    hdmap1l6i
    wph
    @2
    @3
    wne
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
    @1
    cF
    @0
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
    @5
    @13
    hdmap1l6.k
    adantr
    wph
    @6
    @13
    hdmap1l6.f
    adantr
    wph
    @8
    @13
    hdmap1l6cl.x
    adantr
    wph
    @9
    @13
    hdmap1l6.mn
    adantr
    wph
    @11
    @13
    hdmap1l6i.y
    adantr
    wph
    @12
    @13
    hdmap1l6i.z
    adantr
    wph
    @10
    @13
    hdmap1l6i.xn
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
    hdmap1l6a
    pm2.61dane
end
