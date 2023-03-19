include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "co.mm"
include "cotp.mm"
include "wceq.mm"
include "csn.mm"
include "eldifad.mm"
include "dvh3dim.mm"
include "w3a.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "simp2.mm"
include "simp3.mm"
include "lssneln0.mm"
include "hdmap1l6h.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmap1l6i
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
  let vw: setvar w
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
  assume hdmap1l6i.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )


  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    vw
    cv
    #
    cX
    cY
    cpr
    cN
    cfv
    #
    wcel
    wn
    #
    vw
    cV
    wrex
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
    #
    wph
    vw
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.v
    hdmap1l6.n
    hdmap1l6.k
    wph
    cX
    cV
    c.0
    csn
    #
    hdmap1l6cl.x
    eldifad
    #
    wph
    cY
    cV
    @4
    hdmap1l6i.y
    eldifad
    #
    dvh3dim
    wph
    @2
    @3
    vw
    cV
    wph
    @0
    cV
    wcel
    #
    @2
    w3a
    #
    vw
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
    @7
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    hdmap1l6.k
    3ad2ant1
    wph
    @7
    cF
    cD
    wcel
    @2
    hdmap1l6.f
    3ad2ant1
    wph
    @7
    cX
    cV
    @4
    cdif
    #
    wcel
    @2
    hdmap1l6cl.x
    3ad2ant1
    wph
    @7
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
    @2
    hdmap1l6.mn
    3ad2ant1
    wph
    @7
    cX
    cY
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    @2
    hdmap1l6i.xn
    3ad2ant1
    wph
    @7
    cY
    csn
    cN
    cfv
    cZ
    csn
    cN
    cfv
    wceq
    @2
    hdmap1l6i.yz
    3ad2ant1
    wph
    @7
    cY
    @9
    wcel
    @2
    hdmap1l6i.y
    3ad2ant1
    wph
    @7
    cZ
    @9
    wcel
    @2
    hdmap1l6i.z
    3ad2ant1
    @8
    cU
    clss
    cfv
    #
    @1
    cV
    cU
    @0
    c.0
    hdmap1l6.v
    hdmap1l6c.o
    @10
    eqid
    #
    wph
    @7
    cU
    clmod
    wcel
    @2
    wph
    cU
    cH
    cK
    cW
    hdmap1l6.h
    hdmap1l6.u
    hdmap1l6.k
    dvhlmod
    #
    3ad2ant1
    wph
    @7
    @1
    @10
    wcel
    @2
    wph
    @10
    cN
    cV
    cU
    cX
    cY
    hdmap1l6.v
    @11
    hdmap1l6.n
    @12
    @5
    @6
    lspprcl
    3ad2ant1
    wph
    @7
    @2
    simp2
    wph
    @7
    @2
    simp3
    #
    lssneln0
    @13
    hdmap1l6h
    rexlimdv3a
    mpd
end
