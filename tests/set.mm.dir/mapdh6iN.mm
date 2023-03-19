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
include "mapdh6hN.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem mapdh6iN
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
  assume mapdh6i.yz: |- ( ph -> ( N ` { Y } ) = ( N ` { Z } ) )

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
    mapdh.h
    mapdh.u
    mapdh.v
    mapdh.n
    mapdh.k
    wph
    cX
    cV
    c.0
    csn
    #
    mapdhcl.x
    eldifad
    #
    wph
    cY
    cV
    @4
    mapdh6i.y
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
    vx
    vw
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
    @7
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    mapdh.k
    3ad2ant1
    wph
    @7
    cF
    cD
    wcel
    @2
    mapdhc.f
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
    cJ
    cfv
    wceq
    @2
    mapdh.mn
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
    mapdhcl.x
    3ad2ant1
    mapdh.p
    mapdh.a
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
    mapdh6i.xn
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
    mapdh6i.yz
    3ad2ant1
    wph
    @7
    cY
    @9
    wcel
    @2
    mapdh6i.y
    3ad2ant1
    wph
    @7
    cZ
    @9
    wcel
    @2
    mapdh6i.z
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
    mapdh.v
    mapdhc.o
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
    mapdh.h
    mapdh.u
    mapdh.k
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
    mapdh.v
    @11
    mapdh.n
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
    mapdh6hN
    rexlimdv3a
    mpd
end
