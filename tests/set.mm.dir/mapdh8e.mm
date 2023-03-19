include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
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
include "wne.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "simp2.mm"
include "simp3.mm"
include "lssneln0.mm"
include "wss.mm"
include "dvhlvec.mm"
include "prcom.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "lspexch.mm"
include "lspsnel5a.mm"
include "adantr.mm"
include "simpr.mm"
include "lspsnel5.mm"
include "biimprd.mm"
include "con3d.mm"
include "3impia.mm"
include "nssne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "clvec.mm"
include "lspindpi.mm"
include "simprd.mm"
include "lspindp2l.mm"
include "mapdh8d.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem mapdh8e
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
  let vw: setvar w
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
  assume mapdh8e.f: |- ( ph -> F e. D )
  assume mapdh8e.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8e.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8e.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8e.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8e.t: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8e.xy: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdh8e.xt: |- ( ph -> ( N ` { X } ) =/= ( N ` { T } ) )
  assume mapdh8e.yt: |- ( ph -> ( N ` { Y } ) =/= ( N ` { T } ) )
  assume mapdh8e.e: |- ( ph -> X e. ( N ` { Y , T } ) )

  disjoint V h
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
  disjoint I x
  disjoint F w
  disjoint G w
  disjoint I w
  disjoint N w
  disjoint T w
  disjoint U w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint ph w
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  disjoint h w
  disjoint w x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. X , F , T >. ) )

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
    #
    wn
    #
    vw
    cV
    wrex
    cY
    cG
    cT
    cotp
    cI
    cfv
    cX
    cF
    cT
    cotp
    cI
    cfv
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
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.n
    mapdh8a.k
    wph
    cX
    cV
    c.0
    csn
    #
    mapdh8e.x
    eldifad
    #
    wph
    cY
    cV
    @5
    mapdh8e.y
    eldifad
    #
    dvh3dim
    wph
    @3
    @4
    vw
    cV
    wph
    @0
    cV
    wcel
    #
    @3
    w3a
    #
    vx
    vw
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
    @8
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    mapdh8a.k
    3ad2ant1
    wph
    @8
    cF
    cD
    wcel
    @3
    mapdh8e.f
    3ad2ant1
    wph
    @8
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
    @3
    mapdh8e.mn
    3ad2ant1
    wph
    @8
    cX
    cF
    cY
    cotp
    cI
    cfv
    cG
    wceq
    @3
    mapdh8e.eg
    3ad2ant1
    wph
    @8
    cX
    cV
    @5
    cdif
    #
    wcel
    @3
    mapdh8e.x
    3ad2ant1
    #
    wph
    @8
    cY
    @11
    wcel
    @3
    mapdh8e.y
    3ad2ant1
    wph
    @8
    cT
    @11
    wcel
    @3
    mapdh8e.t
    3ad2ant1
    wph
    @8
    cY
    csn
    cN
    cfv
    #
    cT
    csn
    cN
    cfv
    #
    wne
    @3
    mapdh8e.yt
    3ad2ant1
    @9
    cU
    clss
    cfv
    #
    @1
    cV
    cU
    @0
    c.0
    mapdh8a.v
    mapdh8a.o
    @15
    eqid
    #
    wph
    @8
    cU
    clmod
    wcel
    #
    @3
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlmod
    #
    3ad2ant1
    wph
    @8
    @1
    @15
    wcel
    #
    @3
    wph
    @15
    cN
    cV
    cU
    cX
    cY
    mapdh8a.v
    @16
    mapdh8a.n
    @18
    @6
    @7
    lspprcl
    #
    3ad2ant1
    wph
    @8
    @3
    simp2
    #
    wph
    @8
    @3
    simp3
    #
    lssneln0
    @9
    @14
    @0
    csn
    cN
    cfv
    #
    @9
    @14
    @1
    wss
    #
    @23
    @1
    wss
    #
    wn
    #
    @14
    @23
    wne
    wph
    @8
    @24
    @3
    wph
    @15
    @1
    cN
    cU
    cT
    @16
    mapdh8a.n
    @18
    @20
    wph
    cN
    cV
    cU
    cX
    cT
    c.0
    cY
    mapdh8a.v
    mapdh8a.o
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
    mapdh8e.x
    wph
    cT
    cV
    @5
    mapdh8e.t
    eldifad
    @7
    mapdh8e.xy
    wph
    cX
    cY
    cT
    cpr
    #
    cN
    cfv
    cT
    cY
    cpr
    #
    cN
    cfv
    mapdh8e.e
    @28
    @29
    cN
    cY
    cT
    prcom
    fveq2i
    syl6eleq
    lspexch
    lspsnel5a
    3ad2ant1
    wph
    @8
    @3
    @26
    wph
    @8
    wa
    #
    @25
    @2
    @30
    @2
    @25
    @30
    @15
    @1
    cN
    cV
    cU
    @0
    mapdh8a.v
    @16
    mapdh8a.n
    wph
    @17
    @8
    @18
    adantr
    wph
    @19
    @8
    @20
    adantr
    wph
    @8
    simpr
    lspsnel5
    biimprd
    con3d
    3impia
    @14
    @23
    @1
    nssne2
    syl2anc
    necomd
    wph
    @8
    @10
    @14
    wne
    @3
    mapdh8e.xt
    3ad2ant1
    @9
    @23
    @13
    @9
    @23
    @10
    wne
    @23
    @13
    wne
    @9
    cN
    cV
    cU
    @0
    cX
    cY
    mapdh8a.v
    mapdh8a.n
    wph
    @8
    cU
    clvec
    wcel
    @3
    @27
    3ad2ant1
    #
    @21
    wph
    @8
    cX
    cV
    wcel
    @3
    @6
    3ad2ant1
    wph
    @8
    cY
    cV
    wcel
    @3
    @7
    3ad2ant1
    #
    @22
    lspindpi
    simprd
    necomd
    @9
    @13
    @23
    wne
    cX
    cY
    @0
    cpr
    cN
    cfv
    wcel
    wn
    @9
    cN
    cV
    cU
    cX
    cY
    c.0
    @0
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    @31
    @12
    @32
    @21
    wph
    @8
    @10
    @13
    wne
    @3
    mapdh8e.xy
    3ad2ant1
    @22
    lspindp2l
    simprd
    mapdh8d
    rexlimdv3a
    mpd
end
