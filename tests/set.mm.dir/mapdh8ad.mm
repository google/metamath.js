include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "cotp.mm"
include "wceq.mm"
include "csn.mm"
include "eldifad.mm"
include "dvh3dim2.mm"
include "w3a.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "eqidd.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspprcl.mm"
include "simp2.mm"
include "simp3l.mm"
include "lssneln0.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simprd.mm"
include "necomd.mm"
include "simpl1.mm"
include "syl.mm"
include "simpl2.mm"
include "simpr.mm"
include "prcom.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "lspexch.mm"
include "mtand.mm"
include "simp3r.mm"
include "mapdh8ac.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem mapdh8ad
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
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
  let cZ: class Z
  let cB: class B
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
  assume mapdh8ac.f: |- ( ph -> F e. D )
  assume mapdh8ac.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8ac.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8ac.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = E )
  assume mapdh8ac.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8ac.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8ac.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh8ac.t: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8ac.yn: |- ( ph -> ( N ` { X } ) = ( N ` { T } ) )
  assume mapdh8ad.xy: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdh8ad.xz: |- ( ph -> ( N ` { X } ) =/= ( N ` { Z } ) )

  disjoint h x
  disjoint I x
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
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  disjoint B h
  disjoint B x
  disjoint h w
  disjoint w x
  disjoint E w
  disjoint G w
  disjoint I w
  disjoint N w
  disjoint T w
  disjoint U w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint Z w
  disjoint ph w
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. Z , E , T >. ) )

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
    @0
    cX
    cZ
    cpr
    cN
    cfv
    wcel
    #
    wn
    #
    wa
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
    cZ
    cE
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
    cZ
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
    mapdh8ac.x
    eldifad
    #
    wph
    cY
    cV
    @8
    mapdh8ac.y
    eldifad
    #
    wph
    cZ
    cV
    @8
    mapdh8ac.z
    eldifad
    #
    dvh3dim2
    wph
    @6
    @7
    vw
    cV
    wph
    @0
    cV
    wcel
    #
    @6
    w3a
    #
    vx
    vw
    cX
    cF
    @0
    cotp
    cI
    cfv
    #
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cE
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
    @12
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @6
    mapdh8a.k
    3ad2ant1
    wph
    @12
    cF
    cD
    wcel
    @6
    mapdh8ac.f
    3ad2ant1
    wph
    @12
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
    @6
    mapdh8ac.mn
    3ad2ant1
    wph
    @12
    cX
    cF
    cY
    cotp
    cI
    cfv
    cG
    wceq
    @6
    mapdh8ac.eg
    3ad2ant1
    wph
    @12
    cX
    cF
    cZ
    cotp
    cI
    cfv
    cE
    wceq
    @6
    mapdh8ac.ee
    3ad2ant1
    wph
    @12
    cX
    cV
    @8
    cdif
    #
    wcel
    #
    @6
    mapdh8ac.x
    3ad2ant1
    wph
    @12
    cY
    @16
    wcel
    @6
    mapdh8ac.y
    3ad2ant1
    wph
    @12
    cZ
    @16
    wcel
    @6
    mapdh8ac.z
    3ad2ant1
    wph
    @12
    cT
    @16
    wcel
    @6
    mapdh8ac.t
    3ad2ant1
    wph
    @12
    @15
    cT
    csn
    cN
    cfv
    wceq
    @6
    mapdh8ac.yn
    3ad2ant1
    @13
    @14
    eqidd
    @13
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
    @18
    eqid
    #
    wph
    @12
    cU
    clmod
    wcel
    @6
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
    @12
    @1
    @18
    wcel
    @6
    wph
    @18
    cN
    cV
    cU
    cX
    cY
    mapdh8a.v
    @19
    mapdh8a.n
    @20
    @9
    @10
    lspprcl
    3ad2ant1
    wph
    @12
    @6
    simp2
    #
    wph
    @12
    @3
    @5
    simp3l
    #
    lssneln0
    @13
    @0
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    @13
    @23
    @15
    wne
    #
    @23
    @24
    wne
    @13
    cN
    cV
    cU
    @0
    cX
    cY
    mapdh8a.v
    mapdh8a.n
    wph
    @12
    cU
    clvec
    wcel
    #
    @6
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
    3ad2ant1
    #
    @21
    wph
    @12
    cX
    cV
    wcel
    @6
    @9
    3ad2ant1
    #
    wph
    @12
    cY
    cV
    wcel
    #
    @6
    @10
    3ad2ant1
    @22
    lspindpi
    simprd
    necomd
    @13
    cX
    cY
    @0
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    @2
    @22
    @13
    @33
    wa
    #
    cN
    cV
    cU
    cX
    @0
    c.0
    cY
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    @34
    wph
    @26
    wph
    @12
    @6
    @33
    simpl1
    #
    @27
    syl
    @34
    wph
    @17
    @35
    mapdh8ac.x
    syl
    wph
    @12
    @6
    @33
    simpl2
    @34
    wph
    @30
    @35
    @10
    syl
    @34
    wph
    @15
    @24
    wne
    @35
    mapdh8ad.xy
    syl
    @34
    cX
    @32
    @0
    cY
    cpr
    #
    cN
    cfv
    @13
    @33
    simpr
    @31
    @36
    cN
    cY
    @0
    prcom
    fveq2i
    syl6eleq
    lspexch
    mtand
    @13
    @25
    @23
    cZ
    csn
    cN
    cfv
    #
    wne
    @13
    cN
    cV
    cU
    @0
    cX
    cZ
    mapdh8a.v
    mapdh8a.n
    @28
    @21
    @29
    wph
    @12
    cZ
    cV
    wcel
    #
    @6
    @11
    3ad2ant1
    wph
    @12
    @3
    @5
    simp3r
    #
    lspindpi
    simprd
    @13
    cX
    @0
    cZ
    cpr
    cN
    cfv
    wcel
    #
    @4
    @39
    @13
    @40
    wa
    #
    cN
    cV
    cU
    cX
    @0
    c.0
    cZ
    mapdh8a.v
    mapdh8a.o
    mapdh8a.n
    @41
    wph
    @26
    wph
    @12
    @6
    @40
    simpl1
    #
    @27
    syl
    @41
    wph
    @17
    @42
    mapdh8ac.x
    syl
    wph
    @12
    @6
    @40
    simpl2
    @41
    wph
    @38
    @42
    @11
    syl
    @41
    wph
    @15
    @37
    wne
    @42
    mapdh8ad.xz
    syl
    @13
    @40
    simpr
    lspexch
    mtand
    mapdh8ac
    rexlimdv3a
    mpd
end
