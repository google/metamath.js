include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "wrex.mm"
include "wa.mm"
include "w3a.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "csn.mm"
include "cdif.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspprcl.mm"
include "simp2l.mm"
include "simp3l.mm"
include "lssneln0.mm"
include "simp2r.mm"
include "simp3r.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "simprd.mm"
include "mapdh8.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "wb.mm"
include "dvh3dim.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "mapdhcl.mm"
include "co.mm"
include "eqidd.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "ex.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"
include "weq.mm"
include "eleq1.mm"
include "notbid.mm"
include "oteq1.mm"
include "oteq3.mm"
include "fveq2d.mm"
include "oteq2d.mm"
include "eqtrd.mm"
include "reusv3.mm"
include "syl.mm"
include "reusv1.mm"
include "mpbird.mm"

theorem mapdh9aOLDN
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
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
  let c.0: class .0.
  let cG: class G
  let cY: class Y
  let cE: class E
  let cZ: class Z
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
  assume mapdh8h.f: |- ( ph -> F e. D )
  assume mapdh8h.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh9a.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh9a.t: |- ( ph -> T e. V )

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
  disjoint I x
  disjoint V h
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F y
  disjoint F z
  disjoint I y
  disjoint I z
  disjoint N y
  disjoint N z
  disjoint .0. y
  disjoint .0. z
  disjoint T y
  disjoint T z
  disjoint U z
  disjoint V y
  disjoint V z
  disjoint X y
  disjoint X z
  disjoint ph y
  disjoint ph z
  disjoint h z
  disjoint x z
  disjoint G h
  disjoint G x
  disjoint Y h
  disjoint Y x
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  disjoint h w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint F w
  disjoint I w
  disjoint N w
  disjoint .0. w
  disjoint T w
  disjoint V w
  disjoint X w
  disjoint ph w
  assert |- ( ph -> E! y e. D A. z e. V ( -. z e. ( N ` { X , T } ) -> y = ( I ` <. z , ( I ` <. X , F , z >. ) , T >. ) ) )

  proof
    wph
    vz
    cv
    #
    cX
    cT
    cpr
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vy
    cv
    @0
    cX
    cF
    @0
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    wceq
    wi
    vz
    cV
    wral
    #
    vy
    cD
    wreu
    #
    @8
    vy
    cD
    wrex
    #
    wph
    @3
    vw
    cv
    #
    @1
    wcel
    #
    wn
    #
    wa
    #
    @7
    @11
    cX
    cF
    @11
    cotp
    #
    cI
    cfv
    #
    cT
    cotp
    #
    cI
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cV
    wral
    vz
    cV
    wral
    #
    @10
    wph
    @20
    vz
    vw
    cV
    cV
    wph
    @0
    cV
    wcel
    #
    @11
    cV
    wcel
    #
    wa
    #
    @14
    @19
    wph
    @24
    @14
    w3a
    #
    vx
    cC
    cD
    cQ
    cR
    cT
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
    @0
    c.0
    @11
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
    @24
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @14
    mapdh8a.k
    3ad2ant1
    wph
    @24
    cF
    cD
    wcel
    #
    @14
    mapdh8h.f
    3ad2ant1
    wph
    @24
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
    #
    @14
    mapdh8h.mn
    3ad2ant1
    wph
    @24
    cX
    cV
    c.0
    csn
    #
    cdif
    wcel
    #
    @14
    mapdh9a.x
    3ad2ant1
    @25
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
    @32
    eqid
    #
    wph
    @24
    cU
    clmod
    wcel
    #
    @14
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
    #
    wph
    @24
    @1
    @32
    wcel
    #
    @14
    wph
    @32
    cN
    cV
    cU
    cX
    cT
    mapdh8a.v
    @33
    mapdh8a.n
    @35
    wph
    cX
    cV
    @30
    mapdh9a.x
    eldifad
    #
    mapdh9a.t
    lspprcl
    #
    3ad2ant1
    #
    wph
    @22
    @23
    @14
    simp2l
    #
    wph
    @24
    @3
    @13
    simp3l
    #
    lssneln0
    @25
    @32
    @1
    cV
    cU
    @11
    c.0
    mapdh8a.v
    mapdh8a.o
    @33
    @36
    @40
    wph
    @22
    @23
    @14
    simp2r
    #
    wph
    @24
    @3
    @13
    simp3r
    #
    lssneln0
    @25
    @0
    csn
    cN
    cfv
    #
    @28
    @25
    @45
    @28
    wne
    #
    @45
    cT
    csn
    cN
    cfv
    #
    wne
    #
    @25
    cN
    cV
    cU
    @0
    cX
    cT
    mapdh8a.v
    mapdh8a.n
    wph
    @24
    cU
    clvec
    wcel
    #
    @14
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
    @41
    wph
    @24
    cX
    cV
    wcel
    #
    @14
    @38
    3ad2ant1
    #
    wph
    @24
    cT
    cV
    wcel
    #
    @14
    mapdh9a.t
    3ad2ant1
    #
    @42
    lspindpi
    #
    simpld
    necomd
    @25
    @11
    csn
    cN
    cfv
    #
    @28
    @25
    @57
    @28
    wne
    #
    @57
    @47
    wne
    #
    @25
    cN
    cV
    cU
    @11
    cX
    cT
    mapdh8a.v
    mapdh8a.n
    @51
    @43
    @53
    @55
    @44
    lspindpi
    #
    simpld
    necomd
    @25
    @46
    @48
    @56
    simprd
    @25
    @58
    @59
    @60
    simprd
    @55
    mapdh8
    3exp
    ralrimivv
    wph
    @3
    @7
    cD
    wcel
    #
    wa
    #
    vz
    cV
    wrex
    #
    @21
    @10
    wb
    wph
    @3
    vz
    cV
    wrex
    #
    @63
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cT
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.n
    mapdh8a.k
    @38
    mapdh9a.t
    dvh3dim
    #
    wph
    @3
    @62
    vz
    cV
    wph
    @22
    wa
    #
    @3
    @61
    @66
    @3
    @61
    @66
    @3
    wa
    #
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    @5
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    @0
    cT
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
    wph
    @26
    @22
    @3
    mapdh8a.k
    ad2antrr
    #
    @67
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
    @0
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
    @68
    wph
    @27
    @22
    @3
    mapdh8h.f
    ad2antrr
    #
    wph
    @29
    @22
    @3
    mapdh8h.mn
    ad2antrr
    #
    wph
    @31
    @22
    @3
    mapdh9a.x
    ad2antrr
    #
    wph
    @22
    @3
    simplr
    #
    @67
    @45
    @28
    @67
    @46
    @48
    @67
    cN
    cV
    cU
    @0
    cX
    cT
    mapdh8a.v
    mapdh8a.n
    wph
    @49
    @22
    @3
    @50
    ad2antrr
    @72
    wph
    @52
    @22
    @3
    @38
    ad2antrr
    wph
    @54
    @22
    @3
    mapdh9a.t
    ad2antrr
    #
    @66
    @3
    simpr
    #
    lspindpi
    #
    simpld
    necomd
    #
    mapdhcl
    #
    @67
    @45
    cM
    cfv
    @5
    csn
    cJ
    cfv
    wceq
    #
    cX
    @0
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    @5
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    @67
    @5
    @5
    wceq
    @78
    @79
    wa
    @67
    @5
    eqidd
    @67
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    @5
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
    @0
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
    @68
    @69
    @70
    @71
    @67
    @32
    @1
    cV
    cU
    @0
    c.0
    mapdh8a.v
    mapdh8a.o
    @33
    wph
    @34
    @22
    @3
    @35
    ad2antrr
    wph
    @37
    @22
    @3
    @39
    ad2antrr
    @72
    @74
    lssneln0
    #
    @77
    @76
    mapdheq
    mpbid
    simpld
    @80
    @73
    @67
    @46
    @48
    @75
    simprd
    mapdhcl
    ex
    ancld
    reximdva
    mpd
    @3
    @13
    vy
    vz
    vw
    cD
    cV
    @7
    @18
    vz
    vw
    weq
    #
    @2
    @12
    @0
    @11
    @1
    eleq1
    notbid
    @81
    @6
    @17
    cI
    @81
    @6
    @11
    @5
    cT
    cotp
    @17
    @0
    @11
    @5
    cT
    oteq1
    @81
    @5
    @16
    @11
    cT
    @81
    @4
    @15
    cI
    @0
    @11
    cX
    cF
    oteq3
    fveq2d
    oteq2d
    eqtrd
    fveq2d
    reusv3
    syl
    mpbid
    wph
    @64
    @9
    @10
    wb
    @65
    @3
    vy
    vz
    cD
    cV
    @7
    reusv1
    syl
    mpbird
end
