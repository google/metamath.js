include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "wrex.mm"
include "cdif.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp3ll.mm"
include "simp3rl.mm"
include "simplrl.mm"
include "3ad2ant3.mm"
include "necomd.mm"
include "simprrl.mm"
include "simplrr.mm"
include "simprrr.mm"
include "mapdh8.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "wb.mm"
include "cpr.mm"
include "eldifad.mm"
include "dvh3dim.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "ad2antrr.mm"
include "lspprcl.mm"
include "simplr.mm"
include "simpr.mm"
include "lssneln0.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "mapdhcl.mm"
include "co.mm"
include "eqidd.mm"
include "simprl.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "simpld.mm"
include "ancld.mm"
include "weq.mm"
include "eleq1.mm"
include "sneq.mm"
include "fveq2d.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "oteq1.mm"
include "oteq3.mm"
include "oteq2d.mm"
include "eqtrd.mm"
include "reusv3.mm"
include "syl.mm"
include "wo.mm"
include "ioran.mm"
include "elun.mm"
include "xchnxbir.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnne2.mm"
include "anim12d.mm"
include "jcad.mm"
include "syl5bi.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "lspprid1.mm"
include "lspsnel5a.mm"
include "lspprid2.mm"
include "unssd.mm"
include "ssneld.mm"
include "reusv1.mm"
include "mpbird.mm"

theorem mapdh9a
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
  assert |- ( ph -> E! y e. D A. z e. V ( -. z e. ( ( N ` { X } ) u. ( N ` { T } ) ) -> y = ( I ` <. z , ( I ` <. X , F , z >. ) , T >. ) ) )

  proof
    wph
    vz
    cv
    #
    cX
    csn
    cN
    cfv
    #
    cT
    csn
    cN
    cfv
    #
    cun
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
    #
    wi
    #
    vz
    cV
    wral
    #
    vy
    cD
    wreu
    #
    @12
    vy
    cD
    wrex
    #
    wph
    @0
    cV
    c.0
    csn
    #
    cdif
    #
    wcel
    #
    @0
    csn
    #
    cN
    cfv
    #
    @1
    wne
    #
    @19
    @2
    wne
    #
    wa
    #
    wa
    #
    @10
    wi
    #
    vz
    cV
    wral
    #
    vy
    cD
    wrex
    #
    @14
    wph
    @23
    vw
    cv
    #
    @16
    wcel
    #
    @27
    csn
    #
    cN
    cfv
    #
    @1
    wne
    #
    @30
    @2
    wne
    #
    wa
    #
    wa
    #
    wa
    #
    @9
    @27
    cX
    cF
    @27
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
    @26
    wph
    @41
    vz
    vw
    cV
    cV
    wph
    @0
    cV
    wcel
    #
    @27
    cV
    wcel
    wa
    #
    @35
    @40
    wph
    @44
    @35
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
    @27
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
    @44
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @35
    mapdh8a.k
    3ad2ant1
    wph
    @44
    cF
    cD
    wcel
    #
    @35
    mapdh8h.f
    3ad2ant1
    wph
    @44
    @1
    cM
    cfv
    cF
    csn
    cJ
    cfv
    wceq
    #
    @35
    mapdh8h.mn
    3ad2ant1
    wph
    @44
    cX
    @16
    wcel
    #
    @35
    mapdh9a.x
    3ad2ant1
    @17
    @22
    @34
    wph
    @44
    simp3ll
    @28
    @33
    @23
    wph
    @44
    simp3rl
    @45
    @19
    @1
    @35
    wph
    @20
    @44
    @17
    @20
    @21
    @34
    simplrl
    3ad2ant3
    necomd
    @45
    @30
    @1
    @35
    wph
    @31
    @44
    @23
    @28
    @31
    @32
    simprrl
    3ad2ant3
    necomd
    @35
    wph
    @21
    @44
    @17
    @20
    @21
    @34
    simplrr
    3ad2ant3
    @35
    wph
    @32
    @44
    @23
    @28
    @31
    @32
    simprrr
    3ad2ant3
    wph
    @44
    cT
    cV
    wcel
    #
    @35
    mapdh9a.t
    3ad2ant1
    mapdh8
    3exp
    ralrimivv
    wph
    @23
    @9
    cD
    wcel
    #
    wa
    #
    vz
    cV
    wrex
    #
    @42
    @26
    wb
    wph
    @23
    vz
    cV
    wrex
    #
    @53
    wph
    @0
    cX
    cT
    cpr
    cN
    cfv
    #
    wcel
    wn
    #
    vz
    cV
    wrex
    #
    @54
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
    wph
    cX
    cV
    @15
    mapdh9a.x
    eldifad
    #
    mapdh9a.t
    dvh3dim
    #
    wph
    @56
    @23
    vz
    cV
    wph
    @43
    wa
    #
    @56
    @23
    @60
    @56
    wa
    #
    @17
    @22
    @61
    cU
    clss
    cfv
    #
    @55
    cV
    cU
    @0
    c.0
    mapdh8a.v
    mapdh8a.o
    @62
    eqid
    #
    wph
    cU
    clmod
    wcel
    #
    @43
    @56
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
    ad2antrr
    wph
    @55
    @62
    wcel
    @43
    @56
    wph
    @62
    cN
    cV
    cU
    cX
    cT
    mapdh8a.v
    @63
    mapdh8a.n
    @65
    @58
    mapdh9a.t
    lspprcl
    #
    ad2antrr
    wph
    @43
    @56
    simplr
    #
    @60
    @56
    simpr
    #
    lssneln0
    @61
    cN
    cV
    cU
    @0
    cX
    cT
    mapdh8a.v
    mapdh8a.n
    wph
    cU
    clvec
    wcel
    @43
    @56
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlvec
    ad2antrr
    @67
    wph
    cX
    cV
    wcel
    #
    @43
    @56
    @58
    ad2antrr
    wph
    @50
    @43
    @56
    mapdh9a.t
    ad2antrr
    @68
    lspindpi
    jca
    ex
    reximdva
    mpd
    wph
    @23
    @52
    vz
    cV
    @60
    @23
    @51
    @60
    @23
    @51
    @60
    @23
    wa
    #
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    @7
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
    @46
    @43
    @23
    mapdh8a.k
    ad2antrr
    #
    @70
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
    @71
    wph
    @47
    @43
    @23
    mapdh8h.f
    ad2antrr
    #
    wph
    @48
    @43
    @23
    mapdh8h.mn
    ad2antrr
    #
    wph
    @49
    @43
    @23
    mapdh9a.x
    ad2antrr
    #
    wph
    @43
    @23
    simplr
    @70
    @19
    @1
    @60
    @17
    @20
    @21
    simprrl
    necomd
    #
    mapdhcl
    #
    @70
    @19
    cM
    cfv
    @7
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
    @7
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    @70
    @7
    @7
    wceq
    @77
    @78
    wa
    @70
    @7
    eqidd
    @70
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    @7
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
    @71
    @72
    @73
    @74
    @60
    @17
    @22
    simprl
    #
    @76
    @75
    mapdheq
    mpbid
    simpld
    @79
    wph
    @50
    @43
    @23
    mapdh9a.t
    ad2antrr
    @60
    @17
    @20
    @21
    simprrr
    mapdhcl
    ex
    ancld
    reximdva
    mpd
    @23
    @34
    vy
    vz
    vw
    cD
    cV
    @9
    @39
    vz
    vw
    weq
    #
    @17
    @28
    @22
    @33
    @0
    @27
    @16
    eleq1
    @80
    @20
    @31
    @21
    @32
    @80
    @19
    @30
    @1
    @80
    @18
    @29
    cN
    @0
    @27
    sneq
    fveq2d
    #
    neeq1d
    @80
    @19
    @30
    @2
    @81
    neeq1d
    anbi12d
    anbi12d
    @80
    @8
    @38
    cI
    @80
    @8
    @27
    @7
    cT
    cotp
    @38
    @0
    @27
    @7
    cT
    oteq1
    @80
    @7
    @37
    @27
    cT
    @80
    @6
    @36
    cI
    @0
    @27
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
    @25
    @12
    vy
    cD
    wph
    @24
    @11
    vz
    cV
    @60
    @5
    @23
    @10
    @5
    @0
    @1
    wcel
    #
    wn
    #
    @0
    @2
    wcel
    #
    wn
    #
    wa
    #
    @60
    @23
    @82
    @84
    wo
    @86
    @4
    @82
    @84
    ioran
    @0
    @1
    @2
    elun
    xchnxbir
    @60
    @86
    @17
    @22
    @60
    @86
    @17
    @60
    @86
    wa
    @62
    @1
    cV
    cU
    @0
    c.0
    mapdh8a.v
    mapdh8a.o
    @63
    wph
    @64
    @43
    @86
    @65
    ad2antrr
    wph
    @1
    @62
    wcel
    #
    @43
    @86
    wph
    @64
    @69
    @87
    @65
    @58
    @62
    cN
    cV
    cU
    cX
    mapdh8a.v
    @63
    mapdh8a.n
    lspsncl
    syl2anc
    ad2antrr
    wph
    @43
    @86
    simplr
    @60
    @83
    @85
    simprl
    lssneln0
    ex
    @60
    @83
    @20
    @85
    @21
    @60
    @83
    @20
    @60
    @83
    wa
    cN
    cV
    cU
    @0
    cX
    mapdh8a.v
    mapdh8a.n
    wph
    @64
    @43
    @83
    @65
    ad2antrr
    wph
    @43
    @83
    simplr
    wph
    @69
    @43
    @83
    @58
    ad2antrr
    @60
    @83
    simpr
    lspsnne2
    ex
    @60
    @85
    @21
    @60
    @85
    wa
    cN
    cV
    cU
    @0
    cT
    mapdh8a.v
    mapdh8a.n
    wph
    @64
    @43
    @85
    @65
    ad2antrr
    wph
    @43
    @85
    simplr
    wph
    @50
    @43
    @85
    mapdh9a.t
    ad2antrr
    @60
    @85
    simpr
    lspsnne2
    ex
    anim12d
    jcad
    syl5bi
    imim1d
    ralimdva
    reximdv
    mpd
    wph
    @5
    vz
    cV
    wrex
    #
    @13
    @14
    wb
    wph
    @57
    @88
    @59
    wph
    @56
    @5
    vz
    cV
    wph
    @3
    @55
    @0
    wph
    @1
    @2
    @55
    wph
    @62
    @55
    cN
    cU
    cX
    @63
    mapdh8a.n
    @65
    @66
    wph
    cN
    cV
    cU
    cX
    cT
    mapdh8a.v
    mapdh8a.n
    @65
    @58
    mapdh9a.t
    lspprid1
    lspsnel5a
    wph
    @62
    @55
    cN
    cU
    cT
    @63
    mapdh8a.n
    @65
    @66
    wph
    cN
    cV
    cU
    cX
    cT
    mapdh8a.v
    mapdh8a.n
    @65
    @58
    mapdh9a.t
    lspprid2
    lspsnel5a
    unssd
    ssneld
    reximdv
    mpd
    @5
    vy
    vz
    cD
    cV
    @9
    reusv1
    syl
    mpbird
end
