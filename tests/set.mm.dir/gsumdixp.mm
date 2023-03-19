include "co.mm"
include "cmpt2.mm"
include "cgsu.mm"
include "cmpt.mm"
include "cv.mm"
include "cfv.mm"
include "csupp.mm"
include "cxp.mm"
include "crg.mm"
include "wcel.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "syl.mm"
include "adantr.mm"
include "wa.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simpr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cfn.mm"
include "fsuppimpd.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "ianor.mm"
include "brxp.mm"
include "xchnxbir.mm"
include "cdif.mm"
include "simprl.mm"
include "eldif.mm"
include "biimpri.mm"
include "sylan.mm"
include "cvv.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "syldan.mm"
include "oveq1d.mm"
include "ringlz.mm"
include "eqtrd.mm"
include "simprr.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "anasss.mm"
include "gsum2d2.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "weq.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "cbvmpt2.mm"
include "w3a.mm"
include "simp2.mm"
include "3adant3.mm"
include "fvmpt2.mm"
include "simp3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "mpt2eq3dva.mm"
include "syl5eq.mm"
include "nfmpt.mm"
include "mpteq2dv.mm"
include "cbvmpt.mm"
include "syl6eq.mm"
include "3expa.mm"
include "mpteq2dva.mm"
include "3eqtr3d.mm"
include "cplusg.mm"
include "adantlr.mm"
include "cfsupp.mm"
include "gsummulc2.mm"
include "gsumcl.mm"
include "gsummulc1.mm"
include "3eqtrrd.mm"

theorem gsumdixp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume gsumdixp.b: |- B = ( Base ` R )
  assume gsumdixp.t: |- .x. = ( .r ` R )
  assume gsumdixp.z: |- .0. = ( 0g ` R )
  assume gsumdixp.i: |- ( ph -> I e. V )
  assume gsumdixp.j: |- ( ph -> J e. W )
  assume gsumdixp.r: |- ( ph -> R e. Ring )
  assume gsumdixp.x: |- ( ( ph /\ x e. I ) -> X e. B )
  assume gsumdixp.y: |- ( ( ph /\ y e. J ) -> Y e. B )
  assume gsumdixp.xf: |- ( ph -> ( x e. I |-> X ) finSupp .0. )
  assume gsumdixp.yf: |- ( ph -> ( y e. J |-> Y ) finSupp .0. )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint I x
  disjoint I y
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint .x. x
  disjoint .x. y
  disjoint X y
  disjoint Y x
  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint B i
  disjoint B j
  disjoint I i
  disjoint I j
  disjoint J i
  disjoint J j
  disjoint R i
  disjoint R j
  disjoint .x. i
  disjoint .x. j
  disjoint V i
  disjoint X i
  disjoint X j
  disjoint Y i
  disjoint Y j
  disjoint .0. i
  disjoint .0. j
  assert |- ( ph -> ( ( R gsum ( x e. I |-> X ) ) .x. ( R gsum ( y e. J |-> Y ) ) ) = ( R gsum ( x e. I , y e. J |-> ( X .x. Y ) ) ) )

  proof
    wph
    cR
    vx
    vy
    cI
    cJ
    cX
    cY
    c.x
    co
    #
    cmpt2
    #
    cgsu
    co
    #
    cR
    vx
    cI
    cR
    vy
    cJ
    @0
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vx
    cI
    cX
    cR
    vy
    cJ
    cY
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vx
    cI
    cX
    cmpt
    #
    cgsu
    co
    @8
    c.x
    co
    wph
    cR
    vi
    vj
    cI
    cJ
    vi
    cv
    #
    @11
    cfv
    #
    vj
    cv
    #
    @7
    cfv
    #
    c.x
    co
    #
    cmpt2
    #
    cgsu
    co
    cR
    vi
    cI
    cR
    vj
    cJ
    @16
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    @2
    @6
    wph
    cI
    cB
    cJ
    @11
    c.0
    csupp
    co
    #
    @7
    c.0
    csupp
    co
    #
    cxp
    #
    vi
    vj
    cR
    cV
    cW
    @16
    c.0
    gsumdixp.b
    gsumdixp.z
    wph
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
    gsumdixp.r
    cR
    ringcmn
    syl
    #
    gsumdixp.i
    wph
    cJ
    cW
    wcel
    #
    @12
    cI
    wcel
    #
    gsumdixp.j
    adantr
    wph
    @27
    @14
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @24
    @13
    cB
    wcel
    #
    @15
    cB
    wcel
    #
    @16
    cB
    wcel
    wph
    @24
    @29
    gsumdixp.r
    adantr
    #
    wph
    cI
    cB
    @11
    wf
    #
    @27
    @31
    @29
    wph
    vx
    cI
    cX
    cB
    @11
    gsumdixp.x
    @11
    eqid
    #
    fmptd
    #
    @27
    @28
    simpl
    cI
    cB
    @12
    @11
    ffvelrn
    syl2an
    #
    wph
    cJ
    cB
    @7
    wf
    #
    @28
    @32
    @29
    wph
    vy
    cJ
    cY
    cB
    @7
    gsumdixp.y
    @7
    eqid
    #
    fmptd
    #
    @27
    @28
    simpr
    cJ
    cB
    @14
    @7
    ffvelrn
    syl2an
    #
    cB
    cR
    c.x
    @13
    @15
    gsumdixp.b
    gsumdixp.t
    ringcl
    syl3anc
    wph
    @21
    cfn
    wcel
    @22
    cfn
    wcel
    @23
    cfn
    wcel
    wph
    @11
    c.0
    gsumdixp.xf
    fsuppimpd
    wph
    @7
    c.0
    gsumdixp.yf
    fsuppimpd
    @21
    @22
    xpfi
    syl2anc
    wph
    @29
    @12
    @14
    @23
    wbr
    #
    wn
    #
    @16
    c.0
    wceq
    #
    @43
    @30
    @12
    @21
    wcel
    #
    wn
    #
    @14
    @22
    wcel
    #
    wn
    #
    wo
    #
    @44
    @45
    @47
    wa
    @49
    @42
    @45
    @47
    ianor
    @12
    @14
    @21
    @22
    brxp
    xchnxbir
    @30
    @46
    @44
    @48
    @30
    @46
    wa
    #
    @16
    c.0
    @15
    c.x
    co
    #
    c.0
    @50
    @13
    c.0
    @15
    c.x
    @30
    @46
    @12
    cI
    @21
    cdif
    wcel
    #
    @13
    c.0
    wceq
    @30
    @27
    @46
    @52
    wph
    @27
    @28
    simprl
    @52
    @27
    @46
    wa
    @12
    cI
    @21
    eldif
    biimpri
    sylan
    @30
    cI
    cB
    cvv
    @11
    cV
    @21
    @12
    c.0
    wph
    @34
    @29
    @36
    adantr
    @21
    @21
    wss
    @30
    @21
    ssid
    a1i
    wph
    cI
    cV
    wcel
    @29
    gsumdixp.i
    adantr
    c.0
    cvv
    wcel
    @30
    c.0
    cR
    c0g
    cfv
    cvv
    gsumdixp.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    #
    suppssr
    syldan
    oveq1d
    @30
    @51
    c.0
    wceq
    #
    @46
    @30
    @24
    @32
    @54
    @33
    @41
    cB
    cR
    c.x
    @15
    c.0
    gsumdixp.b
    gsumdixp.t
    gsumdixp.z
    ringlz
    syl2anc
    adantr
    eqtrd
    @30
    @48
    wa
    #
    @16
    @13
    c.0
    c.x
    co
    #
    c.0
    @55
    @15
    c.0
    @13
    c.x
    @30
    @48
    @14
    cJ
    @22
    cdif
    wcel
    #
    @15
    c.0
    wceq
    @30
    @28
    @48
    @57
    wph
    @27
    @28
    simprr
    @57
    @28
    @48
    wa
    @14
    cJ
    @22
    eldif
    biimpri
    sylan
    @30
    cJ
    cB
    cvv
    @7
    cW
    @22
    @14
    c.0
    wph
    @38
    @29
    @40
    adantr
    @22
    @22
    wss
    @30
    @22
    ssid
    a1i
    wph
    @26
    @29
    gsumdixp.j
    adantr
    @53
    suppssr
    syldan
    oveq2d
    @30
    @56
    c.0
    wceq
    #
    @48
    @30
    @24
    @31
    @58
    @33
    @37
    cB
    cR
    c.x
    @13
    c.0
    gsumdixp.b
    gsumdixp.t
    gsumdixp.z
    ringrz
    syl2anc
    adantr
    eqtrd
    jaodan
    sylan2b
    anasss
    gsum2d2
    wph
    @17
    @1
    cR
    cgsu
    wph
    @17
    vx
    vy
    cI
    cJ
    vx
    cv
    #
    @11
    cfv
    #
    vy
    cv
    #
    @7
    cfv
    #
    c.x
    co
    #
    cmpt2
    @1
    vi
    vj
    vx
    vy
    cI
    cJ
    @16
    @63
    vx
    @13
    @15
    c.x
    vx
    cI
    cX
    @12
    nffvmpt1
    vx
    c.x
    nfcv
    vx
    @15
    nfcv
    nfov
    #
    vy
    @13
    @15
    c.x
    vy
    @13
    nfcv
    vy
    c.x
    nfcv
    #
    vy
    cJ
    cY
    @14
    nffvmpt1
    #
    nfov
    vi
    @63
    nfcv
    vj
    @63
    nfcv
    #
    vi
    vx
    weq
    #
    vj
    vy
    weq
    #
    @13
    @60
    @15
    @62
    c.x
    @12
    @59
    @11
    fveq2
    #
    @14
    @61
    @7
    fveq2
    #
    oveqan12d
    cbvmpt2
    wph
    vx
    vy
    cI
    cJ
    @63
    @0
    wph
    @59
    cI
    wcel
    #
    @61
    cJ
    wcel
    #
    w3a
    #
    @60
    cX
    @62
    cY
    c.x
    @74
    @72
    cX
    cB
    wcel
    #
    @60
    cX
    wceq
    wph
    @72
    @73
    simp2
    wph
    @72
    @75
    @73
    gsumdixp.x
    3adant3
    vx
    cI
    cX
    cB
    @11
    @35
    fvmpt2
    syl2anc
    @74
    @73
    cY
    cB
    wcel
    #
    @62
    cY
    wceq
    wph
    @72
    @73
    simp3
    wph
    @73
    @76
    @72
    gsumdixp.y
    3adant2
    vy
    cJ
    cY
    cB
    @7
    @39
    fvmpt2
    syl2anc
    oveq12d
    #
    mpt2eq3dva
    syl5eq
    oveq2d
    wph
    @20
    @5
    cR
    cgsu
    wph
    @20
    vx
    cI
    cR
    vy
    cJ
    @63
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @5
    vi
    vx
    cI
    @19
    @79
    vx
    cR
    @18
    cgsu
    vx
    cR
    nfcv
    vx
    cgsu
    nfcv
    vx
    vj
    cJ
    @16
    vx
    cJ
    nfcv
    @64
    nfmpt
    nfov
    vi
    @79
    nfcv
    @68
    @18
    @78
    cR
    cgsu
    @68
    @18
    vj
    cJ
    @60
    @15
    c.x
    co
    #
    cmpt
    @78
    @68
    vj
    cJ
    @16
    @80
    @68
    @13
    @60
    @15
    c.x
    @70
    oveq1d
    mpteq2dv
    vj
    vy
    cJ
    @80
    @63
    vy
    @60
    @15
    c.x
    vy
    @60
    nfcv
    @65
    @66
    nfov
    @67
    @69
    @15
    @62
    @60
    c.x
    @71
    oveq2d
    cbvmpt
    syl6eq
    oveq2d
    cbvmpt
    wph
    vx
    cI
    @79
    @4
    wph
    @72
    wa
    #
    @78
    @3
    cR
    cgsu
    @81
    vy
    cJ
    @63
    @0
    wph
    @72
    @73
    @63
    @0
    wceq
    @77
    3expa
    mpteq2dva
    oveq2d
    mpteq2dva
    syl5eq
    oveq2d
    3eqtr3d
    wph
    @5
    @10
    cR
    cgsu
    wph
    vx
    cI
    @4
    @9
    @81
    cJ
    cB
    cR
    cplusg
    cfv
    #
    cR
    c.x
    vy
    cW
    cY
    cX
    c.0
    gsumdixp.b
    gsumdixp.z
    @82
    eqid
    #
    gsumdixp.t
    wph
    @24
    @72
    gsumdixp.r
    adantr
    wph
    @26
    @72
    gsumdixp.j
    adantr
    gsumdixp.x
    wph
    @73
    @76
    @72
    gsumdixp.y
    adantlr
    wph
    @7
    c.0
    cfsupp
    wbr
    @72
    gsumdixp.yf
    adantr
    gsummulc2
    mpteq2dva
    oveq2d
    wph
    cI
    cB
    @82
    cR
    c.x
    vx
    cV
    cX
    @8
    c.0
    gsumdixp.b
    gsumdixp.z
    @83
    gsumdixp.t
    gsumdixp.r
    gsumdixp.i
    wph
    cJ
    cB
    @7
    cR
    cW
    c.0
    gsumdixp.b
    gsumdixp.z
    @25
    gsumdixp.j
    @40
    gsumdixp.yf
    gsumcl
    gsumdixp.x
    gsumdixp.xf
    gsummulc1
    3eqtrrd
end
