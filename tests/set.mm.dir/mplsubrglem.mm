include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "cfsupp.mm"
include "wbr.mm"
include "eqid.mm"
include "mplbasss.mm"
include "sseldi.mm"
include "psrmulcl.mm"
include "cvv.mm"
include "wfun.mm"
include "cfn.mm"
include "csupp.mm"
include "wss.mm"
include "ovexd.mm"
include "psrelbasfun.mm"
include "syl.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "caddc.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "df-ima.mm"
include "eqtri.mm"
include "wfo.mm"
include "mplelbas.mm"
include "simprbi.mm"
include "fsuppxpfi.mm"
include "syl2anc.mm"
include "wfn.mm"
include "cv.mm"
include "ofmres.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fofi.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "psrelbas.mm"
include "cdif.mm"
include "wa.mm"
include "cle.mm"
include "cofr.mm"
include "crab.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "psrmulval.mm"
include "wceq.mm"
include "crg.mm"
include "ad2antrr.mm"
include "wf.mm"
include "mplelf.mm"
include "ssrab2.mm"
include "simpr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "ringlz.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "ringrz.mm"
include "oveq2.mm"
include "wn.mm"
include "wo.mm"
include "cn0.mm"
include "psrbagf.mm"
include "ffvelrnda.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan3.mm"
include "syl2an.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "eldifbd.mm"
include "ovres.mm"
include "w3a.mm"
include "fnovrn.mm"
include "syl6eleqr.mm"
include "mp3an1.mm"
include "eqeltrrd.mm"
include "nsyl.mm"
include "ianor.mm"
include "sylib.mm"
include "wb.mm"
include "eldif.mm"
include "baib.mm"
include "ssid.mm"
include "ccnv.mm"
include "cn.mm"
include "cmap.mm"
include "rabex2.mm"
include "suppssr.mm"
include "ex.mm"
include "sylbird.mm"
include "orim12d.mm"
include "mpd.mm"
include "mpjaod.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "psrbaglefi.mm"
include "gsumz.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "sylanbrc.mm"

theorem mplsubrglem
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cI: class I
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vg: setvar g
  let vy: setvar y
  assume mplsubg.s: |- S = ( I mPwSer R )
  assume mplsubg.p: |- P = ( I mPoly R )
  assume mplsubg.u: |- U = ( Base ` P )
  assume mplsubg.i: |- ( ph -> I e. W )
  assume mpllss.r: |- ( ph -> R e. Ring )
  assume mplsubrglem.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplsubrglem.z: |- .0. = ( 0g ` R )
  assume mplsubrglem.p: |- A = ( oF + " ( ( X supp .0. ) X. ( Y supp .0. ) ) )
  assume mplsubrglem.t: |- .x. = ( .r ` R )
  assume mplsubrglem.x: |- ( ph -> X e. U )
  assume mplsubrglem.y: |- ( ph -> Y e. U )

  disjoint I f
  disjoint R f
  disjoint S f
  disjoint X f
  disjoint Y f
  disjoint .0. f
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint I g
  disjoint k y
  disjoint I k
  disjoint n y
  disjoint I n
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint g ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint R g
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint S g
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint U x
  disjoint U y
  disjoint X g
  disjoint X k
  disjoint X x
  disjoint Y g
  disjoint Y k
  disjoint Y x
  disjoint .x. x
  disjoint W k
  disjoint W y
  disjoint .0. g
  disjoint .0. k
  assert |- ( ph -> ( X ( .r ` S ) Y ) e. U )

  proof
    wph
    cX
    cY
    cS
    cmulr
    cfv
    #
    co
    #
    cS
    cbs
    cfv
    #
    wcel
    #
    @1
    c.0
    cfsupp
    wbr
    #
    @1
    cU
    wcel
    wph
    @2
    cR
    cS
    @0
    cI
    cX
    cY
    mplsubg.s
    @2
    eqid
    #
    @0
    eqid
    #
    mpllss.r
    wph
    cU
    @2
    cX
    @2
    cP
    cR
    cS
    cU
    cI
    mplsubg.p
    mplsubg.s
    mplsubg.u
    @5
    mplbasss
    #
    mplsubrglem.x
    sseldi
    #
    wph
    cU
    @2
    cY
    @7
    mplsubrglem.y
    sseldi
    #
    psrmulcl
    #
    wph
    @1
    cvv
    wcel
    @1
    wfun
    #
    c.0
    cvv
    wcel
    #
    cA
    cfn
    wcel
    @1
    c.0
    csupp
    co
    cA
    wss
    @4
    wph
    cX
    cY
    @0
    ovexd
    wph
    @3
    @11
    @10
    @2
    cR
    cS
    cI
    @1
    mplsubg.s
    @5
    psrelbasfun
    syl
    @12
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    mplsubrglem.z
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    wph
    cA
    caddc
    cof
    #
    cX
    c.0
    csupp
    co
    #
    cY
    c.0
    csupp
    co
    #
    cxp
    #
    cres
    #
    crn
    #
    cfn
    cA
    @14
    @17
    cima
    @19
    mplsubrglem.p
    @14
    @17
    df-ima
    eqtri
    #
    wph
    @17
    cfn
    wcel
    #
    @17
    @19
    @18
    wfo
    #
    @19
    cfn
    wcel
    wph
    cX
    c.0
    cfsupp
    wbr
    #
    cY
    c.0
    cfsupp
    wbr
    #
    @21
    wph
    cX
    cU
    wcel
    #
    @23
    mplsubrglem.x
    @25
    cX
    @2
    wcel
    #
    @23
    @2
    cP
    cR
    cS
    cU
    cI
    cX
    c.0
    mplsubg.p
    mplsubg.s
    @5
    mplsubrglem.z
    mplsubg.u
    mplelbas
    simprbi
    syl
    wph
    cY
    cU
    wcel
    #
    @24
    mplsubrglem.y
    @27
    cY
    @2
    wcel
    #
    @24
    @2
    cP
    cR
    cS
    cU
    cI
    cY
    c.0
    mplsubg.p
    mplsubg.s
    @5
    mplsubrglem.z
    mplsubg.u
    mplelbas
    simprbi
    syl
    cX
    cY
    c.0
    fsuppxpfi
    syl2anc
    @18
    @17
    wfn
    #
    @22
    vf
    vg
    @15
    @16
    vf
    cv
    #
    vg
    cv
    #
    @14
    co
    @18
    @15
    @16
    caddc
    vf
    vg
    ofmres
    @30
    @31
    @14
    ovex
    fnmpt2i
    #
    @17
    @18
    dffn4
    mpbi
    @17
    @19
    @18
    fofi
    sylancl
    syl5eqel
    wph
    cD
    cR
    cbs
    cfv
    #
    vk
    @1
    cA
    c.0
    wph
    @2
    cD
    cR
    cS
    vf
    cI
    @33
    @1
    mplsubg.s
    @33
    eqid
    #
    mplsubrglem.d
    @5
    @10
    psrelbas
    wph
    vk
    cv
    #
    cD
    cA
    cdif
    #
    wcel
    #
    wa
    #
    @35
    @1
    cfv
    cR
    vx
    vy
    cv
    @35
    cle
    cofr
    wbr
    #
    vy
    cD
    crab
    #
    vx
    cv
    #
    cX
    cfv
    #
    @35
    @41
    cmin
    cof
    co
    #
    cY
    cfv
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
    @40
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @38
    vy
    @2
    cD
    cR
    cS
    @0
    c.x
    vf
    vx
    cX
    cY
    cI
    @35
    mplsubg.s
    @5
    mplsubrglem.t
    @6
    mplsubrglem.d
    wph
    @26
    @37
    @8
    adantr
    wph
    @28
    @37
    @9
    adantr
    @37
    @35
    cD
    wcel
    #
    wph
    @35
    cD
    cA
    eldifi
    #
    adantl
    #
    psrmulval
    @38
    @46
    @47
    cR
    cgsu
    @38
    vx
    @40
    @45
    c.0
    @38
    @41
    @40
    wcel
    #
    wa
    #
    @42
    c.0
    wceq
    #
    @45
    c.0
    wceq
    #
    @44
    c.0
    wceq
    #
    @53
    @55
    @54
    c.0
    @44
    c.x
    co
    #
    c.0
    wceq
    #
    @53
    cR
    crg
    wcel
    #
    @44
    @33
    wcel
    @58
    wph
    @59
    @37
    @52
    mpllss.r
    ad2antrr
    #
    @53
    cD
    @33
    @43
    cY
    wph
    cD
    @33
    cY
    wf
    @37
    @52
    wph
    cU
    cD
    cP
    cR
    vf
    cI
    @33
    cY
    mplsubg.p
    @34
    mplsubg.u
    mplsubrglem.d
    mplsubrglem.y
    mplelf
    ad2antrr
    #
    @53
    @40
    cD
    @43
    @39
    vy
    cD
    ssrab2
    #
    @53
    cI
    cW
    wcel
    #
    @49
    @52
    @43
    @40
    wcel
    wph
    @63
    @37
    @52
    mplsubg.i
    ad2antrr
    #
    @38
    @49
    @52
    @51
    adantr
    #
    @38
    @52
    simpr
    #
    vy
    cD
    @40
    vf
    @35
    cI
    cW
    @41
    mplsubrglem.d
    @40
    eqid
    psrbagconcl
    syl3anc
    sseldi
    #
    ffvelrnd
    @33
    cR
    c.x
    @44
    c.0
    @34
    mplsubrglem.t
    mplsubrglem.z
    ringlz
    syl2anc
    @54
    @45
    @57
    c.0
    @42
    c.0
    @44
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @53
    @55
    @56
    @42
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    @53
    @59
    @42
    @33
    wcel
    @69
    @60
    @53
    cD
    @33
    @41
    cX
    wph
    cD
    @33
    cX
    wf
    @37
    @52
    wph
    cU
    cD
    cP
    cR
    vf
    cI
    @33
    cX
    mplsubg.p
    @34
    mplsubg.u
    mplsubrglem.d
    mplsubrglem.x
    mplelf
    ad2antrr
    #
    @53
    @40
    cD
    @41
    @62
    @66
    sseldi
    #
    ffvelrnd
    @33
    cR
    c.x
    @42
    c.0
    @34
    mplsubrglem.t
    mplsubrglem.z
    ringrz
    syl2anc
    @56
    @45
    @68
    c.0
    @44
    c.0
    @42
    c.x
    oveq2
    eqeq1d
    syl5ibrcom
    @53
    @41
    @15
    wcel
    #
    wn
    #
    @43
    @16
    wcel
    #
    wn
    #
    wo
    #
    @54
    @56
    wo
    @53
    @72
    @74
    wa
    #
    wn
    @76
    @53
    @41
    @43
    @14
    co
    #
    cA
    wcel
    @77
    @53
    @78
    cD
    cA
    @53
    @78
    @35
    @36
    @53
    vn
    cI
    vn
    cv
    #
    @41
    cfv
    #
    @79
    @35
    cfv
    #
    @80
    cmin
    co
    #
    caddc
    co
    #
    cmpt
    vn
    cI
    @81
    cmpt
    @78
    @35
    @53
    vn
    cI
    @83
    @81
    @53
    @79
    cI
    wcel
    wa
    #
    @80
    cn0
    wcel
    #
    @81
    cn0
    wcel
    #
    @83
    @81
    wceq
    #
    @53
    cI
    cn0
    @79
    @41
    @53
    @63
    @41
    cD
    wcel
    #
    cI
    cn0
    @41
    wf
    @64
    @71
    cD
    vf
    @41
    cI
    cW
    mplsubrglem.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @53
    cI
    cn0
    @79
    @35
    @53
    @63
    @49
    cI
    cn0
    @35
    wf
    @64
    @65
    cD
    vf
    @35
    cI
    cW
    mplsubrglem.d
    psrbagf
    syl2anc
    #
    ffvelrnda
    #
    @85
    @80
    cc
    wcel
    @81
    cc
    wcel
    @87
    @86
    @80
    nn0cn
    @81
    nn0cn
    @80
    @81
    pncan3
    syl2an
    syl2anc
    mpteq2dva
    @53
    vn
    cI
    @80
    @82
    caddc
    @41
    @43
    cW
    cn0
    cvv
    @64
    @90
    @84
    @81
    @80
    cmin
    ovexd
    @53
    vn
    cI
    cn0
    @41
    @89
    feqmptd
    #
    @53
    vn
    cI
    @81
    @80
    cmin
    @35
    @41
    cW
    cn0
    cn0
    @64
    @92
    @90
    @53
    vn
    cI
    cn0
    @35
    @91
    feqmptd
    #
    @93
    offval2
    offval2
    @94
    3eqtr4d
    wph
    @37
    @52
    simplr
    eqeltrd
    eldifbd
    @77
    @41
    @43
    @18
    co
    #
    @78
    cA
    @41
    @43
    @15
    @16
    @14
    ovres
    @29
    @72
    @74
    @95
    cA
    wcel
    @32
    @29
    @72
    @74
    w3a
    @95
    @19
    cA
    @15
    @16
    @41
    @43
    @18
    fnovrn
    @20
    syl6eleqr
    mp3an1
    eqeltrrd
    nsyl
    @72
    @74
    ianor
    sylib
    @53
    @73
    @54
    @75
    @56
    @53
    @73
    @41
    cD
    @15
    cdif
    wcel
    #
    @54
    @53
    @88
    @96
    @73
    wb
    @71
    @96
    @88
    @73
    @41
    cD
    @15
    eldif
    baib
    syl
    @53
    @96
    @54
    @53
    cD
    @33
    cvv
    cX
    cvv
    @15
    @41
    c.0
    @70
    @15
    @15
    wss
    @53
    @15
    ssid
    a1i
    cD
    cvv
    wcel
    @53
    @30
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    mplsubrglem.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    #
    @12
    @53
    @13
    a1i
    #
    suppssr
    ex
    sylbird
    @53
    @75
    @43
    cD
    @16
    cdif
    wcel
    #
    @56
    @53
    @43
    cD
    wcel
    #
    @99
    @75
    wb
    @67
    @99
    @100
    @75
    @43
    cD
    @16
    eldif
    baib
    syl
    @53
    @99
    @56
    @53
    cD
    @33
    cvv
    cY
    cvv
    @16
    @43
    c.0
    @61
    @16
    @16
    wss
    @53
    @16
    ssid
    a1i
    @97
    @98
    suppssr
    ex
    sylbird
    orim12d
    mpd
    mpjaod
    mpteq2dva
    oveq2d
    @38
    cR
    cmnd
    wcel
    #
    @40
    cfn
    wcel
    #
    @48
    c.0
    wceq
    @38
    @59
    @101
    wph
    @59
    @37
    mpllss.r
    adantr
    cR
    ringmnd
    syl
    wph
    @63
    @49
    @102
    @37
    mplsubg.i
    @50
    vy
    cD
    vf
    @35
    cI
    cW
    mplsubrglem.d
    psrbaglefi
    syl2an
    @40
    vx
    cR
    cfn
    c.0
    mplsubrglem.z
    gsumz
    syl2anc
    3eqtrd
    suppss
    cA
    @1
    cvv
    cvv
    c.0
    suppssfifsupp
    syl32anc
    @2
    cP
    cR
    cS
    cU
    cI
    @1
    c.0
    mplsubg.p
    mplsubg.s
    @5
    mplsubrglem.z
    mplsubg.u
    mplelbas
    sylanbrc
end
