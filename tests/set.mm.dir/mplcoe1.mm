include "csupp.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "cif.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wcel.mm"
include "cbs.mm"
include "eqid.mm"
include "mplelf.mm"
include "feqmptd.mm"
include "wa.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "ifid.mm"
include "cvv.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "ifeq2d.mm"
include "syl5reqr.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "wi.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmps.mm"
include "mplelbas.mm"
include "simprbi.mm"
include "fsuppimpd.mm"
include "wel.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sseq1.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "gsum0.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "mpteq2dv.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "ifbid.mm"
include "cxp.mm"
include "crg.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "mpl0.mm"
include "fconstmpt.mm"
include "a1d.mm"
include "ssun1.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "cplusg.mm"
include "oveq1.mm"
include "ccmn.mm"
include "mplring.mm"
include "syl2anc.mm"
include "ringcmn.mm"
include "adantr.mm"
include "simprll.mm"
include "simprr.mm"
include "unssad.mm"
include "sselda.mm"
include "clmod.mm"
include "csca.mm"
include "mpllmod.mm"
include "ffvelrnda.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "mplmon.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "syldan.mm"
include "vex.mm"
include "simprlr.mm"
include "unssbd.mm"
include "snss.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "equequ2.mm"
include "oveq12d.mm"
include "gsumunsn.mm"
include "cof.mm"
include "cmulr.mm"
include "ring0cl.mm"
include "ad2antrr.mm"
include "ifcld.mm"
include "fmptd.mm"
include "elmap.mm"
include "psrbas.mm"
include "eleqtrrd.mm"
include "wfun.mm"
include "w3a.mm"
include "mptex.mm"
include "funmpt.mm"
include "3pm3.2i.mm"
include "eldifn.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl12anc.mm"
include "sylanbrc.mm"
include "mpladd.mm"
include "ovexd.mm"
include "eqidd.mm"
include "mplvsca.mm"
include "ringidcl.mm"
include "offval2.mm"
include "eqtrd.mm"
include "grplid.mm"
include "velsn.mm"
include "sylib.mm"
include "eqneltrd.mm"
include "iftrued.mm"
include "ringridm.mm"
include "elun2.mm"
include "3eqtr4d.mm"
include "grprid.mm"
include "sylnib.mm"
include "ringrz.mm"
include "wb.mm"
include "wo.mm"
include "biorf.mm"
include "elun.mm"
include "orcom.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "3eqtrrd.mm"
include "syl5ibr.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpd.mm"
include "cres.mm"
include "resmptd.mm"
include "oveq1d.mm"
include "eldifi.mm"
include "syl5eq.mm"
include "lmod0vs.mm"
include "sylan2.mm"
include "gsumres.mm"
include "eqtr3d.mm"

theorem mplcoe1
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vk: setvar k
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vi: setvar i
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let c.ex: class .^
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  assume mplcoe1.p: |- P = ( I mPoly R )
  assume mplcoe1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplcoe1.z: |- .0. = ( 0g ` R )
  assume mplcoe1.o: |- .1. = ( 1r ` R )
  assume mplcoe1.i: |- ( ph -> I e. W )
  assume mplcoe1.b: |- B = ( Base ` P )
  assume mplcoe1.n: |- .x. = ( .s ` P )
  assume mplcoe1.r: |- ( ph -> R e. Ring )
  assume mplcoe1.x: |- ( ph -> X e. B )

  disjoint k y
  disjoint .1. k
  disjoint .1. y
  disjoint B k
  disjoint f k
  disjoint f y
  disjoint I f
  disjoint I k
  disjoint I y
  disjoint k ph
  disjoint ph y
  disjoint R f
  disjoint R y
  disjoint D k
  disjoint D y
  disjoint P k
  disjoint .0. f
  disjoint .0. k
  disjoint .0. y
  disjoint X f
  disjoint X k
  disjoint X y
  disjoint W k
  disjoint W y
  disjoint .x. k
  disjoint i k
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint .^ i
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint .^ k
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint .^ n
  disjoint w x
  disjoint w z
  disjoint .^ w
  disjoint x z
  disjoint .^ x
  disjoint .^ z
  disjoint i y
  disjoint .1. i
  disjoint n y
  disjoint .1. n
  disjoint w y
  disjoint .1. w
  disjoint x y
  disjoint .1. x
  disjoint y z
  disjoint .1. z
  disjoint G i
  disjoint G k
  disjoint G w
  disjoint G x
  disjoint G z
  disjoint f i
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint I i
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint D x
  disjoint D z
  disjoint P i
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint V i
  disjoint V k
  disjoint V n
  disjoint V w
  disjoint V x
  disjoint V z
  disjoint .0. i
  disjoint .0. n
  disjoint .0. w
  disjoint .0. x
  disjoint .0. z
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint Y f
  disjoint Y i
  disjoint Y k
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint W i
  disjoint .x. w
  disjoint .x. x
  disjoint .x. z
  assert |- ( ph -> X = ( P gsum ( k e. D |-> ( ( X ` k ) .x. ( y e. D |-> if ( y = k , .1. , .0. ) ) ) ) ) )

  proof
    wph
    cX
    cP
    vk
    cX
    c.0
    csupp
    co
    #
    vk
    cv
    #
    cX
    cfv
    #
    vy
    cD
    vy
    vk
    weq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    vk
    cD
    @6
    cmpt
    #
    cgsu
    co
    #
    wph
    cX
    vy
    cD
    vy
    cv
    #
    @0
    wcel
    #
    @11
    cX
    cfv
    #
    c.0
    cif
    #
    cmpt
    #
    @8
    wph
    cX
    vy
    cD
    @13
    cmpt
    @15
    wph
    vy
    cD
    cR
    cbs
    cfv
    #
    cX
    wph
    cB
    cD
    cP
    cR
    vf
    cI
    @16
    cX
    mplcoe1.p
    @16
    eqid
    #
    mplcoe1.b
    mplcoe1.d
    mplcoe1.x
    mplelf
    #
    feqmptd
    wph
    vy
    cD
    @14
    @13
    wph
    @11
    cD
    wcel
    #
    wa
    #
    @12
    @14
    @13
    wceq
    #
    @12
    @21
    @20
    @12
    @13
    c.0
    iftrue
    adantl
    wph
    @19
    @12
    wn
    #
    @21
    @19
    @22
    wa
    wph
    @11
    cD
    @0
    cdif
    #
    wcel
    #
    @21
    @11
    cD
    @0
    eldif
    wph
    @24
    wa
    #
    @13
    @12
    @13
    @13
    cif
    @14
    @12
    @13
    ifid
    @25
    @12
    @13
    c.0
    @13
    wph
    cD
    @16
    cvv
    cX
    cvv
    @0
    @11
    c.0
    @18
    @0
    @0
    wss
    wph
    @0
    ssid
    a1i
    #
    cD
    cvv
    wcel
    #
    wph
    vf
    cv
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
    mplcoe1.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    a1i
    #
    c.0
    cvv
    wcel
    #
    wph
    c.0
    cR
    c0g
    cfv
    #
    cvv
    mplcoe1.z
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    #
    suppssr
    ifeq2d
    syl5reqr
    sylan2br
    anassrs
    pm2.61dan
    mpteq2dva
    eqtr4d
    wph
    @0
    cD
    wss
    #
    @8
    @15
    wceq
    #
    wph
    cX
    cdm
    #
    @0
    cD
    cX
    c.0
    suppssdm
    wph
    cD
    @16
    cX
    wf
    #
    @36
    cD
    wceq
    @18
    cD
    @16
    cX
    fdm
    syl
    syl5sseq
    #
    @0
    cfn
    wcel
    #
    wph
    @34
    @35
    wi
    #
    wph
    cX
    c.0
    wph
    cX
    cB
    wcel
    #
    cX
    c.0
    cfsupp
    wbr
    #
    mplcoe1.x
    @41
    cX
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    wcel
    @42
    @44
    cP
    cR
    @43
    cB
    cI
    cX
    c.0
    mplcoe1.p
    @43
    eqid
    #
    @44
    eqid
    #
    mplcoe1.z
    mplcoe1.b
    mplelbas
    simprbi
    syl
    fsuppimpd
    #
    wph
    vw
    cv
    #
    cD
    wss
    #
    cP
    vk
    @48
    @6
    cmpt
    #
    cgsu
    co
    #
    vy
    cD
    vy
    vw
    wel
    #
    @13
    c.0
    cif
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    cD
    wss
    #
    cP
    c0g
    cfv
    #
    vy
    cD
    c.0
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    vx
    cv
    #
    cD
    wss
    #
    cP
    vk
    @62
    @6
    cmpt
    #
    cgsu
    co
    #
    vy
    cD
    vy
    vx
    wel
    #
    @13
    c.0
    cif
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    @62
    vz
    cv
    #
    csn
    #
    cun
    #
    cD
    wss
    #
    cP
    vk
    @73
    @6
    cmpt
    #
    cgsu
    co
    #
    vy
    cD
    @11
    @73
    wcel
    #
    @13
    c.0
    cif
    #
    cmpt
    #
    wceq
    #
    wi
    #
    wi
    wph
    @40
    wi
    vw
    vx
    vz
    @0
    @48
    c0
    wceq
    #
    @56
    @61
    wph
    @82
    @49
    @57
    @55
    @60
    @48
    c0
    cD
    sseq1
    @82
    @51
    @58
    @54
    @59
    @82
    @51
    cP
    c0
    cgsu
    co
    @58
    @82
    @50
    c0
    cP
    cgsu
    @82
    @50
    vk
    c0
    @6
    cmpt
    c0
    vk
    @48
    c0
    @6
    mpteq1
    vk
    @6
    mpt0
    syl6eq
    oveq2d
    cP
    @58
    @58
    eqid
    #
    gsum0
    syl6eq
    @82
    vy
    cD
    @53
    c.0
    @82
    @52
    @13
    c.0
    @82
    @52
    @11
    c0
    wcel
    @11
    noel
    @48
    c0
    @11
    eleq2
    mtbiri
    iffalsed
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    vw
    vx
    weq
    #
    @56
    @70
    wph
    @84
    @49
    @63
    @55
    @69
    @48
    @62
    cD
    sseq1
    @84
    @51
    @65
    @54
    @68
    @84
    @50
    @64
    cP
    cgsu
    vk
    @48
    @62
    @6
    mpteq1
    oveq2d
    @84
    vy
    cD
    @53
    @67
    @84
    @52
    @66
    @13
    c.0
    @48
    @62
    @11
    eleq2
    ifbid
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    @48
    @73
    wceq
    #
    @56
    @81
    wph
    @85
    @49
    @74
    @55
    @80
    @48
    @73
    cD
    sseq1
    @85
    @51
    @76
    @54
    @79
    @85
    @50
    @75
    cP
    cgsu
    vk
    @48
    @73
    @6
    mpteq1
    oveq2d
    @85
    vy
    cD
    @53
    @78
    @85
    @52
    @77
    @13
    c.0
    @48
    @73
    @11
    eleq2
    ifbid
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    @48
    @0
    wceq
    #
    @56
    @40
    wph
    @86
    @49
    @34
    @55
    @35
    @48
    @0
    cD
    sseq1
    @86
    @51
    @8
    @54
    @15
    @86
    @50
    @7
    cP
    cgsu
    vk
    @48
    @0
    @6
    mpteq1
    oveq2d
    @86
    vy
    cD
    @53
    @14
    @86
    @52
    @12
    @13
    c.0
    @48
    @0
    @11
    eleq2
    ifbid
    mpteq2dv
    eqeq12d
    imbi12d
    imbi2d
    wph
    @60
    @57
    wph
    @58
    cD
    c.0
    csn
    cxp
    @59
    wph
    cD
    cP
    cR
    vf
    cI
    c.0
    cW
    @58
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    @83
    mplcoe1.i
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    #
    mplcoe1.r
    cR
    ringgrp
    #
    syl
    #
    mpl0
    vy
    cD
    c.0
    fconstmpt
    syl6eq
    a1d
    @62
    cfn
    wcel
    #
    vz
    vx
    wel
    wn
    #
    wa
    #
    wph
    @70
    @81
    wph
    @93
    @70
    @81
    wi
    @70
    @74
    @69
    wi
    wph
    @93
    wa
    #
    @81
    @74
    @63
    @69
    @62
    @73
    wss
    @74
    @63
    wi
    @62
    @72
    ssun1
    @62
    @73
    cD
    sstr2
    ax-mp
    imim1i
    @94
    @74
    @69
    @80
    wph
    @93
    @74
    @69
    @80
    wi
    @69
    @80
    wph
    @93
    @74
    wa
    #
    wa
    #
    @65
    @71
    cX
    cfv
    #
    vy
    cD
    vy
    vz
    weq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    c.x
    co
    #
    cP
    cplusg
    cfv
    #
    co
    #
    @68
    @101
    @102
    co
    #
    wceq
    @65
    @68
    @101
    @102
    oveq1
    @96
    @76
    @103
    @79
    @104
    @96
    @62
    cB
    @102
    vk
    cP
    @71
    cvv
    @6
    @101
    mplcoe1.b
    @102
    eqid
    #
    wph
    cP
    ccmn
    wcel
    #
    @95
    wph
    cP
    crg
    wcel
    #
    @106
    wph
    cI
    cW
    wcel
    #
    @87
    @107
    mplcoe1.i
    mplcoe1.r
    cP
    cR
    cI
    cW
    mplcoe1.p
    mplring
    syl2anc
    cP
    ringcmn
    syl
    #
    adantr
    wph
    @91
    @92
    @74
    simprll
    #
    @96
    vk
    vx
    wel
    @1
    cD
    wcel
    #
    @6
    cB
    wcel
    #
    @96
    @62
    cD
    @1
    @96
    @62
    @72
    cD
    wph
    @93
    @74
    simprr
    #
    unssad
    sselda
    wph
    @111
    @112
    @95
    wph
    @111
    wa
    #
    cP
    clmod
    wcel
    #
    @2
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @5
    cB
    wcel
    #
    @112
    @114
    @108
    @87
    @115
    wph
    @108
    @111
    mplcoe1.i
    adantr
    #
    wph
    @87
    @111
    mplcoe1.r
    adantr
    #
    cP
    cR
    cI
    cW
    mplcoe1.p
    mpllmod
    #
    syl2anc
    #
    @114
    @2
    @16
    @117
    wph
    cD
    @16
    @1
    cX
    @18
    ffvelrnda
    @114
    cR
    @116
    cbs
    wph
    cR
    @116
    wceq
    #
    @111
    wph
    cP
    cR
    cI
    cW
    crg
    mplcoe1.p
    mplcoe1.i
    mplcoe1.r
    mplsca
    #
    adantr
    #
    fveq2d
    eleqtrd
    @114
    vy
    cB
    cD
    cP
    cR
    c.1
    vf
    cI
    cW
    @1
    c.0
    mplcoe1.p
    mplcoe1.b
    mplcoe1.z
    mplcoe1.o
    mplcoe1.d
    @119
    @120
    wph
    @111
    simpr
    mplmon
    #
    @2
    c.x
    @116
    @117
    cB
    cP
    @5
    mplcoe1.b
    @116
    eqid
    #
    mplcoe1.n
    @117
    eqid
    #
    lmodvscl
    syl3anc
    #
    adantlr
    syldan
    @71
    cvv
    wcel
    @96
    vz
    vex
    #
    a1i
    wph
    @91
    @92
    @74
    simprlr
    #
    @96
    @115
    @97
    @117
    wcel
    @100
    cB
    wcel
    @101
    cB
    wcel
    wph
    @115
    @95
    wph
    @108
    @87
    @115
    mplcoe1.i
    mplcoe1.r
    @121
    syl2anc
    adantr
    @96
    @97
    @16
    @117
    @96
    cD
    @16
    @71
    cX
    wph
    @37
    @95
    @18
    adantr
    #
    @96
    @72
    cD
    wss
    @71
    cD
    wcel
    @96
    @62
    @72
    cD
    @113
    unssbd
    @71
    cD
    @130
    snss
    sylibr
    #
    ffvelrnd
    #
    @96
    cR
    @116
    cbs
    wph
    @123
    @95
    @124
    adantr
    fveq2d
    eleqtrd
    @96
    vy
    cB
    cD
    cP
    cR
    c.1
    vf
    cI
    cW
    @71
    c.0
    mplcoe1.p
    mplcoe1.b
    mplcoe1.z
    mplcoe1.o
    mplcoe1.d
    wph
    @108
    @95
    mplcoe1.i
    adantr
    #
    wph
    @87
    @95
    mplcoe1.r
    adantr
    #
    @133
    mplmon
    #
    @97
    c.x
    @116
    @117
    cB
    cP
    @100
    mplcoe1.b
    @127
    mplcoe1.n
    @128
    lmodvscl
    syl3anc
    #
    vk
    vz
    weq
    #
    @2
    @97
    @5
    @100
    c.x
    @1
    @71
    cX
    fveq2
    @139
    vy
    cD
    @4
    @99
    @139
    @3
    @98
    c.1
    c.0
    vk
    vz
    vy
    equequ2
    ifbid
    mpteq2dv
    oveq12d
    gsumunsn
    @96
    @104
    @68
    @101
    cR
    cplusg
    cfv
    #
    cof
    co
    vy
    cD
    @67
    @97
    @99
    cR
    cmulr
    cfv
    #
    co
    #
    @140
    co
    #
    cmpt
    @79
    @96
    cB
    cP
    @140
    @102
    cR
    cI
    @68
    @101
    mplcoe1.p
    mplcoe1.b
    @140
    eqid
    #
    @105
    @96
    @68
    @44
    wcel
    @68
    c.0
    cfsupp
    wbr
    #
    @68
    cB
    wcel
    @96
    @68
    @16
    cD
    cmap
    co
    #
    @44
    @96
    cD
    @16
    @68
    wf
    @68
    @146
    wcel
    @96
    vy
    cD
    @67
    @16
    @68
    @96
    @19
    wa
    #
    @66
    @13
    c.0
    @16
    @96
    cD
    @16
    @11
    cX
    @132
    ffvelrnda
    wph
    c.0
    @16
    wcel
    #
    @95
    @19
    wph
    @87
    @148
    mplcoe1.r
    @16
    cR
    c.0
    @17
    mplcoe1.z
    ring0cl
    #
    syl
    ad2antrr
    ifcld
    #
    @68
    eqid
    fmptd
    @16
    cD
    @68
    cR
    cbs
    fvex
    @28
    elmap
    sylibr
    @96
    @44
    cD
    cR
    @43
    vf
    cI
    @16
    cW
    @45
    @17
    mplcoe1.d
    @46
    @135
    psrbas
    eleqtrrd
    @96
    @68
    cvv
    wcel
    #
    @68
    wfun
    #
    @30
    w3a
    #
    @91
    @68
    c.0
    csupp
    co
    @62
    wss
    @145
    @153
    @96
    @151
    @152
    @30
    vy
    cD
    @67
    @28
    mptex
    vy
    cD
    @67
    funmpt
    @32
    3pm3.2i
    a1i
    @110
    @96
    cD
    @67
    vy
    cvv
    @62
    c.0
    @96
    @11
    cD
    @62
    cdif
    wcel
    #
    wa
    @66
    @13
    c.0
    @154
    @66
    wn
    @96
    @11
    cD
    @62
    eldifn
    adantl
    iffalsed
    @27
    @96
    @28
    a1i
    #
    suppss2
    @62
    @68
    cvv
    cvv
    c.0
    suppssfifsupp
    syl12anc
    @44
    cP
    cR
    @43
    cB
    cI
    @68
    c.0
    mplcoe1.p
    @45
    @46
    mplcoe1.z
    mplcoe1.b
    mplelbas
    sylanbrc
    @138
    mpladd
    @96
    vy
    cD
    @67
    @142
    @140
    @68
    @101
    cvv
    @16
    cvv
    @155
    @150
    @147
    @97
    @99
    @141
    ovexd
    @96
    @68
    eqidd
    @96
    @101
    cD
    @97
    csn
    cxp
    #
    @100
    @141
    cof
    co
    vy
    cD
    @142
    cmpt
    @96
    cB
    cD
    cP
    cR
    c.x
    @141
    vf
    @100
    cI
    @16
    @97
    mplcoe1.p
    mplcoe1.n
    @17
    mplcoe1.b
    @141
    eqid
    #
    mplcoe1.d
    @134
    @137
    mplvsca
    @96
    vy
    cD
    @97
    @99
    @141
    @156
    @100
    cvv
    @16
    @16
    @155
    @96
    @97
    @16
    wcel
    #
    @19
    @134
    adantr
    wph
    @99
    @16
    wcel
    #
    @95
    @19
    wph
    @87
    @159
    mplcoe1.r
    @87
    @98
    c.1
    c.0
    @16
    @16
    cR
    c.1
    @17
    mplcoe1.o
    ringidcl
    @149
    ifcld
    syl
    ad2antrr
    @156
    vy
    cD
    @97
    cmpt
    wceq
    @96
    vy
    cD
    @97
    fconstmpt
    a1i
    @96
    @100
    eqidd
    offval2
    eqtrd
    offval2
    @96
    vy
    cD
    @143
    @78
    @147
    @11
    @72
    wcel
    #
    @143
    @78
    wceq
    @147
    @160
    wa
    #
    c.0
    @97
    @140
    co
    #
    @13
    @143
    @78
    @161
    @162
    @97
    @13
    @96
    @162
    @97
    wceq
    #
    @19
    @160
    @96
    @88
    @158
    @163
    @96
    @87
    @88
    @136
    @89
    syl
    @134
    @16
    @140
    cR
    @97
    c.0
    @17
    @144
    mplcoe1.z
    grplid
    syl2anc
    ad2antrr
    @161
    @11
    @71
    cX
    @161
    @160
    @98
    @147
    @160
    simpr
    vy
    @71
    velsn
    #
    sylib
    #
    fveq2d
    eqtr4d
    @161
    @67
    c.0
    @142
    @97
    @140
    @161
    @66
    @13
    c.0
    @161
    @11
    @71
    @62
    @165
    @96
    @92
    @19
    @160
    @131
    ad2antrr
    eqneltrd
    iffalsed
    @161
    @142
    @97
    c.1
    @141
    co
    #
    @97
    @161
    @99
    c.1
    @97
    @141
    @161
    @98
    c.1
    c.0
    @165
    iftrued
    oveq2d
    @96
    @166
    @97
    wceq
    #
    @19
    @160
    @96
    @87
    @158
    @167
    @136
    @134
    @16
    cR
    @141
    c.1
    @97
    @17
    @157
    mplcoe1.o
    ringridm
    syl2anc
    ad2antrr
    eqtrd
    oveq12d
    @161
    @77
    @13
    c.0
    @160
    @77
    @147
    @11
    @72
    @62
    elun2
    adantl
    iftrued
    3eqtr4d
    @147
    @160
    wn
    #
    wa
    #
    @67
    c.0
    @140
    co
    #
    @67
    @143
    @78
    @147
    @170
    @67
    wceq
    #
    @168
    @147
    @88
    @67
    @16
    wcel
    @171
    wph
    @88
    @95
    @19
    @90
    ad2antrr
    @150
    @16
    @140
    cR
    @67
    c.0
    @17
    @144
    mplcoe1.z
    grprid
    syl2anc
    adantr
    @169
    @142
    c.0
    @67
    @140
    @169
    @142
    @97
    c.0
    @141
    co
    #
    c.0
    @169
    @99
    c.0
    @97
    @141
    @169
    @98
    c.1
    c.0
    @169
    @160
    @98
    @147
    @168
    simpr
    @164
    sylnib
    iffalsed
    oveq2d
    @96
    @172
    c.0
    wceq
    #
    @19
    @168
    @96
    @87
    @158
    @173
    @136
    @134
    @16
    cR
    @141
    @97
    c.0
    @17
    @157
    mplcoe1.z
    ringrz
    syl2anc
    ad2antrr
    eqtrd
    oveq2d
    @169
    @77
    @66
    @13
    c.0
    @168
    @77
    @66
    wb
    @147
    @168
    @66
    @160
    @66
    wo
    #
    @77
    @160
    @66
    biorf
    @77
    @66
    @160
    wo
    @174
    @11
    @62
    @72
    elun
    @66
    @160
    orcom
    bitri
    syl6rbbr
    adantl
    ifbid
    3eqtr4d
    pm2.61dan
    mpteq2dva
    3eqtrrd
    eqeq12d
    syl5ibr
    expr
    a2d
    syl5
    expcom
    a2d
    findcard2s
    mpcom
    mpd
    eqtr4d
    wph
    cP
    @9
    @0
    cres
    #
    cgsu
    co
    @8
    @10
    wph
    @175
    @7
    cP
    cgsu
    wph
    vk
    cD
    @0
    @6
    @38
    resmptd
    oveq2d
    wph
    cD
    cB
    @9
    cP
    cvv
    @0
    @58
    mplcoe1.b
    @83
    @109
    @29
    wph
    vk
    cD
    @6
    cB
    @9
    @129
    @9
    eqid
    fmptd
    wph
    cD
    @6
    vk
    cvv
    @0
    @58
    wph
    @1
    @23
    wcel
    #
    wa
    #
    @6
    c.0
    @5
    c.x
    co
    #
    @58
    @177
    @2
    c.0
    @5
    c.x
    wph
    cD
    @16
    cvv
    cX
    cvv
    @0
    @1
    c.0
    @18
    @26
    @29
    @33
    suppssr
    oveq1d
    @176
    wph
    @111
    @178
    @58
    wceq
    @1
    cD
    @0
    eldifi
    @114
    @178
    @116
    c0g
    cfv
    #
    @5
    c.x
    co
    #
    @58
    @114
    c.0
    @179
    @5
    c.x
    @114
    c.0
    @31
    @179
    mplcoe1.z
    @114
    cR
    @116
    c0g
    @125
    fveq2d
    syl5eq
    oveq1d
    @114
    @115
    @118
    @180
    @58
    wceq
    @122
    @126
    c.x
    @116
    @179
    cB
    cP
    @5
    @58
    mplcoe1.b
    @127
    mplcoe1.n
    @179
    eqid
    @83
    lmod0vs
    syl2anc
    eqtrd
    sylan2
    eqtrd
    @29
    suppss2
    #
    wph
    @9
    cvv
    wcel
    #
    @9
    wfun
    #
    @58
    cvv
    wcel
    #
    w3a
    #
    @39
    @9
    @58
    csupp
    co
    @0
    wss
    @9
    @58
    cfsupp
    wbr
    @185
    wph
    @182
    @183
    @184
    vk
    cD
    @6
    @28
    mptex
    vk
    cD
    @6
    funmpt
    cP
    c0g
    fvex
    3pm3.2i
    a1i
    @47
    @181
    @0
    @9
    cvv
    cvv
    @58
    suppssfifsupp
    syl12anc
    gsumres
    eqtr3d
    eqtrd
end
