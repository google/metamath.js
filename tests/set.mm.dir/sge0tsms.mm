include "csumge0.mm"
include "cfv.mm"
include "ctsu.mm"
include "co.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "wceq.mm"
include "eqid.mm"
include "a1i.mm"
include "cvv.mm"
include "wb.mm"
include "xrltso.mm"
include "supex.mm"
include "elsng.mm"
include "syl.mm"
include "mpbird.mm"
include "cpnf.mm"
include "wa.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "wf.mm"
include "simpr.mm"
include "sge0pnfval.mm"
include "wrex.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "wss.mm"
include "wral.mm"
include "iccssxr.mm"
include "elinel1.mm"
include "elpwi.mm"
include "adantl.mm"
include "fssres.mm"
include "syl2anc.mm"
include "cr.mm"
include "elinel2.mm"
include "0red.mm"
include "fdmfifsupp.mm"
include "gsumge0cl.mm"
include "sseldi.mm"
include "ralrimiva.mm"
include "3ad2ant1.mm"
include "rnmptss.mm"
include "snelpwi.mm"
include "snfi.mm"
include "elind.mm"
include "3ad2ant2.mm"
include "snssi.mm"
include "fssresd.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3adant3.mm"
include "cmnd.mm"
include "ccmn.mm"
include "cxrs.mm"
include "cress.mm"
include "xrge0cmn.mm"
include "eqeltri.mm"
include "cmnmnd.mm"
include "ax-mp.mm"
include "simp2.mm"
include "ffvelrnda.mm"
include "cbs.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "ovex.mm"
include "xrsbas.mm"
include "ressbas.mm"
include "eqtri.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "simp3.mm"
include "3eqtrrd.mm"
include "reseq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "pnfxr.mm"
include "elrnmpt.mm"
include "supxrpnf.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "eqtr4d.mm"
include "wn.mm"
include "csu.mm"
include "fge0iccico.mm"
include "sge0reval.mm"
include "cico.mm"
include "feqresmpt.mm"
include "adantlr.mm"
include "cxad.mm"
include "cplusg.mm"
include "fveq2i.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "eqtr2i.mm"
include "oveq1i.mm"
include "icossicc.mm"
include "pm3.2i.mm"
include "ressabs.mm"
include "elexi.mm"
include "0xr.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "wne.mm"
include "id.mm"
include "eqcomd.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "sylan.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "eqeltrd.mm"
include "adantlllr.mm"
include "ad3antrrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "ge0xrre.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "fmptd.mm"
include "0e0icopnf.mm"
include "sseli.mm"
include "xaddid2.mm"
include "xaddid1.mm"
include "jca.mm"
include "gsumress.mm"
include "ccnfld.mm"
include "csubmnd.mm"
include "rege0subm.mm"
include "gsumsubm.mm"
include "eqidd.mm"
include "vex.mm"
include "mptex.mm"
include "ovexd.mm"
include "cc.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "csrg.mm"
include "rge0srg.mm"
include "simpl.mm"
include "srgacl.mm"
include "syl6eleq.mm"
include "sseldd.mm"
include "caddc.mm"
include "rexadd.mm"
include "cnfldadd.mm"
include "eqtr3i.mm"
include "eqtr4i.mm"
include "oveqi.mm"
include "3eqtr4d.mm"
include "funmpt.mm"
include "gsumpropd2.mm"
include "3eqtrd.mm"
include "recnd.mm"
include "gsumfsum.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "pm2.61dan.mm"
include "xrge0tsms.mm"
include "eleq12d.mm"

theorem sge0tsms
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume sge0tsms.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume sge0tsms.x: |- ( ph -> X e. V )
  assume sge0tsms.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( sum^ ` F ) e. ( G tsums F ) )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cG
    cF
    ctsu
    co
    #
    wcel
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    cG
    cF
    vx
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @9
    csn
    #
    wcel
    #
    wph
    @11
    @9
    @9
    wceq
    #
    @12
    wph
    @9
    eqid
    #
    a1i
    wph
    @9
    cvv
    wcel
    #
    @11
    @12
    wb
    @14
    wph
    cxr
    @8
    clt
    xrltso
    supex
    a1i
    @9
    @9
    cvv
    elsng
    syl
    mpbird
    wph
    @0
    @9
    @1
    @10
    wph
    cpnf
    cF
    crn
    #
    wcel
    #
    @0
    @9
    wceq
    wph
    @16
    wa
    #
    @0
    cpnf
    @9
    @17
    cF
    cV
    cX
    wph
    cX
    cV
    wcel
    #
    @16
    sge0tsms.x
    adantr
    wph
    cX
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @16
    sge0tsms.f
    adantr
    wph
    @16
    simpr
    #
    sge0pnfval
    @17
    vy
    cv
    #
    cF
    cfv
    #
    cpnf
    wceq
    #
    vy
    cX
    wrex
    #
    @9
    cpnf
    wceq
    #
    @17
    @16
    @25
    @21
    @17
    cF
    cX
    wfn
    #
    @16
    @25
    wb
    wph
    @27
    @16
    wph
    @20
    @27
    sge0tsms.f
    cX
    @19
    cF
    ffn
    syl
    adantr
    vy
    cX
    cpnf
    cF
    fvelrnb
    syl
    mpbid
    @17
    @24
    @26
    vy
    cX
    wph
    @22
    cX
    wcel
    #
    @24
    @26
    wi
    wi
    @16
    wph
    @28
    @24
    @26
    wph
    @28
    @24
    w3a
    #
    @8
    cxr
    wss
    #
    cpnf
    @8
    wcel
    #
    @26
    @29
    @6
    cxr
    wcel
    #
    vx
    @3
    wral
    #
    @30
    wph
    @28
    @33
    @24
    wph
    @32
    vx
    @3
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @19
    cxr
    @6
    cc0
    cpnf
    iccssxr
    #
    @35
    @5
    cG
    @3
    @4
    sge0tsms.g
    wph
    @34
    simpr
    #
    @35
    @20
    @4
    cX
    wss
    #
    @4
    @19
    @5
    wf
    wph
    @20
    @34
    sge0tsms.f
    adantr
    #
    @34
    @38
    wph
    @34
    @4
    @2
    wcel
    @38
    @4
    @2
    cfn
    elinel1
    @4
    cX
    elpwi
    syl
    #
    adantl
    #
    cX
    @19
    @4
    cF
    fssres
    syl2anc
    #
    @35
    @4
    @19
    @5
    cr
    cc0
    @42
    @34
    @4
    cfn
    wcel
    #
    wph
    @4
    @2
    cfn
    elinel2
    #
    adantl
    @35
    0red
    fdmfifsupp
    gsumge0cl
    sseldi
    ralrimiva
    3ad2ant1
    vx
    @3
    @6
    cxr
    @7
    @7
    eqid
    #
    rnmptss
    syl
    @29
    @31
    cpnf
    @6
    wceq
    #
    vx
    @3
    wrex
    #
    @29
    @22
    csn
    #
    @3
    wcel
    #
    cpnf
    cG
    cF
    @48
    cres
    #
    cgsu
    co
    #
    wceq
    #
    @47
    @28
    wph
    @49
    @24
    @28
    @2
    cfn
    @48
    @22
    cX
    snelpwi
    @48
    cfn
    wcel
    @28
    @22
    snfi
    a1i
    elind
    3ad2ant2
    @29
    @51
    cG
    vx
    @48
    @4
    cF
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @23
    cpnf
    wph
    @28
    @51
    @55
    wceq
    @24
    wph
    @28
    wa
    #
    @50
    @54
    cG
    cgsu
    @56
    @50
    vx
    @48
    @4
    @50
    cfv
    #
    cmpt
    #
    @54
    @56
    vx
    @48
    @19
    @50
    @56
    cX
    @19
    @48
    cF
    wph
    @20
    @28
    sge0tsms.f
    adantr
    @28
    @48
    cX
    wss
    wph
    @22
    cX
    snssi
    adantl
    fssresd
    feqmptd
    @58
    @54
    wceq
    @56
    vx
    @48
    @57
    @53
    @4
    @48
    cF
    fvres
    mpteq2ia
    a1i
    eqtrd
    oveq2d
    3adant3
    @29
    cG
    cmnd
    wcel
    #
    @28
    @23
    @19
    wcel
    #
    @55
    @23
    wceq
    @59
    @29
    cG
    ccmn
    wcel
    @59
    cG
    cxrs
    @19
    cress
    co
    #
    ccmn
    sge0tsms.g
    xrge0cmn
    eqeltri
    #
    cG
    cmnmnd
    ax-mp
    a1i
    wph
    @28
    @24
    simp2
    wph
    @28
    @60
    @24
    wph
    cX
    @19
    @22
    cF
    sge0tsms.f
    ffvelrnda
    3adant3
    @53
    @19
    @23
    vx
    cG
    @22
    cX
    @19
    @19
    cxr
    cin
    #
    cG
    cbs
    cfv
    #
    @63
    @19
    @19
    cxr
    wss
    @63
    @19
    wceq
    @36
    @19
    cxr
    df-ss
    mpbi
    eqcomi
    @19
    cvv
    wcel
    #
    @63
    @64
    wceq
    cc0
    cpnf
    cicc
    ovex
    #
    @19
    cxr
    cG
    cvv
    cxrs
    sge0tsms.g
    xrsbas
    ressbas
    ax-mp
    eqtri
    #
    @4
    @22
    cF
    fveq2
    gsumsn
    syl3anc
    wph
    @28
    @24
    simp3
    3eqtrrd
    @46
    @52
    vx
    @48
    @3
    @4
    @48
    wceq
    #
    @6
    @51
    cpnf
    @68
    @5
    @50
    cG
    cgsu
    @4
    @48
    cF
    reseq2
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    @29
    cpnf
    cxr
    wcel
    #
    @31
    @47
    wb
    @69
    @29
    pnfxr
    a1i
    vx
    @3
    @6
    cpnf
    @7
    cxr
    @45
    elrnmpt
    syl
    mpbird
    @8
    supxrpnf
    syl2anc
    3exp
    adantr
    rexlimdv
    mpd
    eqtr4d
    wph
    @16
    wn
    #
    wa
    #
    @0
    vx
    @3
    @4
    @23
    vy
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    @9
    @71
    vx
    vy
    cF
    cV
    cX
    wph
    @18
    @70
    sge0tsms.x
    adantr
    @71
    cF
    cX
    wph
    @20
    @70
    sge0tsms.f
    adantr
    #
    wph
    @70
    simpr
    #
    fge0iccico
    sge0reval
    @71
    cxr
    @74
    @8
    clt
    @71
    @73
    @7
    @71
    vx
    @3
    @72
    @6
    @71
    @34
    wa
    #
    @6
    cG
    vy
    @4
    @23
    cmpt
    #
    cgsu
    co
    cxrs
    cc0
    cpnf
    cico
    co
    #
    cress
    co
    #
    @78
    cgsu
    co
    #
    @72
    @77
    @5
    @78
    cG
    cgsu
    wph
    @34
    @5
    @78
    wceq
    @70
    @35
    vy
    cX
    @19
    @4
    cF
    @39
    @41
    feqresmpt
    adantlr
    oveq2d
    @77
    vy
    @4
    @19
    cxad
    @79
    @78
    cG
    @80
    cvv
    @3
    cc0
    @67
    cG
    cplusg
    cfv
    @61
    cplusg
    cfv
    #
    cxad
    cG
    @61
    cplusg
    sge0tsms.g
    fveq2i
    cxad
    @82
    @65
    cxad
    @82
    wceq
    @66
    @19
    cxad
    cxrs
    @61
    cvv
    @61
    eqid
    xrsadd
    ressplusg
    ax-mp
    eqcomi
    eqtr2i
    cG
    @79
    cress
    co
    @61
    @79
    cress
    co
    #
    @80
    cG
    @61
    @79
    cress
    sge0tsms.g
    oveq1i
    @65
    @79
    @19
    wss
    #
    wa
    @83
    @80
    wceq
    @65
    @84
    @66
    cc0
    cpnf
    icossicc
    #
    pm3.2i
    @19
    @79
    cxrs
    cvv
    ressabs
    ax-mp
    eqtr2i
    cG
    cvv
    wcel
    @77
    cG
    ccmn
    @62
    elexi
    a1i
    @71
    @34
    simpr
    #
    @84
    @77
    @85
    a1i
    @77
    vy
    @4
    @23
    @79
    @78
    @77
    @22
    @4
    wcel
    #
    wa
    #
    cc0
    cpnf
    @23
    cc0
    cxr
    wcel
    #
    @88
    0xr
    a1i
    #
    @69
    @88
    pnfxr
    a1i
    #
    @88
    @19
    cxr
    @23
    @36
    @88
    cX
    @19
    @22
    cF
    @71
    @20
    @34
    @87
    @75
    ad2antrr
    @34
    @87
    @28
    @71
    @34
    @4
    cX
    @22
    @40
    sselda
    #
    adantll
    ffvelrnd
    #
    sseldi
    @88
    @89
    @69
    @60
    cc0
    @23
    cle
    wbr
    @90
    @91
    @93
    cc0
    cpnf
    @23
    iccgelb
    syl3anc
    @88
    @23
    @88
    @60
    @23
    cpnf
    wne
    @23
    cr
    wcel
    @93
    @88
    @23
    cpnf
    @88
    @24
    @16
    wph
    @34
    @87
    @24
    @16
    @70
    @35
    @87
    wa
    #
    @24
    wa
    cpnf
    @23
    @15
    @24
    cpnf
    @23
    wceq
    @94
    @24
    @23
    cpnf
    @24
    id
    eqcomd
    adantl
    @94
    @23
    @15
    wcel
    #
    @24
    @94
    cF
    wfun
    #
    @22
    cF
    cdm
    #
    wcel
    @95
    wph
    @96
    @34
    @87
    wph
    @20
    @96
    sge0tsms.f
    cX
    @19
    cF
    ffun
    syl
    ad2antrr
    @94
    @22
    cX
    @97
    @35
    @34
    @87
    @28
    @37
    @92
    sylan
    wph
    cX
    @97
    wceq
    @34
    @87
    wph
    @97
    cX
    wph
    @20
    @97
    cX
    wceq
    sge0tsms.f
    cX
    @19
    cF
    fdm
    syl
    eqcomd
    ad2antrr
    eleqtrd
    @22
    cF
    fvelrn
    syl2anc
    adantr
    eqeltrd
    adantlllr
    @71
    @70
    @34
    @87
    @24
    @76
    ad3antrrr
    pm2.65da
    neqned
    @23
    ge0xrre
    syl2anc
    #
    ltpnfd
    elicod
    #
    @78
    eqid
    #
    fmptd
    #
    cc0
    @79
    wcel
    @77
    0e0icopnf
    a1i
    @22
    @19
    wcel
    #
    cc0
    @22
    cxad
    co
    @22
    wceq
    #
    @22
    cc0
    cxad
    co
    @22
    wceq
    #
    wa
    #
    @77
    @102
    @22
    cxr
    wcel
    #
    @105
    @19
    cxr
    @22
    @36
    sseli
    @106
    @103
    @104
    @22
    xaddid2
    @22
    xaddid1
    jca
    syl
    adantl
    gsumress
    @77
    ccnfld
    @78
    cgsu
    co
    #
    @81
    @72
    @77
    @107
    ccnfld
    @79
    cress
    co
    #
    @78
    cgsu
    co
    #
    @109
    @81
    @77
    @4
    @79
    @78
    ccnfld
    @108
    @3
    @86
    @79
    ccnfld
    csubmnd
    cfv
    #
    wcel
    @77
    rege0subm
    a1i
    @101
    @108
    eqid
    #
    gsumsubm
    @77
    @109
    eqidd
    @77
    vt
    @78
    @108
    @80
    cvv
    cvv
    cvv
    vs
    @78
    cvv
    wcel
    @77
    vy
    @4
    @23
    vx
    vex
    mptex
    a1i
    @77
    ccnfld
    @79
    cress
    ovexd
    @77
    cxrs
    @79
    cress
    ovexd
    @108
    cbs
    cfv
    #
    @80
    cbs
    cfv
    #
    wceq
    @77
    @112
    @79
    @113
    @79
    @112
    @79
    cc
    wss
    @79
    @112
    wceq
    @79
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    @79
    cc
    @108
    ccnfld
    @111
    cnfldbas
    ressbas2
    ax-mp
    #
    eqcomi
    #
    @79
    cxr
    wss
    @79
    @113
    wceq
    @79
    @19
    cxr
    @85
    @36
    sstri
    @79
    cxr
    @80
    cxrs
    @80
    eqid
    #
    xrsbas
    ressbas2
    ax-mp
    eqtri
    a1i
    vs
    cv
    #
    @112
    wcel
    #
    vt
    cv
    #
    @112
    wcel
    #
    wa
    #
    @117
    @119
    @108
    cplusg
    cfv
    #
    co
    #
    @112
    wcel
    #
    @77
    @121
    @108
    csrg
    wcel
    #
    @118
    @120
    @124
    @125
    @121
    rge0srg
    a1i
    @118
    @120
    simpl
    @118
    @120
    simpr
    @112
    @122
    @108
    @117
    @119
    @112
    eqid
    @122
    eqid
    srgacl
    syl3anc
    adantl
    @121
    @123
    @117
    @119
    @80
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    @77
    @121
    @117
    cr
    wcel
    #
    @119
    cr
    wcel
    #
    @128
    @118
    @129
    @120
    @118
    @79
    cr
    @117
    @79
    cr
    wss
    #
    @118
    rge0ssre
    a1i
    @118
    @117
    @112
    @79
    @118
    id
    @115
    syl6eleq
    sseldd
    adantr
    @120
    @130
    @118
    @120
    @79
    cr
    @119
    @131
    @120
    rge0ssre
    a1i
    @120
    @119
    @112
    @79
    @120
    id
    @115
    syl6eleq
    sseldd
    adantl
    @129
    @130
    wa
    #
    @117
    @119
    caddc
    co
    #
    @117
    @119
    cxad
    co
    #
    @123
    @127
    @132
    @134
    @133
    @117
    @119
    rexadd
    eqcomd
    @123
    @133
    wceq
    @132
    @122
    caddc
    @117
    @119
    @122
    ccnfld
    cplusg
    cfv
    #
    caddc
    caddc
    @122
    @135
    @79
    cvv
    wcel
    #
    caddc
    @122
    wceq
    @79
    @110
    rege0subm
    elexi
    #
    @79
    caddc
    ccnfld
    @108
    cvv
    @111
    cnfldadd
    ressplusg
    ax-mp
    cnfldadd
    eqtr3i
    cnfldadd
    eqtr4i
    oveqi
    a1i
    @127
    @134
    wceq
    @132
    @126
    cxad
    @117
    @119
    cxad
    @126
    @136
    cxad
    @126
    wceq
    @137
    @79
    cxad
    cxrs
    @80
    cvv
    @116
    xrsadd
    ressplusg
    ax-mp
    eqcomi
    oveqi
    a1i
    3eqtr4d
    syl2anc
    adantl
    @78
    wfun
    @77
    vy
    @4
    @23
    funmpt
    a1i
    @77
    @23
    @112
    wcel
    #
    vy
    @4
    wral
    @78
    crn
    @112
    wss
    @77
    @138
    vy
    @4
    @88
    @23
    @79
    @112
    @99
    @114
    syl6eleq
    ralrimiva
    vy
    @4
    @23
    @112
    @78
    @100
    rnmptss
    syl
    gsumpropd2
    3eqtrd
    @77
    @4
    @23
    vy
    @34
    @43
    @71
    @44
    adantl
    @88
    @23
    @98
    recnd
    gsumfsum
    eqtr3d
    3eqtrrd
    mpteq2dva
    rneqd
    supeq1d
    eqtrd
    pm2.61dan
    wph
    cX
    @9
    cF
    cG
    cV
    vx
    sge0tsms.g
    sge0tsms.x
    sge0tsms.f
    @13
    xrge0tsms
    eleq12d
    mpbird
end
