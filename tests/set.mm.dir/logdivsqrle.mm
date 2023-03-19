include "crp.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "csqrt.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cle.mm"
include "cc0.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioorp.mm"
include "eqcomi.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "relogcld.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "wne.mm"
include "rpsqrtcl.mm"
include "rpne0.mm"
include "syl.mm"
include "adantl.mm"
include "redivcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cdv.mm"
include "c1.mm"
include "c2.mm"
include "cneg.mm"
include "ccxp.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "ccncf.mm"
include "cc.mm"
include "rpcn.mm"
include "logcld.mm"
include "sqrtcld.mm"
include "divrecd.mm"
include "2cnd.mm"
include "adantr.mm"
include "2ne0.mm"
include "a1i.mm"
include "reccld.mm"
include "cxpnegd.mm"
include "wceq.mm"
include "cxpsqrt.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "rpreccld.mm"
include "cres.mm"
include "dvrelog.mm"
include "csn.mm"
include "cdif.mm"
include "crn.mm"
include "wf.mm"
include "wf1o.mm"
include "logf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "wss.mm"
include "wn.mm"
include "ssriv.mm"
include "0nrp.mm"
include "ssdifsn.mm"
include "mpbir2an.mm"
include "feqresmpt.mm"
include "syl5reqr.mm"
include "1cnd.mm"
include "halfcld.mm"
include "negcld.mm"
include "cxpcld.mm"
include "subcld.mm"
include "mulcld.mm"
include "dvcxp1.mm"
include "dvmptmul.mm"
include "ax-resscn.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ctx.mm"
include "ccn.mm"
include "addcn.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "difss.mm"
include "cncfmptid.mm"
include "sylancl.mm"
include "divcncf.mm"
include "cmnf.mm"
include "cioc.mm"
include "wi.mm"
include "ax-1.mm"
include "jca.mm"
include "ellogdm.mm"
include "sylibr.mm"
include "cxpcncf1.mm"
include "mulcncf.mm"
include "cncfss.mm"
include "mp2an.mm"
include "relogcn.mm"
include "syl6eqelr.mm"
include "sseldi.mm"
include "cncfmpt2f.mm"
include "rpre.mm"
include "rereccld.mm"
include "rpge0.mm"
include "halfre.mm"
include "renegcli.mm"
include "recxpcld.mm"
include "remulcld.mm"
include "1re.mm"
include "resubcli.mm"
include "relogcl.mm"
include "readdcld.mm"
include "cncffvrn.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "eqeltrd.mm"
include "fveq1d.mm"
include "cxpadd.mm"
include "syl211anc.mm"
include "mulid2d.mm"
include "negsubd.mm"
include "mulcomd.mm"
include "cxpneg.mm"
include "cxp1d.mm"
include "eqtr2d.mm"
include "3eqtr4rd.mm"
include "mul32d.mm"
include "oveq12d.mm"
include "adddird.mm"
include "cvv.mm"
include "eqidd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cicc.mm"
include "ioossicc.mm"
include "fct2relem.mm"
include "sstrd.mm"
include "sselda.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "0red.mm"
include "rpcxpcl.mm"
include "rpge0d.mm"
include "wbr.mm"
include "2cn.mm"
include "mulid2i.mm"
include "ce.mm"
include "2re.mm"
include "reefcld.mm"
include "clt.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "letrd.mm"
include "reeflog.mm"
include "breqtrrd.mm"
include "wb.mm"
include "efle.mm"
include "sylancr.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "2rp.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "divrec2d.mm"
include "breqtrd.mm"
include "mulneg1d.mm"
include "subnegd.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "leaddsub.mm"
include "lemul1ad.mm"
include "mul02d.mm"
include "eqbrtrd.mm"
include "fdvnegge.mm"
include "ovex.mm"
include "3brtr3d.mm"

theorem logdivsqrle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume logdivsqrle.a: |- ( ph -> A e. RR+ )
  assume logdivsqrle.b: |- ( ph -> B e. RR+ )
  assume logdivsqrle.1: |- ( ph -> ( exp ` 2 ) <_ A )
  assume logdivsqrle.2: |- ( ph -> A <_ B )


  assert |- ( ph -> ( ( log ` B ) / ( sqrt ` B ) ) <_ ( ( log ` A ) / ( sqrt ` A ) ) )

  proof
    wph
    cB
    vx
    crp
    vx
    cv
    #
    clog
    cfv
    #
    @0
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    cA
    @4
    cfv
    cB
    clog
    cfv
    #
    cB
    csqrt
    cfv
    #
    cdiv
    co
    #
    cA
    clog
    cfv
    #
    cA
    csqrt
    cfv
    #
    cdiv
    co
    #
    cle
    wph
    vy
    cA
    cB
    cc0
    cpnf
    crp
    @4
    cc0
    cpnf
    cioo
    co
    crp
    ioorp
    eqcomi
    #
    logdivsqrle.a
    logdivsqrle.b
    wph
    vx
    crp
    @3
    cr
    @4
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @1
    @2
    @13
    @0
    wph
    @12
    simpr
    #
    relogcld
    @13
    @2
    @13
    @0
    @14
    rpsqrtcld
    rpred
    @12
    @2
    cc0
    wne
    #
    wph
    @12
    @2
    crp
    wcel
    @15
    @0
    rpsqrtcl
    @2
    rpne0
    syl
    adantl
    #
    redivcld
    @4
    eqid
    fmptd
    wph
    cr
    @4
    cdv
    co
    #
    vx
    crp
    c1
    @0
    cdiv
    co
    #
    @0
    c1
    c2
    cdiv
    co
    #
    cneg
    #
    ccxp
    co
    #
    cmul
    co
    #
    @20
    @0
    @20
    c1
    cmin
    co
    #
    ccxp
    co
    #
    cmul
    co
    #
    @1
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    crp
    cr
    ccncf
    co
    #
    wph
    @17
    cr
    vx
    crp
    @1
    @21
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    @28
    wph
    @4
    @31
    cr
    cdv
    wph
    vx
    crp
    @3
    @30
    @13
    @3
    @1
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    @30
    @13
    @1
    @2
    @13
    @0
    @12
    @0
    cc
    wcel
    #
    wph
    @0
    rpcn
    #
    adantl
    #
    @12
    @0
    cc0
    wne
    #
    wph
    @0
    rpne0
    #
    adantl
    #
    logcld
    #
    @13
    @0
    @35
    sqrtcld
    @16
    divrecd
    @13
    @21
    @32
    @1
    cmul
    @13
    @21
    c1
    @0
    @19
    ccxp
    co
    #
    cdiv
    co
    @32
    @13
    @0
    @19
    @35
    @38
    @13
    c2
    wph
    c2
    cc
    wcel
    #
    @12
    wph
    2cnd
    #
    adantr
    c2
    cc0
    wne
    #
    @13
    2ne0
    a1i
    reccld
    cxpnegd
    @13
    @40
    @2
    c1
    cdiv
    @13
    @33
    @40
    @2
    wceq
    @35
    @0
    cxpsqrt
    syl
    oveq2d
    eqtrd
    oveq2d
    eqtr4d
    mpteq2dva
    oveq2d
    wph
    vx
    @1
    @18
    @21
    @25
    cr
    crp
    cc
    crp
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @39
    @13
    @0
    @14
    rpreccld
    #
    wph
    vx
    crp
    @18
    cmpt
    cr
    clog
    crp
    cres
    #
    cdv
    co
    cr
    vx
    crp
    @1
    cmpt
    #
    cdv
    co
    vx
    dvrelog
    wph
    @45
    @46
    cr
    cdv
    wph
    vx
    cc
    cc0
    csn
    #
    cdif
    #
    clog
    crn
    #
    crp
    clog
    @48
    @49
    clog
    wf
    #
    wph
    @48
    @49
    clog
    wf1o
    @50
    logf1o
    @48
    @49
    clog
    f1of
    ax-mp
    a1i
    crp
    @48
    wss
    #
    wph
    @51
    crp
    cc
    wss
    #
    cc0
    crp
    wcel
    wn
    vx
    crp
    cc
    @34
    ssriv
    #
    0nrp
    crp
    cc
    cc0
    ssdifsn
    mpbir2an
    a1i
    #
    feqresmpt
    #
    oveq2d
    syl5reqr
    @13
    @0
    @20
    @35
    wph
    @20
    cc
    wcel
    #
    @12
    wph
    @19
    wph
    c1
    wph
    1cnd
    #
    halfcld
    #
    negcld
    #
    adantr
    #
    cxpcld
    #
    @13
    @20
    @24
    @60
    @13
    @0
    @23
    @35
    @13
    @20
    c1
    @60
    wph
    c1
    cc
    wcel
    #
    @12
    @57
    adantr
    #
    subcld
    cxpcld
    #
    mulcld
    wph
    @56
    cr
    vx
    crp
    @21
    cmpt
    cdv
    co
    vx
    crp
    @25
    cmpt
    wceq
    @59
    vx
    @20
    dvcxp1
    syl
    dvmptmul
    eqtrd
    #
    wph
    cr
    cc
    wss
    #
    @28
    crp
    cc
    ccncf
    co
    #
    wcel
    #
    crp
    cr
    @28
    wf
    #
    @28
    @29
    wcel
    #
    @66
    wph
    ax-resscn
    a1i
    wph
    vx
    @22
    @26
    caddc
    ccnfld
    ctopn
    cfv
    #
    crp
    @71
    eqid
    #
    caddc
    @71
    @71
    ctx
    co
    @71
    ccn
    co
    wcel
    wph
    @71
    @72
    addcn
    a1i
    wph
    vx
    @18
    @21
    crp
    wph
    vx
    c1
    @0
    crp
    wph
    @62
    @52
    cc
    cc
    wss
    #
    vx
    crp
    c1
    cmpt
    @67
    wcel
    @57
    @52
    wph
    @53
    a1i
    #
    @73
    wph
    cc
    ssid
    #
    a1i
    #
    vx
    c1
    crp
    cc
    cncfmptc
    syl3anc
    wph
    @51
    @48
    cc
    wss
    vx
    crp
    @0
    cmpt
    crp
    @48
    ccncf
    co
    wcel
    @54
    cc
    @47
    difss
    vx
    crp
    @48
    cncfmptid
    sylancl
    divcncf
    wph
    vx
    @20
    crp
    @59
    crp
    cc
    cmnf
    cc0
    cioc
    co
    cdif
    #
    wss
    wph
    vx
    crp
    @77
    @12
    @33
    @0
    cr
    wcel
    #
    @12
    wi
    #
    wa
    @0
    @77
    wcel
    @12
    @33
    @79
    @34
    @12
    @78
    ax-1
    jca
    @0
    @77
    @77
    eqid
    ellogdm
    sylibr
    ssriv
    a1i
    #
    cxpcncf1
    mulcncf
    wph
    vx
    @25
    @1
    crp
    wph
    vx
    @20
    @24
    crp
    wph
    @56
    @52
    @73
    vx
    crp
    @20
    cmpt
    @67
    wcel
    @59
    @74
    @76
    vx
    @20
    crp
    cc
    cncfmptc
    syl3anc
    wph
    vx
    @23
    crp
    wph
    @20
    c1
    @59
    @57
    subcld
    @80
    cxpcncf1
    mulcncf
    wph
    @29
    @67
    @46
    @66
    @73
    @29
    @67
    wss
    ax-resscn
    @75
    crp
    cr
    cc
    cncfss
    mp2an
    wph
    @46
    @45
    @29
    @55
    relogcn
    syl6eqelr
    sseldi
    mulcncf
    cncfmpt2f
    wph
    vx
    crp
    @27
    cr
    @28
    @12
    @27
    cr
    wcel
    wph
    @12
    @22
    @26
    @12
    @18
    @21
    @12
    @0
    @0
    rpre
    #
    @37
    rereccld
    @12
    @0
    @20
    @81
    @0
    rpge0
    #
    @20
    cr
    wcel
    #
    @12
    @19
    halfre
    renegcli
    #
    a1i
    #
    recxpcld
    remulcld
    @12
    @25
    @1
    @12
    @20
    @24
    @85
    @12
    @0
    @23
    @81
    @82
    @23
    cr
    wcel
    #
    @12
    @20
    c1
    @84
    1re
    resubcli
    #
    a1i
    recxpcld
    remulcld
    @0
    relogcl
    remulcld
    readdcld
    adantl
    @28
    eqid
    fmptd
    @66
    @68
    wa
    @70
    @69
    crp
    cc
    cr
    @28
    cncffvrn
    biimpar
    syl21anc
    eqeltrd
    logdivsqrle.2
    wph
    vy
    cv
    #
    cA
    cB
    cioo
    co
    #
    wcel
    #
    wa
    #
    @88
    @17
    cfv
    #
    @88
    @28
    cfv
    #
    cc0
    cle
    wph
    @92
    @93
    wceq
    @90
    wph
    @88
    @17
    @28
    @65
    fveq1d
    adantr
    @91
    @93
    @88
    vx
    crp
    c1
    @20
    @1
    cmul
    co
    #
    caddc
    co
    #
    @24
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    cc0
    cle
    wph
    @93
    @98
    wceq
    @90
    wph
    @88
    @28
    @97
    wph
    vx
    crp
    @27
    @96
    @13
    @27
    c1
    @24
    cmul
    co
    #
    @94
    @24
    cmul
    co
    #
    caddc
    co
    @96
    @13
    @22
    @99
    @26
    @100
    caddc
    @13
    @0
    @20
    c1
    cneg
    #
    caddc
    co
    #
    ccxp
    co
    #
    @21
    @0
    @101
    ccxp
    co
    #
    cmul
    co
    #
    @99
    @22
    @13
    @33
    @36
    @56
    @101
    cc
    wcel
    @103
    @105
    wceq
    @35
    @38
    @60
    @13
    c1
    @63
    negcld
    @0
    @20
    @101
    cxpadd
    syl211anc
    @13
    @99
    @24
    @103
    @13
    @24
    @64
    mulid2d
    @13
    @102
    @23
    @0
    ccxp
    @13
    @20
    c1
    @60
    @63
    negsubd
    oveq2d
    eqtr4d
    @13
    @22
    @21
    @18
    cmul
    co
    @105
    @13
    @18
    @21
    @13
    crp
    cc
    @18
    @53
    @44
    sseldi
    @61
    mulcomd
    @13
    @18
    @104
    @21
    cmul
    @13
    @104
    c1
    @0
    c1
    ccxp
    co
    #
    cdiv
    co
    #
    @18
    @13
    @33
    @36
    @62
    @104
    @107
    wceq
    @35
    @38
    @63
    @0
    c1
    cxpneg
    syl3anc
    @13
    @106
    @0
    c1
    cdiv
    @13
    @0
    @35
    cxp1d
    oveq2d
    eqtr2d
    oveq2d
    eqtrd
    3eqtr4rd
    @13
    @20
    @24
    @1
    @60
    @64
    @39
    mul32d
    oveq12d
    @13
    c1
    @94
    @24
    @63
    @13
    @20
    @1
    @60
    @39
    mulcld
    @64
    adddird
    eqtr4d
    mpteq2dva
    fveq1d
    adantr
    @91
    @98
    c1
    @20
    @88
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @88
    @23
    ccxp
    co
    #
    cmul
    co
    #
    cc0
    cle
    @91
    vx
    @88
    @96
    @112
    crp
    @97
    cvv
    @91
    @97
    eqidd
    @91
    @0
    @88
    wceq
    #
    wa
    #
    @95
    @110
    @24
    @111
    cmul
    @114
    @94
    @109
    c1
    caddc
    @114
    @1
    @108
    @20
    cmul
    @114
    @0
    @88
    clog
    @91
    @113
    simpr
    #
    fveq2d
    oveq2d
    oveq2d
    @114
    @0
    @88
    @23
    ccxp
    @115
    oveq1d
    oveq12d
    wph
    @89
    crp
    @88
    wph
    @89
    cA
    cB
    cicc
    co
    #
    crp
    @89
    @116
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    wph
    cA
    cB
    cc0
    cpnf
    crp
    @11
    logdivsqrle.a
    logdivsqrle.b
    fct2relem
    sstrd
    sselda
    #
    @91
    @110
    @111
    cmul
    ovexd
    fvmptd
    @91
    @112
    cc0
    @111
    cmul
    co
    cc0
    cle
    @91
    @110
    cc0
    @111
    @91
    c1
    @109
    c1
    cr
    wcel
    #
    @91
    1re
    a1i
    #
    @91
    @20
    @108
    @83
    @91
    @84
    a1i
    @91
    @88
    @117
    relogcld
    #
    remulcld
    #
    readdcld
    @91
    0red
    #
    @91
    @111
    @91
    @88
    crp
    wcel
    #
    @86
    @111
    crp
    wcel
    @117
    @87
    @88
    @23
    rpcxpcl
    sylancl
    #
    rpred
    @91
    @111
    @124
    rpge0d
    @91
    @110
    cc0
    cle
    wbr
    #
    c1
    cc0
    @109
    cmin
    co
    #
    cle
    wbr
    #
    @91
    c1
    @19
    @108
    cmul
    co
    #
    @126
    cle
    @91
    c1
    @108
    c2
    cdiv
    co
    #
    @128
    cle
    @91
    c1
    c2
    cmul
    co
    #
    @108
    cle
    wbr
    c1
    @129
    cle
    wbr
    @91
    @130
    c2
    @108
    cle
    c2
    2cn
    mulid2i
    @91
    c2
    @108
    cle
    wbr
    #
    c2
    ce
    cfv
    #
    @108
    ce
    cfv
    #
    cle
    wbr
    #
    @91
    @132
    @88
    @133
    cle
    @91
    @132
    cA
    @88
    @91
    c2
    c2
    cr
    wcel
    #
    @91
    2re
    a1i
    reefcld
    wph
    cA
    cr
    wcel
    @90
    wph
    cA
    logdivsqrle.a
    rpred
    adantr
    #
    @91
    @88
    @117
    rpred
    #
    wph
    @132
    cA
    cle
    wbr
    @90
    logdivsqrle.1
    adantr
    @91
    cA
    @88
    @136
    @137
    @90
    cA
    @88
    clt
    wbr
    #
    wph
    @90
    @138
    @88
    cB
    clt
    wbr
    @88
    cA
    cB
    eliooord
    simpld
    adantl
    ltled
    letrd
    @91
    @123
    @133
    @88
    wceq
    @117
    @88
    reeflog
    syl
    breqtrrd
    @91
    @135
    @108
    cr
    wcel
    @131
    @134
    wb
    2re
    @120
    c2
    @108
    efle
    sylancr
    mpbird
    syl5eqbr
    @91
    c1
    @108
    c2
    @119
    @120
    c2
    crp
    wcel
    @91
    2rp
    a1i
    lemuldivd
    mpbid
    @91
    @108
    c2
    @91
    cr
    cc
    @108
    ax-resscn
    @120
    sseldi
    #
    wph
    @41
    @90
    @42
    adantr
    @43
    @91
    2ne0
    a1i
    divrec2d
    breqtrd
    @91
    @126
    cc0
    @128
    cneg
    #
    cmin
    co
    cc0
    @128
    caddc
    co
    @128
    @91
    @109
    @140
    cc0
    cmin
    @91
    @19
    @108
    wph
    @19
    cc
    wcel
    @90
    @58
    adantr
    #
    @139
    mulneg1d
    oveq2d
    @91
    cc0
    @128
    @91
    cr
    cc
    cc0
    ax-resscn
    @122
    sseldi
    @91
    @19
    @108
    @141
    @139
    mulcld
    #
    subnegd
    @91
    @128
    @142
    addid2d
    3eqtrd
    breqtrrd
    @91
    @118
    @109
    cr
    wcel
    cc0
    cr
    wcel
    @125
    @127
    wb
    @119
    @121
    @122
    c1
    @109
    cc0
    leaddsub
    syl3anc
    mpbird
    lemul1ad
    @91
    @111
    @91
    crp
    cc
    @111
    @53
    @124
    sseldi
    mul02d
    breqtrd
    eqbrtrd
    eqbrtrd
    eqbrtrd
    fdvnegge
    wph
    vx
    cB
    @3
    @7
    crp
    @4
    cvv
    wph
    @4
    eqidd
    #
    wph
    @0
    cB
    wceq
    #
    wa
    #
    @1
    @5
    @2
    @6
    cdiv
    @145
    @0
    cB
    clog
    wph
    @144
    simpr
    #
    fveq2d
    @145
    @0
    cB
    csqrt
    @146
    fveq2d
    oveq12d
    logdivsqrle.b
    @7
    cvv
    wcel
    wph
    @5
    @6
    cdiv
    ovex
    a1i
    fvmptd
    wph
    vx
    cA
    @3
    @10
    crp
    @4
    cvv
    @143
    wph
    @0
    cA
    wceq
    #
    wa
    #
    @1
    @8
    @2
    @9
    cdiv
    @148
    @0
    cA
    clog
    wph
    @147
    simpr
    #
    fveq2d
    @148
    @0
    cA
    csqrt
    @149
    fveq2d
    oveq12d
    logdivsqrle.a
    @10
    cvv
    wcel
    wph
    @8
    @9
    cdiv
    ovex
    a1i
    fvmptd
    3brtr3d
end
