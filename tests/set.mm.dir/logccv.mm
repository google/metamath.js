include "crp.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cneg.mm"
include "cicc.mm"
include "cv.mm"
include "cmpt.mm"
include "cdiv.mm"
include "crn.mm"
include "simpl1.mm"
include "rpred.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cr.mm"
include "ccncf.mm"
include "wf.mm"
include "cpnf.mm"
include "wss.mm"
include "rpgt0d.mm"
include "ltpnf.mm"
include "syl.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "iccssioo.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "ioorp.mm"
include "syl6sseq.mm"
include "sselda.mm"
include "relogcld.mm"
include "renegcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wb.mm"
include "ax-resscn.mm"
include "cres.mm"
include "resabs1d.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "relogcn.mm"
include "sselii.mm"
include "rescncf.mm"
include "mpisyl.mm"
include "eqeltrrd.mm"
include "fvres.mm"
include "negeqd.mm"
include "mpteq2ia.mm"
include "eqcomi.mm"
include "negfcncf.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"
include "cdv.mm"
include "wiso.mm"
include "wor.mm"
include "wpo.mm"
include "wfo.mm"
include "wi.mm"
include "wral.mm"
include "ioossre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "ioossicc.mm"
include "syl5ss.mm"
include "rprecred.mm"
include "frn.mm"
include "sopo.mm"
include "wfn.mm"
include "negex.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "adantrl.mm"
include "adantrr.mm"
include "ltnegd.mm"
include "ltrecd.mm"
include "wceq.mm"
include "oveq2.mm"
include "fvmpt.mm"
include "breqan12d.mm"
include "adantl.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "soisoi.mm"
include "syl22anc.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cvv.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "relogcl.mm"
include "recnd.mm"
include "negcld.mm"
include "ovexd.mm"
include "dvrelog.mm"
include "wf1o.mm"
include "relogf1o.mm"
include "f1of.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "dvmptneg.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptres2.mm"
include "isoeq1.mm"
include "simpr.mm"
include "dvcvx.mm"
include "ax-1cn.mm"
include "elioore.mm"
include "nncan.mm"
include "oveq1d.mm"
include "sseldi.mm"
include "iirev.mm"
include "lincmb01cmp.mm"
include "syl31anc.mm"
include "fveq2.mm"
include "cle.mm"
include "rpxrd.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "mulneg2d.mm"
include "eqtrd.mm"
include "ubicc2.mm"
include "1re.mm"
include "resubcl.mm"
include "oveq12d.mm"
include "remulcld.mm"
include "negdid.mm"
include "eqtr4d.mm"
include "3brtr3d.mm"
include "readdcld.mm"
include "sseldd.mm"

theorem logccv
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. RR+ /\ B e. RR+ /\ A < B ) /\ T e. ( 0 (,) 1 ) ) -> ( ( T x. ( log ` A ) ) + ( ( 1 - T ) x. ( log ` B ) ) ) < ( log ` ( ( T x. A ) + ( ( 1 - T ) x. B ) ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cT
    cc0
    c1
    cioo
    co
    #
    wcel
    #
    wa
    #
    cT
    cA
    clog
    cfv
    #
    cmul
    co
    #
    c1
    cT
    cmin
    co
    #
    cB
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cT
    cA
    cmul
    co
    #
    @9
    cB
    cmul
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    clt
    wbr
    @16
    cneg
    #
    @12
    cneg
    #
    clt
    wbr
    @6
    @15
    vx
    cA
    cB
    cicc
    co
    #
    vx
    cv
    #
    clog
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    cT
    cA
    @23
    cfv
    #
    cmul
    co
    #
    @9
    cB
    @23
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @17
    @18
    clt
    @6
    cA
    cB
    @15
    cT
    @23
    vx
    cA
    cB
    cioo
    co
    #
    c1
    @20
    cdiv
    co
    #
    cneg
    #
    cmpt
    #
    crn
    #
    @6
    cA
    @0
    @1
    @2
    @5
    simpl1
    #
    rpred
    #
    @6
    cB
    @0
    @1
    @2
    @5
    simpl2
    #
    rpred
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    @6
    @23
    @19
    cr
    ccncf
    co
    wcel
    #
    @19
    cr
    @23
    wf
    #
    @6
    vx
    @19
    @22
    cr
    @23
    @6
    @20
    @19
    wcel
    #
    wa
    #
    @21
    @43
    @20
    @6
    @19
    crp
    @20
    @6
    @19
    cc0
    cpnf
    cioo
    co
    #
    crp
    @6
    cc0
    cA
    clt
    wbr
    #
    cB
    cpnf
    clt
    wbr
    #
    @19
    @44
    wss
    #
    @6
    cA
    @35
    rpgt0d
    @6
    cB
    cr
    wcel
    #
    @46
    @38
    cB
    ltpnf
    syl
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @45
    @46
    wa
    @47
    0xr
    pnfxr
    cc0
    cpnf
    cA
    cB
    iccssioo
    mpanl12
    syl2anc
    ioorp
    syl6sseq
    #
    sselda
    relogcld
    renegcld
    @23
    eqid
    #
    fmptd
    @6
    cr
    cc
    wss
    #
    @23
    @19
    cc
    ccncf
    co
    #
    wcel
    #
    @40
    @41
    wb
    ax-resscn
    @6
    clog
    @19
    cres
    #
    @52
    wcel
    @53
    @6
    clog
    crp
    cres
    #
    @19
    cres
    #
    @54
    @52
    @6
    clog
    @19
    crp
    @49
    resabs1d
    @6
    @19
    crp
    wss
    @55
    crp
    cc
    ccncf
    co
    #
    wcel
    @56
    @52
    wcel
    @49
    crp
    cr
    ccncf
    co
    #
    @57
    @55
    @51
    cc
    cc
    wss
    @58
    @57
    wss
    ax-resscn
    cc
    ssid
    crp
    cr
    cc
    cncfss
    mp2an
    relogcn
    sselii
    crp
    cc
    @19
    @55
    rescncf
    mpisyl
    eqeltrrd
    vx
    @19
    @54
    @23
    vx
    @19
    @20
    @54
    cfv
    #
    cneg
    #
    cmpt
    @23
    vx
    @19
    @60
    @22
    @42
    @59
    @21
    @20
    @19
    clog
    fvres
    negeqd
    mpteq2ia
    eqcomi
    negfcncf
    syl
    @19
    cc
    cr
    @23
    cncffvrn
    sylancr
    mpbird
    @6
    @30
    @34
    clt
    clt
    cr
    @23
    cdv
    co
    #
    wiso
    #
    @30
    @34
    clt
    clt
    @33
    wiso
    #
    @6
    @30
    clt
    wor
    #
    @34
    clt
    wpo
    #
    @30
    @34
    @33
    wfo
    #
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @67
    @33
    cfv
    #
    @68
    @33
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vz
    @30
    wral
    vy
    @30
    wral
    @63
    @64
    @6
    @30
    cr
    wss
    cr
    clt
    wor
    #
    @64
    cA
    cB
    ioossre
    ltso
    @30
    cr
    clt
    soss
    mp2
    a1i
    @6
    @34
    clt
    wor
    #
    @65
    @6
    @34
    cr
    wss
    #
    @74
    @75
    @6
    @30
    cr
    @33
    wf
    @76
    @6
    vx
    @30
    @32
    cr
    @33
    @6
    @20
    @30
    wcel
    wa
    #
    @31
    @77
    @20
    @6
    @30
    crp
    @20
    @6
    @30
    @19
    crp
    cA
    cB
    ioossicc
    @49
    syl5ss
    #
    sselda
    rprecred
    renegcld
    @33
    eqid
    #
    fmptd
    @30
    cr
    @33
    frn
    syl
    ltso
    @34
    cr
    clt
    soss
    mpisyl
    @34
    clt
    sopo
    syl
    @66
    @6
    @33
    @30
    wfn
    @66
    vx
    @30
    @32
    @33
    @31
    negex
    #
    @79
    fnmpti
    @30
    @33
    dffn4
    mpbi
    a1i
    @6
    @73
    vy
    vz
    @30
    @30
    @6
    @67
    @30
    wcel
    #
    @68
    @30
    wcel
    #
    wa
    #
    wa
    #
    @69
    @72
    @84
    c1
    @68
    cdiv
    co
    #
    c1
    @67
    cdiv
    co
    #
    clt
    wbr
    @86
    cneg
    #
    @85
    cneg
    #
    clt
    wbr
    #
    @69
    @72
    @84
    @85
    @86
    @84
    @68
    @6
    @82
    @68
    crp
    wcel
    @81
    @6
    @30
    crp
    @68
    @78
    sselda
    adantrl
    #
    rprecred
    @84
    @67
    @6
    @81
    @67
    crp
    wcel
    @82
    @6
    @30
    crp
    @67
    @78
    sselda
    adantrr
    #
    rprecred
    ltnegd
    @84
    @67
    @68
    @91
    @90
    ltrecd
    @83
    @72
    @89
    wb
    @6
    @81
    @82
    @70
    @87
    @71
    @88
    clt
    vx
    @67
    @32
    @87
    @30
    @33
    @20
    @67
    wceq
    @31
    @86
    @20
    @67
    c1
    cdiv
    oveq2
    negeqd
    @79
    @86
    negex
    fvmpt
    vx
    @68
    @32
    @88
    @30
    @33
    @20
    @68
    wceq
    @31
    @85
    @20
    @68
    c1
    cdiv
    oveq2
    negeqd
    @79
    @85
    negex
    fvmpt
    breqan12d
    adantl
    3bitr4d
    biimpd
    ralrimivva
    vy
    vz
    @30
    @34
    clt
    clt
    @33
    soisoi
    syl22anc
    @6
    @61
    @33
    wceq
    @62
    @63
    wb
    @6
    vx
    @22
    @32
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cvv
    crp
    @30
    @19
    cr
    cr
    cc
    cpr
    wcel
    @6
    reelprrecn
    a1i
    #
    @6
    @20
    crp
    wcel
    #
    wa
    #
    @21
    @96
    @21
    @95
    @21
    cr
    wcel
    @6
    @20
    relogcl
    adantl
    recnd
    #
    negcld
    @32
    cvv
    wcel
    @96
    @80
    a1i
    @6
    vx
    @21
    @31
    cr
    cvv
    crp
    @94
    @97
    @96
    c1
    @20
    cdiv
    ovexd
    @6
    vx
    crp
    @31
    cmpt
    cr
    @55
    cdv
    co
    cr
    vx
    crp
    @21
    cmpt
    #
    cdv
    co
    vx
    dvrelog
    @6
    @55
    @98
    cr
    cdv
    @6
    @55
    vx
    crp
    @20
    @55
    cfv
    #
    cmpt
    @98
    @6
    vx
    crp
    cr
    @55
    crp
    cr
    @55
    wf1o
    crp
    cr
    @55
    wf
    @6
    relogf1o
    crp
    cr
    @55
    f1of
    mp1i
    feqmptd
    vx
    crp
    @99
    @21
    @20
    crp
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    dvmptneg
    @49
    @93
    @93
    eqid
    #
    tgioo2
    @100
    @6
    cA
    cr
    wcel
    #
    @48
    @19
    @92
    cnt
    cfv
    cfv
    @30
    wceq
    @36
    @38
    cA
    cB
    iccntr
    syl2anc
    dvmptres2
    @30
    @34
    clt
    clt
    @33
    @61
    isoeq1
    syl
    mpbird
    @3
    @5
    simpr
    #
    @15
    eqid
    dvcvx
    @6
    @15
    @19
    wcel
    @24
    @17
    wceq
    @6
    c1
    @9
    cmin
    co
    #
    cA
    cmul
    co
    #
    @14
    caddc
    co
    #
    @15
    @19
    @6
    @104
    @13
    @14
    caddc
    @6
    @103
    cT
    cA
    cmul
    @6
    c1
    cc
    wcel
    cT
    cc
    wcel
    @103
    cT
    wceq
    ax-1cn
    @6
    cT
    @5
    cT
    cr
    wcel
    #
    @3
    cT
    cc0
    c1
    elioore
    adantl
    #
    recnd
    #
    c1
    cT
    nncan
    sylancr
    oveq1d
    oveq1d
    @6
    @101
    @48
    @2
    @9
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    @105
    @19
    wcel
    @36
    @38
    @39
    @6
    cT
    @109
    wcel
    @110
    @6
    @4
    @109
    cT
    cc0
    c1
    ioossicc
    @102
    sseldi
    cT
    iirev
    syl
    cA
    cB
    @9
    lincmb01cmp
    syl31anc
    eqeltrrd
    #
    vx
    @15
    @22
    @17
    @19
    @23
    @20
    @15
    wceq
    @21
    @16
    @20
    @15
    clog
    fveq2
    negeqd
    @50
    @16
    negex
    fvmpt
    syl
    @6
    @29
    @8
    cneg
    #
    @11
    cneg
    #
    caddc
    co
    @18
    @6
    @26
    @112
    @28
    @113
    caddc
    @6
    @26
    cT
    @7
    cneg
    #
    cmul
    co
    @112
    @6
    @25
    @114
    cT
    cmul
    @6
    cA
    @19
    wcel
    #
    @25
    @114
    wceq
    @6
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @115
    @6
    cA
    @35
    rpxrd
    #
    @6
    cB
    @37
    rpxrd
    #
    @6
    cA
    cB
    @36
    @38
    @39
    ltled
    #
    cA
    cB
    lbicc2
    syl3anc
    vx
    cA
    @22
    @114
    @19
    @23
    @20
    cA
    wceq
    @21
    @7
    @20
    cA
    clog
    fveq2
    negeqd
    @50
    @7
    negex
    fvmpt
    syl
    oveq2d
    @6
    cT
    @7
    @108
    @6
    @7
    @6
    cA
    @35
    relogcld
    #
    recnd
    mulneg2d
    eqtrd
    @6
    @28
    @9
    @10
    cneg
    #
    cmul
    co
    @113
    @6
    @27
    @123
    @9
    cmul
    @6
    cB
    @19
    wcel
    #
    @27
    @123
    wceq
    @6
    @116
    @117
    @118
    @124
    @119
    @120
    @121
    cA
    cB
    ubicc2
    syl3anc
    vx
    cB
    @22
    @123
    @19
    @23
    @20
    cB
    wceq
    @21
    @10
    @20
    cB
    clog
    fveq2
    negeqd
    @50
    @10
    negex
    fvmpt
    syl
    oveq2d
    @6
    @9
    @10
    @6
    @9
    @6
    c1
    cr
    wcel
    @106
    @9
    cr
    wcel
    1re
    @107
    c1
    cT
    resubcl
    sylancr
    #
    recnd
    @6
    @10
    @6
    cB
    @37
    relogcld
    #
    recnd
    mulneg2d
    eqtrd
    oveq12d
    @6
    @8
    @11
    @6
    @8
    @6
    cT
    @7
    @107
    @122
    remulcld
    #
    recnd
    @6
    @11
    @6
    @9
    @10
    @125
    @126
    remulcld
    #
    recnd
    negdid
    eqtr4d
    3brtr3d
    @6
    @12
    @16
    @6
    @8
    @11
    @127
    @128
    readdcld
    @6
    @15
    @6
    @19
    crp
    @15
    @49
    @111
    sseldd
    relogcld
    ltnegd
    mpbird
end
