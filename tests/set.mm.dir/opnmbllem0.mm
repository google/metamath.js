include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cicc.mm"
include "cv.mm"
include "wss.mm"
include "cz.mm"
include "cn0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "cmpt2.mm"
include "crab.mm"
include "cima.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "weq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "elrab.mm"
include "simprr.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "iccf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "ssrab2.mm"
include "cle.mm"
include "cr.mm"
include "cin.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "dyadf.mm"
include "frn.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funimass4.mm"
include "mp2an.mm"
include "sspwuni.mm"
include "sylib.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cres.mm"
include "cbl.mm"
include "crp.mm"
include "wrex.mm"
include "cxmt.mm"
include "eqid.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "wceq.mm"
include "elssuni.mm"
include "uniretop.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "rpre.mm"
include "bl2ioo.mm"
include "syl2an.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "2re.mm"
include "1lt2.mm"
include "expnlbnd.mm"
include "mp3an23.mm"
include "ad2antrl.mm"
include "cmul.mm"
include "cfl.mm"
include "ad2antrr.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnred.mm"
include "remulcld.mm"
include "fllelt.mm"
include "syl.mm"
include "simpld.mm"
include "cc0.mm"
include "reflcl.mm"
include "nngt0d.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "peano2re.mm"
include "nndivred.mm"
include "simprd.mm"
include "ltmuldiv.mm"
include "mpbid.mm"
include "ltled.mm"
include "w3a.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "flcld.mm"
include "dyadval.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "wfn.mm"
include "ffn.mm"
include "fnovrn.mm"
include "simplrl.mm"
include "rpred.mm"
include "resubcld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "recnd.mm"
include "1cnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "nnrecred.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "lttrd.mm"
include "ltsubaddd.mm"
include "leadd1dd.mm"
include "lelttrd.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "eqsstrd.mm"
include "simplrr.mm"
include "sstrd.mm"
include "sylanbrc.mm"
include "wi.mm"
include "funfvima2.mm"
include "elunii.mm"
include "rexlimddv.mm"
include "expr.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem opnmbllem0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint n r
  disjoint n s
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint r s
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  assert |- ( A e. ( topGen ` ran (,) ) -> U. ( [,] " { z e. ran ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. ) | ( [,] ` z ) C_ A } ) = A )

  proof
    cA
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    cicc
    vz
    cv
    #
    cicc
    cfv
    #
    cA
    wss
    #
    vz
    vx
    vy
    cz
    cn0
    vx
    cv
    #
    c2
    vy
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @5
    c1
    caddc
    co
    #
    @7
    cdiv
    co
    #
    cop
    #
    cmpt2
    #
    crn
    #
    crab
    #
    cima
    #
    cuni
    #
    cA
    @1
    @15
    cA
    cpw
    #
    wss
    #
    @16
    cA
    wss
    @1
    vw
    cv
    #
    cicc
    cfv
    #
    @17
    wcel
    #
    vw
    @14
    wral
    #
    @18
    @1
    @21
    vw
    @14
    @19
    @14
    wcel
    @1
    @19
    @13
    wcel
    #
    @20
    cA
    wss
    #
    wa
    #
    @21
    @4
    @24
    vz
    @19
    @13
    vz
    vw
    weq
    @3
    @20
    cA
    @2
    @19
    cicc
    fveq2
    sseq1d
    elrab
    @1
    @25
    wa
    @24
    @21
    @1
    @23
    @24
    simprr
    @20
    cA
    @19
    cicc
    fvex
    elpw
    sylibr
    sylan2b
    ralrimiva
    cicc
    wfun
    #
    @14
    cicc
    cdm
    #
    wss
    #
    @18
    @22
    wb
    cxr
    cxr
    cxp
    #
    cxr
    cpw
    #
    cicc
    wf
    @26
    iccf
    @29
    @30
    cicc
    ffun
    ax-mp
    #
    @14
    @29
    @27
    @14
    @13
    @29
    @4
    vz
    @13
    ssrab2
    @13
    cle
    cr
    cr
    cxp
    #
    cin
    #
    @29
    cz
    cn0
    cxp
    #
    @33
    @12
    wf
    #
    @13
    @33
    wss
    vr
    vs
    @12
    vx
    vy
    vr
    vs
    cz
    cn0
    @11
    vr
    cv
    #
    c2
    vs
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @36
    c1
    caddc
    co
    #
    @38
    cdiv
    co
    #
    cop
    @36
    @7
    cdiv
    co
    #
    @40
    @7
    cdiv
    co
    #
    cop
    vx
    vr
    weq
    #
    @8
    @42
    @10
    @43
    @5
    @36
    @7
    cdiv
    oveq1
    @44
    @9
    @40
    @7
    cdiv
    @5
    @36
    c1
    caddc
    oveq1
    oveq1d
    opeq12d
    vy
    vs
    weq
    #
    @42
    @39
    @43
    @41
    @45
    @7
    @38
    @36
    cdiv
    @6
    @37
    c2
    cexp
    oveq2
    #
    oveq2d
    @45
    @7
    @38
    @40
    cdiv
    @46
    oveq2d
    opeq12d
    cbvmpt2v
    #
    dyadf
    #
    @34
    @33
    @12
    frn
    ax-mp
    @33
    @32
    @29
    cle
    @32
    inss2
    rexpssxrxp
    sstri
    sstri
    sstri
    @29
    @30
    cicc
    iccf
    fdmi
    sseqtr4i
    #
    vw
    @14
    @17
    cicc
    funimass4
    mp2an
    sylibr
    @15
    cA
    sspwuni
    sylib
    @1
    vw
    cA
    @16
    @1
    @19
    cA
    wcel
    #
    @19
    @16
    wcel
    #
    @1
    @50
    wa
    #
    @19
    @36
    cabs
    cmin
    ccom
    @32
    cres
    #
    cbl
    cfv
    co
    #
    cA
    wss
    #
    vr
    crp
    wrex
    #
    @51
    @53
    cr
    cxmt
    cfv
    wcel
    @1
    @50
    @56
    @53
    @53
    eqid
    #
    rexmet
    vr
    cA
    @53
    @19
    @0
    cr
    @53
    @53
    cmopn
    cfv
    #
    @57
    @58
    eqid
    tgioo
    mopni2
    mp3an1
    @52
    @55
    @51
    vr
    crp
    @52
    @36
    crp
    wcel
    #
    wa
    #
    @55
    @19
    @36
    cmin
    co
    #
    @19
    @36
    caddc
    co
    #
    cioo
    co
    #
    cA
    wss
    #
    @51
    @60
    @54
    @63
    cA
    @52
    @19
    cr
    wcel
    #
    @36
    cr
    wcel
    @54
    @63
    wceq
    @59
    @1
    cA
    cr
    @19
    @1
    cA
    @0
    cuni
    cr
    cA
    @0
    elssuni
    uniretop
    syl6sseqr
    sselda
    #
    @36
    rpre
    @19
    @36
    @53
    @57
    bl2ioo
    syl2an
    sseq1d
    @52
    @59
    @64
    @51
    @52
    @59
    @64
    wa
    #
    wa
    #
    c1
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @36
    clt
    wbr
    #
    @51
    vn
    cn
    @59
    @72
    vn
    cn
    wrex
    #
    @52
    @64
    @59
    c2
    cr
    wcel
    c1
    c2
    clt
    wbr
    @73
    2re
    1lt2
    @36
    c2
    vn
    expnlbnd
    mp3an23
    ad2antrl
    @68
    @69
    cn
    wcel
    #
    @72
    wa
    #
    wa
    #
    @19
    @19
    @70
    cmul
    co
    #
    cfl
    cfv
    #
    @69
    @12
    co
    #
    cicc
    cfv
    #
    wcel
    @80
    @15
    wcel
    #
    @51
    @76
    @19
    @78
    @70
    cdiv
    co
    #
    @78
    c1
    caddc
    co
    #
    @70
    cdiv
    co
    #
    cicc
    co
    #
    @80
    @76
    @19
    @85
    wcel
    #
    @65
    @82
    @19
    cle
    wbr
    #
    @19
    @84
    cle
    wbr
    #
    @52
    @65
    @67
    @75
    @66
    ad2antrr
    #
    @76
    @87
    @78
    @77
    cle
    wbr
    #
    @76
    @90
    @77
    @83
    clt
    wbr
    #
    @76
    @77
    cr
    wcel
    #
    @90
    @91
    wa
    @76
    @19
    @70
    @89
    @76
    @70
    @76
    c2
    cn
    wcel
    @69
    cn0
    wcel
    #
    @70
    cn
    wcel
    2nn
    @74
    @93
    @68
    @72
    @69
    nnnn0
    ad2antrl
    #
    c2
    @69
    nnexpcl
    sylancr
    #
    nnred
    #
    remulcld
    #
    @77
    fllelt
    syl
    #
    simpld
    @76
    @78
    cr
    wcel
    #
    @65
    @70
    cr
    wcel
    #
    cc0
    @70
    clt
    wbr
    #
    @87
    @90
    wb
    @76
    @92
    @99
    @97
    @77
    reflcl
    syl
    #
    @89
    @96
    @76
    @70
    @95
    nngt0d
    #
    @78
    @19
    @70
    ledivmul2
    syl112anc
    mpbird
    #
    @76
    @19
    @84
    @89
    @76
    @83
    @70
    @76
    @99
    @83
    cr
    wcel
    #
    @102
    @78
    peano2re
    syl
    #
    @95
    nndivred
    #
    @76
    @91
    @19
    @84
    clt
    wbr
    #
    @76
    @90
    @91
    @98
    simprd
    @76
    @65
    @105
    @100
    @101
    @91
    @108
    wb
    @89
    @106
    @96
    @103
    @19
    @83
    @70
    ltmuldiv
    syl112anc
    mpbid
    #
    ltled
    @76
    @82
    cr
    wcel
    @84
    cr
    wcel
    @86
    @65
    @87
    @88
    w3a
    wb
    @76
    @78
    @70
    @102
    @95
    nndivred
    #
    @107
    @82
    @84
    @19
    elicc2
    syl2anc
    mpbir3and
    @76
    @80
    @82
    @84
    cop
    #
    cicc
    cfv
    @85
    @76
    @79
    @111
    cicc
    @76
    @78
    cz
    wcel
    #
    @93
    @79
    @111
    wceq
    @76
    @77
    @97
    flcld
    #
    @94
    vr
    vs
    @78
    @69
    @12
    @47
    dyadval
    syl2anc
    fveq2d
    @82
    @84
    cicc
    df-ov
    syl6eqr
    #
    eleqtrrd
    @76
    @79
    @14
    wcel
    #
    @81
    @76
    @79
    @13
    wcel
    #
    @80
    cA
    wss
    #
    @115
    @76
    @112
    @93
    @116
    @113
    @94
    @12
    @34
    wfn
    #
    @112
    @93
    @116
    @35
    @118
    @48
    @34
    @33
    @12
    ffn
    ax-mp
    cz
    cn0
    @78
    @69
    @12
    fnovrn
    mp3an1
    syl2anc
    @76
    @80
    @63
    cA
    @76
    @80
    @85
    @63
    @114
    @76
    @61
    cxr
    wcel
    @62
    cxr
    wcel
    @61
    @82
    clt
    wbr
    #
    @84
    @62
    clt
    wbr
    @85
    @63
    wss
    @76
    @61
    @76
    @19
    @36
    @89
    @76
    @36
    @52
    @59
    @64
    @75
    simplrl
    rpred
    #
    resubcld
    rexrd
    @76
    @62
    @76
    @19
    @36
    @89
    @120
    readdcld
    #
    rexrd
    @76
    @119
    @19
    @82
    @36
    caddc
    co
    #
    clt
    wbr
    @76
    @19
    @84
    @122
    @89
    @107
    @76
    @82
    @36
    @110
    @120
    readdcld
    @109
    @76
    @84
    @82
    @71
    caddc
    co
    #
    @122
    clt
    @76
    @78
    c1
    @70
    @76
    @78
    @102
    recnd
    @76
    1cnd
    @76
    @70
    @96
    recnd
    @76
    @70
    @95
    nnne0d
    divdird
    #
    @76
    @71
    @36
    @82
    @76
    @70
    @95
    nnrecred
    #
    @120
    @110
    @68
    @74
    @72
    simprr
    #
    ltadd2dd
    eqbrtrd
    lttrd
    @76
    @19
    @36
    @82
    @89
    @120
    @110
    ltsubaddd
    mpbird
    @76
    @84
    @19
    @71
    caddc
    co
    #
    @62
    @107
    @76
    @19
    @71
    @89
    @125
    readdcld
    @121
    @76
    @84
    @123
    @127
    cle
    @124
    @76
    @82
    @19
    @71
    @110
    @89
    @125
    @104
    leadd1dd
    eqbrtrd
    @76
    @71
    @36
    @19
    @125
    @120
    @89
    @126
    ltadd2dd
    lelttrd
    @61
    @62
    @82
    @84
    iccssioo
    syl22anc
    eqsstrd
    @52
    @59
    @64
    @75
    simplrr
    sstrd
    @4
    @117
    vz
    @79
    @13
    @2
    @79
    wceq
    @3
    @80
    cA
    @2
    @79
    cicc
    fveq2
    sseq1d
    elrab
    sylanbrc
    @26
    @28
    @115
    @81
    wi
    @31
    @49
    @14
    @79
    cicc
    funfvima2
    mp2an
    syl
    @19
    @80
    @15
    elunii
    syl2anc
    rexlimddv
    expr
    sylbid
    rexlimdva
    mpd
    ex
    ssrdv
    eqssd
end
