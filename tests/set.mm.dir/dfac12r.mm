include "cv.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "cr1.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "csuc.mm"
include "cfv.mm"
include "wrex.mm"
include "rankwflemb.mm"
include "wa.mm"
include "char.mm"
include "cen.mm"
include "wbr.mm"
include "wi.mm"
include "harcl.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "cardid2.mm"
include "ensym.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "cvv.mm"
include "crn.mm"
include "crnk.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "cep.mm"
include "coi.mm"
include "ccnv.mm"
include "ccom.mm"
include "cif.mm"
include "cmpt.mm"
include "crecs.mm"
include "simpr.mm"
include "wf1.mm"
include "f1of1.mm"
include "adantr.mm"
include "cardon.mm"
include "onssi.mm"
include "f1ss.mm"
include "sylancl.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "suceq.mm"
include "syl.mm"
include "fveq2d.mm"
include "id.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "imaeq2.mm"
include "ifeq12d.mm"
include "cbvmptv.mm"
include "dmeq.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "rneq.mm"
include "rneqd.mm"
include "oveq1d.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "oieq2.mm"
include "cnveqd.mm"
include "coeq12d.mm"
include "imaeq1d.mm"
include "ifbieq12d.mm"
include "mpteq12dv.mm"
include "syl5eq.mm"
include "recseq.mm"
include "dfac12lem3.mm"
include "ex.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "4syl.mm"
include "imp.mm"
include "r1suc.mm"
include "adantl.mm"
include "eleq2d.mm"
include "elpwi.mm"
include "syl6bi.mm"
include "ssnum.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "onwf.mm"
include "sseli.mm"
include "pwwf.mm"
include "sylib.mm"
include "ssel.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "impbii.mm"

theorem dfac12r
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x e. On ~P x e. dom card <-> U. ( R1 " On ) C_ dom card )

  proof
    vx
    cv
    #
    cpw
    #
    ccrd
    cdm
    #
    wcel
    #
    vx
    con0
    wral
    #
    cr1
    con0
    cima
    cuni
    #
    @2
    wss
    #
    @4
    vy
    @5
    @2
    vy
    cv
    #
    @5
    wcel
    @7
    vz
    cv
    #
    csuc
    cr1
    cfv
    #
    wcel
    #
    vz
    con0
    wrex
    @4
    @7
    @2
    wcel
    #
    vz
    @7
    rankwflemb
    @4
    @10
    @11
    vz
    con0
    @4
    @8
    con0
    wcel
    #
    wa
    #
    @8
    cr1
    cfv
    #
    @2
    wcel
    #
    @10
    @7
    @14
    wss
    #
    @11
    @4
    @12
    @15
    @4
    @14
    char
    cfv
    #
    cpw
    #
    @2
    wcel
    #
    @18
    ccrd
    cfv
    #
    @18
    cen
    wbr
    @18
    @20
    cen
    wbr
    #
    @12
    @15
    wi
    #
    @17
    con0
    wcel
    @4
    @19
    wi
    @14
    harcl
    @3
    @19
    vx
    @17
    con0
    @0
    @17
    wceq
    @1
    @18
    @2
    @0
    @17
    pweq
    eleq1d
    rspcv
    ax-mp
    @18
    cardid2
    @20
    @18
    ensym
    @21
    @18
    @20
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @22
    @18
    @20
    vf
    bren
    @24
    @22
    vf
    @24
    @12
    @15
    @24
    @12
    wa
    #
    va
    vb
    @8
    @23
    vx
    cvv
    vy
    @0
    cdm
    #
    cr1
    cfv
    #
    @26
    @26
    cuni
    #
    wceq
    #
    @0
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    csuc
    #
    @7
    crnk
    cfv
    #
    comu
    co
    #
    @7
    @35
    csuc
    #
    @0
    cfv
    #
    cfv
    #
    coa
    co
    #
    @28
    @0
    cfv
    #
    crn
    #
    cep
    coi
    #
    ccnv
    #
    @41
    ccom
    #
    @7
    cima
    #
    @23
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    crecs
    #
    @24
    @12
    simpr
    @25
    @18
    @20
    @23
    wf1
    #
    @20
    con0
    wss
    @18
    con0
    @23
    wf1
    @24
    @52
    @12
    @18
    @20
    @23
    f1of1
    adantr
    @20
    @18
    cardon
    onssi
    @18
    @20
    con0
    @23
    f1ss
    sylancl
    @50
    va
    cvv
    vb
    va
    cv
    #
    cdm
    #
    cr1
    cfv
    #
    @54
    @54
    cuni
    #
    wceq
    #
    @53
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    csuc
    #
    vb
    cv
    #
    crnk
    cfv
    #
    comu
    co
    #
    @63
    @64
    csuc
    #
    @53
    cfv
    #
    cfv
    #
    coa
    co
    #
    @56
    @53
    cfv
    #
    crn
    #
    cep
    coi
    #
    ccnv
    #
    @70
    ccom
    #
    @63
    cima
    #
    @23
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    wceq
    @51
    @79
    crecs
    wceq
    vx
    va
    cvv
    @49
    @78
    @0
    @53
    wceq
    #
    @49
    vb
    @27
    @29
    @34
    @64
    comu
    co
    #
    @63
    @66
    @0
    cfv
    #
    cfv
    #
    coa
    co
    #
    @45
    @63
    cima
    #
    @23
    cfv
    #
    cif
    #
    cmpt
    @78
    vy
    vb
    @27
    @48
    @87
    @7
    @63
    wceq
    #
    @29
    @40
    @84
    @47
    @86
    @88
    @36
    @81
    @39
    @83
    coa
    @88
    @35
    @64
    @34
    comu
    @7
    @63
    crnk
    fveq2
    #
    oveq2d
    @88
    @7
    @63
    @38
    @82
    @88
    @37
    @66
    @0
    @88
    @35
    @64
    wceq
    @37
    @66
    wceq
    @89
    @35
    @64
    suceq
    syl
    fveq2d
    @88
    id
    fveq12d
    oveq12d
    @88
    @46
    @85
    @23
    @7
    @63
    @45
    imaeq2
    fveq2d
    ifeq12d
    cbvmptv
    @80
    vb
    @27
    @87
    @55
    @77
    @80
    @26
    @54
    cr1
    @0
    @53
    dmeq
    #
    fveq2d
    @80
    @29
    @57
    @84
    @86
    @69
    @76
    @80
    @26
    @54
    @28
    @56
    @90
    @80
    @26
    @54
    @90
    unieqd
    #
    eqeq12d
    @80
    @81
    @65
    @83
    @68
    coa
    @80
    @34
    @62
    @64
    comu
    @80
    @33
    @61
    wceq
    @34
    @62
    wceq
    @80
    @32
    @60
    @80
    @31
    @59
    @80
    @30
    @58
    @0
    @53
    rneq
    unieqd
    rneqd
    unieqd
    @33
    @61
    suceq
    syl
    oveq1d
    @80
    @63
    @82
    @67
    @66
    @0
    @53
    fveq1
    fveq1d
    oveq12d
    @80
    @85
    @75
    @23
    @80
    @45
    @74
    @63
    @80
    @44
    @73
    @41
    @70
    @80
    @43
    @72
    @80
    @42
    @71
    wceq
    @43
    @72
    wceq
    @80
    @41
    @70
    @80
    @28
    @56
    @0
    @53
    @80
    id
    @91
    fveq12d
    #
    rneqd
    @42
    @71
    cep
    oieq2
    syl
    cnveqd
    @92
    coeq12d
    imaeq1d
    fveq2d
    ifbieq12d
    mpteq12dv
    syl5eq
    cbvmptv
    @50
    @79
    recseq
    ax-mp
    dfac12lem3
    ex
    exlimiv
    sylbi
    4syl
    imp
    @13
    @10
    @7
    @14
    cpw
    #
    wcel
    @16
    @13
    @9
    @93
    @7
    @12
    @9
    @93
    wceq
    @4
    @8
    r1suc
    adantl
    eleq2d
    @7
    @14
    elpwi
    syl6bi
    @14
    @7
    ssnum
    syl6an
    rexlimdva
    syl5bi
    ssrdv
    @6
    @3
    vx
    con0
    @0
    con0
    wcel
    #
    @1
    @5
    wcel
    #
    @6
    @3
    @94
    @0
    @5
    wcel
    @95
    con0
    @5
    @0
    onwf
    sseli
    @0
    pwwf
    sylib
    @5
    @2
    @1
    ssel
    syl5
    ralrimiv
    impbii
end
