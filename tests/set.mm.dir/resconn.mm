include "cr.mm"
include "wss.mm"
include "csconn.mm"
include "wcel.mm"
include "cconn.mm"
include "cpconn.mm"
include "sconnpconn.mm"
include "pconnconn.mm"
include "syl.mm"
include "wa.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "eqid.mm"
include "rerest.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "cc.mm"
include "simpl.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "w3a.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "df-3an.mm"
include "wral.mm"
include "weq.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "cle.mm"
include "wbr.mm"
include "unitssre.mm"
include "sstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "simpr2.mm"
include "sseldd.mm"
include "mulcld.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "simpr1.mm"
include "addcomd.mm"
include "nncan.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "iirev.mm"
include "adantl.mm"
include "eleq1i.mm"
include "reconn.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "r19.21bi.mm"
include "anasss.mm"
include "3adantr3.mm"
include "simplll.mm"
include "remulcld.mm"
include "1re.mm"
include "resubcl.mm"
include "readdcld.mm"
include "recnd.mm"
include "pncan3.mm"
include "sylancl.mm"
include "adddird.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "0re.mm"
include "elicc2i.mm"
include "sylib.mm"
include "simp3d.mm"
include "wb.mm"
include "subge0.mm"
include "mpbird.mm"
include "simplr3.mm"
include "lemul2ad.mm"
include "leadd2dd.mm"
include "eqbrtrrd.mm"
include "simp2d.mm"
include "leadd1dd.mm"
include "breqtrd.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "cbvralv.mm"
include "wloglei.mm"
include "sylan2b.mm"
include "cvxsconn.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "impbid2.mm"

theorem resconn
  let cA: class A
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume resconn.1: |- J = ( ( topGen ` ran (,) ) |`t A )


  assert |- ( A C_ RR -> ( J e. SConn <-> J e. Conn ) )

  proof
    cA
    cr
    wss
    #
    cJ
    csconn
    wcel
    #
    cJ
    cconn
    wcel
    #
    @1
    cJ
    cpconn
    wcel
    @2
    cJ
    sconnpconn
    cJ
    pconnconn
    syl
    @0
    @2
    @1
    @0
    @2
    wa
    #
    ccnfld
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    cJ
    csconn
    @0
    @5
    cJ
    wceq
    @2
    @0
    @5
    cioo
    crn
    ctg
    cfv
    #
    cA
    crest
    co
    #
    cJ
    cA
    @6
    @4
    @4
    eqid
    #
    @6
    eqid
    rerest
    resconn.1
    syl6eqr
    adantr
    @3
    vx
    vy
    vt
    cA
    @4
    @5
    @3
    cA
    cr
    cc
    @0
    @2
    simpl
    #
    ax-resscn
    syl6ss
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    vt
    cv
    #
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    w3a
    @3
    @12
    @14
    wa
    #
    @17
    wa
    @15
    @11
    cmul
    co
    #
    c1
    @15
    cmin
    co
    #
    @13
    cmul
    co
    #
    caddc
    co
    #
    cA
    wcel
    #
    @12
    @14
    @17
    df-3an
    @3
    @18
    @17
    @23
    @3
    @18
    wa
    @23
    vt
    @16
    @3
    @15
    vz
    cv
    #
    cmul
    co
    #
    @20
    vw
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cA
    wcel
    #
    vt
    @16
    wral
    @23
    vt
    @16
    wral
    #
    @15
    @13
    cmul
    co
    #
    @20
    @11
    cmul
    co
    #
    caddc
    co
    #
    cA
    wcel
    #
    vt
    @16
    wral
    #
    vx
    vy
    vz
    vw
    cA
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    @29
    @23
    vt
    @16
    @38
    @28
    @22
    cA
    @36
    @37
    @25
    @19
    @27
    @21
    caddc
    @24
    @11
    @15
    cmul
    oveq2
    @26
    @13
    @20
    cmul
    oveq2
    oveqan12d
    eleq1d
    ralbidv
    vz
    vy
    weq
    #
    vw
    vx
    weq
    #
    wa
    #
    @29
    @34
    vt
    @16
    @41
    @28
    @33
    cA
    @39
    @40
    @25
    @31
    @27
    @32
    caddc
    @24
    @13
    @15
    cmul
    oveq2
    @26
    @11
    @20
    cmul
    oveq2
    oveqan12d
    eleq1d
    ralbidv
    @9
    @3
    @12
    @14
    @11
    @13
    cle
    wbr
    #
    w3a
    #
    wa
    #
    vs
    cv
    #
    @13
    cmul
    co
    #
    c1
    @45
    cmin
    co
    #
    @11
    cmul
    co
    #
    caddc
    co
    #
    cA
    wcel
    #
    vs
    @16
    wral
    @35
    @44
    @50
    vs
    @16
    @44
    @45
    @16
    wcel
    #
    wa
    #
    @49
    @48
    c1
    @47
    cmin
    co
    #
    @13
    cmul
    co
    #
    caddc
    co
    #
    cA
    @52
    @49
    @48
    @46
    caddc
    co
    @55
    @52
    @46
    @48
    @52
    @45
    @13
    @52
    @16
    cc
    @45
    @16
    cr
    cc
    unitssre
    ax-resscn
    sstri
    @44
    @51
    simpr
    sseldi
    #
    @44
    @13
    cc
    wcel
    #
    @51
    @44
    cA
    cc
    @13
    @3
    cA
    cc
    wss
    @43
    @10
    adantr
    #
    @3
    @12
    @14
    @42
    simpr2
    #
    sseldd
    #
    adantr
    mulcld
    @52
    @47
    @11
    @52
    c1
    cc
    wcel
    #
    @45
    cc
    wcel
    #
    @47
    cc
    wcel
    ax-1cn
    @56
    c1
    @45
    subcl
    sylancr
    @44
    @11
    cc
    wcel
    #
    @51
    @44
    cA
    cc
    @11
    @58
    @3
    @12
    @14
    @42
    simpr1
    #
    sseldd
    #
    adantr
    mulcld
    addcomd
    @52
    @54
    @46
    @48
    caddc
    @52
    @53
    @45
    @13
    cmul
    @52
    @61
    @62
    @53
    @45
    wceq
    ax-1cn
    @56
    c1
    @45
    nncan
    sylancr
    oveq1d
    oveq2d
    eqtr4d
    @52
    @47
    @16
    wcel
    #
    @30
    @55
    cA
    wcel
    #
    @51
    @66
    @44
    @45
    iirev
    adantl
    @44
    @30
    @51
    @44
    @23
    vt
    @16
    @44
    @17
    wa
    #
    @11
    @13
    cicc
    co
    #
    cA
    @22
    @44
    @69
    cA
    wss
    #
    @17
    @3
    @12
    @14
    @70
    @42
    @3
    @12
    @14
    @70
    @3
    @12
    wa
    @70
    vy
    cA
    @3
    @70
    vy
    cA
    wral
    #
    vx
    cA
    @0
    @2
    @71
    vx
    cA
    wral
    #
    @2
    @7
    cconn
    wcel
    @0
    @72
    cJ
    @7
    cconn
    resconn.1
    eleq1i
    vx
    vy
    cA
    reconn
    syl5bb
    biimpa
    r19.21bi
    r19.21bi
    anasss
    3adantr3
    adantr
    @68
    @22
    @69
    wcel
    #
    @22
    cr
    wcel
    #
    @11
    @22
    cle
    wbr
    #
    @22
    @13
    cle
    wbr
    #
    @68
    @19
    @21
    @68
    @15
    @11
    @68
    @16
    cr
    @15
    unitssre
    @44
    @17
    simpr
    #
    sseldi
    #
    @68
    cA
    cr
    @11
    @0
    @2
    @43
    @17
    simplll
    #
    @44
    @12
    @17
    @64
    adantr
    sseldd
    #
    remulcld
    #
    @68
    @20
    @13
    @68
    c1
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @20
    cr
    wcel
    1re
    @78
    c1
    @15
    resubcl
    sylancr
    #
    @68
    cA
    cr
    @13
    @79
    @44
    @14
    @17
    @59
    adantr
    sseldd
    #
    remulcld
    #
    readdcld
    @68
    @19
    @32
    caddc
    co
    #
    @11
    @22
    cle
    @68
    @15
    @20
    caddc
    co
    #
    @11
    cmul
    co
    c1
    @11
    cmul
    co
    @87
    @11
    @68
    @88
    c1
    @11
    cmul
    @68
    @15
    cc
    wcel
    @61
    @88
    c1
    wceq
    @68
    @15
    @78
    recnd
    #
    ax-1cn
    @15
    c1
    pncan3
    sylancl
    #
    oveq1d
    @68
    @15
    @20
    @11
    @89
    @68
    @20
    @84
    recnd
    #
    @44
    @63
    @17
    @65
    adantr
    #
    adddird
    @68
    @11
    @92
    mulid2d
    3eqtr3d
    @68
    @32
    @21
    @19
    @68
    @20
    @11
    @84
    @80
    remulcld
    @86
    @81
    @68
    @11
    @13
    @20
    @80
    @85
    @84
    @68
    cc0
    @20
    cle
    wbr
    #
    @15
    c1
    cle
    wbr
    #
    @68
    @83
    cc0
    @15
    cle
    wbr
    #
    @94
    @68
    @17
    @83
    @95
    @94
    w3a
    @77
    cc0
    c1
    @15
    0re
    1re
    elicc2i
    sylib
    #
    simp3d
    @68
    @82
    @83
    @93
    @94
    wb
    1re
    @78
    c1
    @15
    subge0
    sylancr
    mpbird
    @12
    @14
    @42
    @3
    @17
    simplr3
    #
    lemul2ad
    leadd2dd
    eqbrtrrd
    @68
    @22
    @31
    @21
    caddc
    co
    #
    @13
    cle
    @68
    @19
    @31
    @21
    @81
    @68
    @15
    @13
    @78
    @85
    remulcld
    @86
    @68
    @11
    @13
    @15
    @80
    @85
    @78
    @68
    @83
    @95
    @94
    @96
    simp2d
    @97
    lemul2ad
    leadd1dd
    @68
    @88
    @13
    cmul
    co
    c1
    @13
    cmul
    co
    @98
    @13
    @68
    @88
    c1
    @13
    cmul
    @90
    oveq1d
    @68
    @15
    @20
    @13
    @89
    @91
    @44
    @57
    @17
    @60
    adantr
    #
    adddird
    @68
    @13
    @99
    mulid2d
    3eqtr3d
    breqtrd
    @68
    @11
    cr
    wcel
    @13
    cr
    wcel
    @73
    @74
    @75
    @76
    w3a
    wb
    @80
    @85
    @11
    @13
    @22
    elicc2
    syl2anc
    mpbir3and
    sseldd
    ralrimiva
    #
    adantr
    @23
    @67
    vt
    @47
    @16
    @15
    @47
    wceq
    #
    @22
    @55
    cA
    @101
    @19
    @48
    @21
    @54
    caddc
    @15
    @47
    @11
    cmul
    oveq1
    @101
    @20
    @53
    @13
    cmul
    @15
    @47
    c1
    cmin
    oveq2
    oveq1d
    oveq12d
    eleq1d
    rspcv
    sylc
    eqeltrd
    ralrimiva
    @50
    @34
    vs
    vt
    @16
    vs
    vt
    weq
    #
    @49
    @33
    cA
    @102
    @46
    @31
    @48
    @32
    caddc
    @45
    @15
    @13
    cmul
    oveq1
    @102
    @47
    @20
    @11
    cmul
    @45
    @15
    c1
    cmin
    oveq2
    oveq1d
    oveq12d
    eleq1d
    cbvralv
    sylib
    @100
    wloglei
    r19.21bi
    anasss
    sylan2b
    @8
    @5
    eqid
    cvxsconn
    eqeltrrd
    ex
    impbid2
end
