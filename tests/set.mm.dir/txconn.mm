include "cconn.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "cuni.mm"
include "cpr.mm"
include "wss.mm"
include "conntop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wex.mm"
include "neq0.mm"
include "inss1.mm"
include "simplr.mm"
include "sseldi.mm"
include "elssuni.mm"
include "syl.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cxp.mm"
include "simprr.mm"
include "simplll.mm"
include "simpllr.mm"
include "eqid.mm"
include "txuni.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "1st2nd2.mm"
include "crab.mm"
include "xp2nd.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "mptpreima.mm"
include "ccn.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "xp1st.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1t.mm"
include "cnima.mm"
include "syl5eqelr.mm"
include "wrex.mm"
include "wne.mm"
include "simprl.mm"
include "elunii.mm"
include "eqeltrrd.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "rabn0.mm"
include "sylibr.mm"
include "inss2.mm"
include "cnclima.mm"
include "connclo.mm"
include "elrab.mm"
include "simprbi.mm"
include "opeq2.mm"
include "eqeltrd.mm"
include "expr.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "orrd.mm"
include "vex.mm"
include "elpr.mm"
include "syl6ibr.mm"
include "isconn2.mm"
include "sylanbrc.mm"

theorem txconn
  let cR: class R
  let cS: class S
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z


  assert |- ( ( R e. Conn /\ S e. Conn ) -> ( R tX S ) e. Conn )

  proof
    cR
    cconn
    wcel
    #
    cS
    cconn
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ctop
    wcel
    #
    @3
    @3
    ccld
    cfv
    #
    cin
    #
    c0
    @3
    cuni
    #
    cpr
    #
    wss
    @3
    cconn
    wcel
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @4
    @1
    cR
    conntop
    #
    cS
    conntop
    #
    cR
    cS
    txtop
    syl2an
    @2
    vx
    @6
    @8
    @2
    vx
    cv
    #
    @6
    wcel
    #
    @13
    c0
    wceq
    #
    @13
    @7
    wceq
    #
    wo
    #
    @13
    @8
    wcel
    @2
    @14
    @17
    @2
    @14
    wa
    #
    @15
    @16
    @15
    wn
    vz
    cv
    #
    @13
    wcel
    #
    vz
    wex
    @18
    @16
    vz
    @13
    neq0
    @18
    @20
    @16
    vz
    @18
    @20
    @16
    @18
    @20
    wa
    #
    @13
    @7
    @21
    @13
    @3
    wcel
    #
    @13
    @7
    wss
    @21
    @6
    @3
    @13
    @3
    @5
    inss1
    #
    @2
    @14
    @20
    simplr
    sseldi
    @13
    @3
    elssuni
    syl
    @21
    vw
    @7
    @13
    @18
    @20
    vw
    cv
    #
    @7
    wcel
    #
    @24
    @13
    wcel
    @18
    @20
    @25
    wa
    #
    wa
    #
    @24
    @24
    c1st
    cfv
    #
    @24
    c2nd
    cfv
    #
    cop
    #
    @13
    @27
    @24
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    wcel
    #
    @24
    @30
    wceq
    @27
    @24
    @7
    @33
    @18
    @20
    @25
    simprr
    @27
    @9
    @10
    @33
    @7
    wceq
    @27
    @0
    @9
    @0
    @1
    @14
    @26
    simplll
    #
    @11
    syl
    #
    @27
    @1
    @10
    @0
    @1
    @14
    @26
    simpllr
    #
    @12
    syl
    #
    cR
    cS
    @31
    @32
    @31
    eqid
    #
    @32
    eqid
    #
    txuni
    syl2anc
    #
    eleqtrrd
    #
    @24
    @31
    @32
    1st2nd2
    syl
    @27
    @29
    @28
    va
    cv
    #
    cop
    #
    @13
    wcel
    #
    va
    @32
    crab
    #
    wcel
    #
    @30
    @13
    wcel
    #
    @27
    @29
    @32
    @46
    @27
    @34
    @29
    @32
    wcel
    #
    @42
    @24
    @31
    @32
    xp2nd
    syl
    @27
    @46
    cS
    @32
    @40
    @37
    @27
    @46
    va
    @32
    @44
    cmpt
    #
    ccnv
    @13
    cima
    #
    cS
    va
    @32
    @44
    @13
    @50
    @50
    eqid
    mptpreima
    #
    @27
    @50
    cS
    @3
    ccn
    co
    wcel
    #
    @22
    @51
    cS
    wcel
    @27
    va
    @28
    @43
    cS
    cR
    cS
    @32
    @27
    @10
    cS
    @32
    ctopon
    cfv
    wcel
    @38
    cS
    @32
    @40
    toptopon
    sylib
    #
    @27
    va
    @28
    cS
    cR
    @32
    @31
    @54
    @27
    @9
    cR
    @31
    ctopon
    cfv
    wcel
    @36
    cR
    @31
    @39
    toptopon
    sylib
    #
    @27
    @34
    @28
    @31
    wcel
    #
    @42
    @24
    @31
    @32
    xp1st
    syl
    #
    cnmptc
    @27
    va
    cS
    @32
    @54
    cnmptid
    cnmpt1t
    #
    @27
    @6
    @3
    @13
    @23
    @2
    @14
    @26
    simplr
    #
    sseldi
    #
    @13
    @50
    cS
    @3
    cnima
    syl2anc
    syl5eqelr
    @27
    @45
    va
    @32
    wrex
    #
    @46
    c0
    wne
    @27
    @19
    c2nd
    cfv
    #
    @32
    wcel
    #
    @28
    @62
    cop
    #
    @13
    wcel
    #
    @61
    @27
    @19
    @33
    wcel
    #
    @63
    @27
    @19
    @7
    @33
    @27
    @20
    @22
    @19
    @7
    wcel
    @18
    @20
    @25
    simprl
    #
    @60
    @19
    @13
    @3
    elunii
    syl2anc
    @41
    eleqtrrd
    #
    @19
    @31
    @32
    xp2nd
    syl
    #
    @27
    @28
    @43
    @62
    cop
    #
    @13
    wcel
    #
    va
    @31
    crab
    #
    wcel
    #
    @65
    @27
    @28
    @31
    @72
    @57
    @27
    @72
    cR
    @31
    @39
    @35
    @27
    @72
    va
    @31
    @70
    cmpt
    #
    ccnv
    @13
    cima
    #
    cR
    va
    @31
    @70
    @13
    @74
    @74
    eqid
    mptpreima
    #
    @27
    @74
    cR
    @3
    ccn
    co
    wcel
    #
    @22
    @75
    cR
    wcel
    @27
    va
    @43
    @62
    cR
    cR
    cS
    @31
    @55
    @27
    va
    cR
    @31
    @55
    cnmptid
    @27
    va
    @62
    cR
    cS
    @31
    @32
    @55
    @54
    @69
    cnmptc
    cnmpt1t
    #
    @60
    @13
    @74
    cR
    @3
    cnima
    syl2anc
    syl5eqelr
    @27
    @71
    va
    @31
    wrex
    #
    @72
    c0
    wne
    @27
    @19
    c1st
    cfv
    #
    @31
    wcel
    #
    @80
    @62
    cop
    #
    @13
    wcel
    #
    @79
    @27
    @66
    @81
    @68
    @19
    @31
    @32
    xp1st
    syl
    @27
    @19
    @82
    @13
    @27
    @66
    @19
    @82
    wceq
    @68
    @19
    @31
    @32
    1st2nd2
    syl
    @67
    eqeltrrd
    @71
    @83
    va
    @80
    @31
    @43
    @80
    wceq
    @70
    @82
    @13
    @43
    @80
    @62
    opeq1
    eleq1d
    rspcev
    syl2anc
    @71
    va
    @31
    rabn0
    sylibr
    @27
    @72
    @75
    cR
    ccld
    cfv
    #
    @76
    @27
    @77
    @13
    @5
    wcel
    #
    @75
    @84
    wcel
    @78
    @27
    @6
    @5
    @13
    @3
    @5
    inss2
    @59
    sseldi
    #
    @13
    @74
    cR
    @3
    cnclima
    syl2anc
    syl5eqelr
    connclo
    eleqtrrd
    @73
    @56
    @65
    @71
    @65
    va
    @28
    @31
    @43
    @28
    wceq
    @70
    @64
    @13
    @43
    @28
    @62
    opeq1
    eleq1d
    elrab
    simprbi
    syl
    @45
    @65
    va
    @62
    @32
    @43
    @62
    wceq
    @44
    @64
    @13
    @43
    @62
    @28
    opeq2
    eleq1d
    rspcev
    syl2anc
    @45
    va
    @32
    rabn0
    sylibr
    @27
    @46
    @51
    cS
    ccld
    cfv
    #
    @52
    @27
    @53
    @85
    @51
    @87
    wcel
    @58
    @86
    @13
    @50
    cS
    @3
    cnclima
    syl2anc
    syl5eqelr
    connclo
    eleqtrrd
    @47
    @49
    @48
    @45
    @48
    va
    @29
    @32
    @43
    @29
    wceq
    @44
    @30
    @13
    @43
    @29
    @28
    opeq2
    eleq1d
    elrab
    simprbi
    syl
    eqeltrd
    expr
    ssrdv
    eqssd
    ex
    exlimdv
    syl5bi
    orrd
    ex
    @13
    c0
    @7
    vx
    vex
    elpr
    syl6ibr
    ssrdv
    @3
    @7
    @7
    eqid
    isconn2
    sylanbrc
end
