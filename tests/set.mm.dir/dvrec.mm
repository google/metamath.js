include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "c2.mm"
include "cexp.mm"
include "cneg.mm"
include "wf.mm"
include "wfn.mm"
include "cdm.mm"
include "dvfcn.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "divcl.mm"
include "3expb.mm"
include "sylan2b.mm"
include "eqid.mm"
include "fmptd.mm"
include "difssd.mm"
include "dvbss.mm"
include "wbr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cnt.mm"
include "cmin.mm"
include "climc.mm"
include "simpr.mm"
include "ctop.mm"
include "wceq.mm"
include "cnfldtop.mm"
include "ccld.mm"
include "cha.mm"
include "cnfldhaus.mm"
include "0cn.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "sncld.mm"
include "mp2an.mm"
include "cldopn.mm"
include "ax-mp.mm"
include "isopn3i.mm"
include "syl6eleqr.mm"
include "cmul.mm"
include "eldifi.mm"
include "adantl.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "simpl.mm"
include "eldifsni.mm"
include "divdiv1d.mm"
include "eqtr4d.mm"
include "negeqd.mm"
include "divcld.mm"
include "divnegd.mm"
include "eqtrd.mm"
include "ccncf.mm"
include "negcld.mm"
include "cdivcncf.mm"
include "syl.mm"
include "oveq2.mm"
include "cnmptlimc.mm"
include "eqeltrd.mm"
include "cres.mm"
include "cncff.mm"
include "limcdif.mm"
include "eldifad.mm"
include "ad2antlr.mm"
include "subcld.mm"
include "adantr.mm"
include "mulneg12.mm"
include "syl2anc.mm"
include "subdird.mm"
include "negsubdi2d.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "simpll.mm"
include "divcan2d.mm"
include "divassd.mm"
include "3eqtr2d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"
include "subne0d.mm"
include "divcan3d.mm"
include "mpteq2dva.mm"
include "difss.mm"
include "resmpt.mm"
include "syl6eqr.mm"
include "eleqtrd.mm"
include "crest.mm"
include "restid.mm"
include "eqcomi.mm"
include "eldv.mm"
include "mpbir2and.mm"
include "vex.mm"
include "negex.mm"
include "breldm.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "mpbii.mm"
include "ffn.mm"
include "cvv.mm"
include "wral.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "wfun.mm"
include "ffun.mm"
include "funbrfv.mm"
include "sylc.mm"
include "oveq1.mm"
include "eqfnfvd.mm"

theorem dvrec
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. CC -> ( CC _D ( x e. ( CC \ { 0 } ) |-> ( A / x ) ) ) = ( x e. ( CC \ { 0 } ) |-> -u ( A / ( x ^ 2 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    vy
    cc
    cc0
    csn
    #
    cdif
    #
    cc
    vx
    @2
    cA
    vx
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    #
    vx
    @2
    cA
    @3
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cmpt
    #
    @0
    @2
    cc
    @6
    wf
    #
    @6
    @2
    wfn
    @0
    @6
    cdm
    #
    cc
    @6
    wf
    #
    @11
    @5
    dvfcn
    #
    @0
    @12
    @2
    cc
    @6
    @0
    @12
    @2
    @0
    @2
    cc
    @5
    cc
    cc
    wss
    #
    @0
    cc
    ssid
    #
    a1i
    @0
    vx
    @2
    @4
    cc
    @5
    @3
    @2
    wcel
    @0
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    wa
    @4
    cc
    wcel
    #
    @3
    cc
    cc0
    eldifsn
    @0
    @17
    @18
    @19
    cA
    @3
    divcl
    3expb
    sylan2b
    @5
    eqid
    #
    fmptd
    #
    @0
    cc
    @1
    difssd
    dvbss
    @0
    vy
    @2
    @12
    @0
    vy
    cv
    #
    @2
    wcel
    #
    @22
    @12
    wcel
    #
    @0
    @23
    wa
    #
    @22
    cA
    @22
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    @6
    wbr
    #
    @24
    @25
    @29
    @22
    @2
    ccnfld
    ctopn
    cfv
    #
    cnt
    cfv
    cfv
    #
    wcel
    @28
    vz
    @2
    @22
    csn
    #
    cdif
    #
    vz
    cv
    #
    @5
    cfv
    #
    @22
    @5
    cfv
    #
    cmin
    co
    #
    @34
    @22
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @22
    climc
    co
    #
    wcel
    @25
    @22
    @2
    @31
    @0
    @23
    simpr
    #
    @30
    ctop
    wcel
    #
    @2
    @30
    wcel
    #
    @31
    @2
    wceq
    @30
    @30
    eqid
    #
    cnfldtop
    #
    @1
    @30
    ccld
    cfv
    wcel
    #
    @44
    @30
    cha
    wcel
    cc0
    cc
    wcel
    @47
    @30
    @45
    cnfldhaus
    0cn
    cc0
    @30
    cc
    cc
    @30
    @30
    @45
    cnfldtopon
    toponunii
    #
    sncld
    mp2an
    @1
    @30
    cc
    @48
    cldopn
    ax-mp
    @2
    @30
    isopn3i
    mp2an
    syl6eleqr
    @25
    @28
    vz
    @2
    cA
    @22
    cdiv
    co
    #
    cneg
    #
    @34
    cdiv
    co
    #
    cmpt
    #
    @22
    climc
    co
    #
    @41
    @25
    @28
    @50
    @22
    cdiv
    co
    #
    @53
    @25
    @28
    @49
    @22
    cdiv
    co
    #
    cneg
    @54
    @25
    @27
    @55
    @25
    @27
    cA
    @22
    @22
    cmul
    co
    #
    cdiv
    co
    @55
    @25
    @26
    @56
    cA
    cdiv
    @25
    @22
    @23
    @22
    cc
    wcel
    #
    @0
    @22
    cc
    @1
    eldifi
    #
    adantl
    #
    sqvald
    oveq2d
    @25
    cA
    @22
    @22
    @0
    @23
    simpl
    #
    @59
    @59
    @23
    @22
    cc0
    wne
    #
    @0
    @22
    cc
    cc0
    eldifsni
    #
    adantl
    #
    @63
    divdiv1d
    eqtr4d
    negeqd
    @25
    @49
    @22
    @25
    cA
    @22
    @60
    @59
    @63
    divcld
    #
    @59
    @63
    divnegd
    eqtrd
    @25
    vz
    @2
    @22
    cc
    @51
    @54
    @25
    @50
    cc
    wcel
    @52
    @2
    cc
    ccncf
    co
    wcel
    #
    @25
    @49
    @64
    negcld
    vz
    @50
    @52
    @52
    eqid
    cdivcncf
    syl
    #
    @42
    @34
    @22
    @50
    cdiv
    oveq2
    cnmptlimc
    eqeltrd
    @25
    @53
    @52
    @33
    cres
    #
    @22
    climc
    co
    @41
    @25
    @2
    @22
    @52
    @25
    @65
    @2
    cc
    @52
    wf
    @66
    @2
    cc
    @52
    cncff
    syl
    limcdif
    @25
    @40
    @67
    @22
    climc
    @25
    @40
    vz
    @33
    @51
    cmpt
    #
    @67
    @25
    vz
    @33
    @39
    @51
    @25
    @34
    @33
    wcel
    #
    wa
    #
    @39
    @38
    @51
    cmul
    co
    #
    @38
    cdiv
    co
    @51
    @70
    @37
    @71
    @38
    cdiv
    @70
    @38
    cneg
    #
    @49
    @34
    cdiv
    co
    #
    cmul
    co
    #
    @38
    @73
    cneg
    #
    cmul
    co
    #
    @37
    @71
    @70
    @38
    cc
    wcel
    @73
    cc
    wcel
    @74
    @76
    wceq
    @70
    @34
    @22
    @70
    @34
    cc
    @1
    @69
    @34
    @2
    wcel
    #
    @25
    @34
    @2
    @32
    eldifi
    adantl
    #
    eldifad
    #
    @23
    @57
    @0
    @69
    @58
    ad2antlr
    #
    subcld
    #
    @70
    @49
    @34
    @25
    @49
    cc
    wcel
    @69
    @64
    adantr
    #
    @79
    @70
    @77
    @34
    cc0
    wne
    @78
    @34
    cc
    cc0
    eldifsni
    syl
    #
    divcld
    #
    @38
    @73
    mulneg12
    syl2anc
    @70
    @22
    @34
    cmin
    co
    #
    @73
    cmul
    co
    @22
    @73
    cmul
    co
    #
    @34
    @73
    cmul
    co
    #
    cmin
    co
    @74
    @37
    @70
    @22
    @34
    @73
    @80
    @79
    @84
    subdird
    @70
    @72
    @85
    @73
    cmul
    @70
    @34
    @22
    @79
    @80
    negsubdi2d
    oveq1d
    @70
    @35
    @86
    @36
    @87
    cmin
    @70
    @35
    cA
    @34
    cdiv
    co
    #
    @22
    @49
    cmul
    co
    #
    @34
    cdiv
    co
    @86
    @70
    @77
    @35
    @88
    wceq
    @78
    vx
    @34
    @4
    @88
    @2
    @5
    @3
    @34
    cA
    cdiv
    oveq2
    @20
    cA
    @34
    cdiv
    ovex
    fvmpt
    syl
    @70
    @89
    cA
    @34
    cdiv
    @70
    cA
    @22
    @0
    @23
    @69
    simpll
    @80
    @23
    @61
    @0
    @69
    @62
    ad2antlr
    divcan2d
    oveq1d
    @70
    @22
    @49
    @34
    @80
    @82
    @79
    @83
    divassd
    3eqtr2d
    @70
    @36
    @49
    @87
    @23
    @36
    @49
    wceq
    @0
    @69
    vx
    @22
    @4
    @49
    @2
    @5
    @3
    @22
    cA
    cdiv
    oveq2
    @20
    cA
    @22
    cdiv
    ovex
    fvmpt
    ad2antlr
    @70
    @49
    @34
    @82
    @79
    @83
    divcan2d
    eqtr4d
    oveq12d
    3eqtr4d
    @70
    @75
    @51
    @38
    cmul
    @70
    @49
    @34
    @82
    @79
    @83
    divnegd
    oveq2d
    3eqtr3d
    oveq1d
    @70
    @51
    @38
    @70
    @50
    @34
    @70
    @49
    @82
    negcld
    @79
    @83
    divcld
    @81
    @70
    @34
    @22
    @79
    @80
    @69
    @34
    @22
    wne
    @25
    @34
    @2
    @22
    eldifsni
    adantl
    subne0d
    divcan3d
    eqtrd
    mpteq2dva
    @33
    @2
    wss
    @67
    @68
    wceq
    @2
    @32
    difss
    vz
    @2
    @33
    @51
    resmpt
    ax-mp
    syl6eqr
    oveq1d
    eqtr4d
    eleqtrd
    @25
    vz
    @2
    @22
    @28
    cc
    @30
    @5
    @40
    @30
    @30
    cc
    crest
    co
    #
    @30
    @43
    @90
    @30
    wceq
    @46
    @30
    ctop
    cc
    @48
    restid
    ax-mp
    eqcomi
    @45
    @40
    eqid
    @15
    @25
    @16
    a1i
    @0
    @2
    cc
    @5
    wf
    @23
    @21
    adantr
    @25
    cc
    @1
    difssd
    eldv
    mpbir2and
    #
    @22
    @28
    @6
    vy
    vex
    @27
    negex
    #
    breldm
    syl
    ex
    ssrdv
    eqssd
    feq2d
    mpbii
    @2
    cc
    @6
    ffn
    syl
    @9
    cvv
    wcel
    #
    vx
    @2
    wral
    @10
    @2
    wfn
    @0
    @93
    vx
    @2
    @8
    negex
    rgenw
    vx
    @2
    @9
    @10
    cvv
    @10
    eqid
    #
    fnmpt
    mp1i
    @25
    @22
    @6
    cfv
    #
    @28
    @22
    @10
    cfv
    #
    @25
    @6
    wfun
    #
    @29
    @95
    @28
    wceq
    @13
    @97
    @25
    @14
    @12
    cc
    @6
    ffun
    mp1i
    @91
    @22
    @28
    @6
    funbrfv
    sylc
    @23
    @96
    @28
    wceq
    @0
    vx
    @22
    @9
    @28
    @2
    @10
    @3
    @22
    wceq
    #
    @8
    @27
    @98
    @7
    @26
    cA
    cdiv
    @3
    @22
    c2
    cexp
    oveq1
    oveq2d
    negeqd
    @94
    @92
    fvmpt
    adantl
    eqtr4d
    eqfnfvd
end
