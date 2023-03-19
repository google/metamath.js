include "c2ndc.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cv.mm"
include "wrmo.mm"
include "wal.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "wi.mm"
include "is2ndc.mm"
include "wf1.mm"
include "wex.mm"
include "omex.mm"
include "brdom.mm"
include "cvv.mm"
include "ccnv.mm"
include "cpw.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wf.mm"
include "wmo.mm"
include "wss.mm"
include "ssrab2.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "adantl.mm"
include "syl5ss.mm"
include "adantr.mm"
include "wne.mm"
include "eldifsn.mm"
include "n0.mm"
include "wel.mm"
include "tg2.mm"
include "con0.mm"
include "omsson.mm"
include "syl6ss.mm"
include "ad2antrr.mm"
include "wfn.mm"
include "f1fn.mm"
include "ad3antlr.mm"
include "simprl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1ocnvfv1.mm"
include "simprrr.mm"
include "selpw.mm"
include "sylibr.mm"
include "simprrl.mm"
include "ne0i.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "rabn0.mm"
include "onint.mm"
include "rexlimdvaa.mm"
include "syl5.mm"
include "expdimp.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "impr.mm"
include "sseldd.mm"
include "expr.mm"
include "ralimdva.mm"
include "imp.mm"
include "adantrr.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "c1o.mm"
include "cif.mm"
include "neeq1.mm"
include "1n0.mm"
include "elimhyp.mm"
include "mpbi.mm"
include "19.29r.mm"
include "mpan.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "weq.mm"
include "elrab.mm"
include "simprbi.mm"
include "simprd.mm"
include "iftrued.mm"
include "simpld.mm"
include "elpwid.mm"
include "eqsstrd.mm"
include "sseld.mm"
include "exp31.mm"
include "com23.mm"
include "exp4a.mm"
include "com25.mm"
include "imp31.mm"
include "an32s.mm"
include "rmoim.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1.mm"
include "cop.mm"
include "copab.mm"
include "df-br.mm"
include "df-mpt.mm"
include "eleq2i.mm"
include "opabid.mm"
include "3bitri.mm"
include "syl6bb.mm"
include "cbvmo.mm"
include "df-rmo.mm"
include "bitr4i.mm"
include "alrimiv.mm"
include "dff12.mm"
include "f1domg.mm"
include "mpsyl.mm"
include "ex.mm"
include "difeq1.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "syl5ibcom.mm"
include "impd.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "3impib.mm"

theorem 2ndcdisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cJ: class J
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let vn: setvar n

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint J x
  disjoint b f
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b n
  disjoint B b
  disjoint f n
  disjoint B f
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint B w
  disjoint B z
  disjoint J b
  disjoint J f
  assert |- ( ( J e. 2ndc /\ A. x e. A B e. ( J \ { (/) } ) /\ A. y E* x e. A y e. B ) -> A ~<_ _om )

  proof
    cJ
    c2ndc
    wcel
    #
    cB
    cJ
    c0
    csn
    #
    cdif
    #
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    #
    cA
    com
    cdom
    wbr
    #
    @0
    vb
    cv
    #
    com
    cdom
    wbr
    #
    @10
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vb
    ctb
    wrex
    @4
    @8
    wa
    #
    @9
    wi
    #
    vb
    cJ
    is2ndc
    @14
    @16
    vb
    ctb
    @10
    ctb
    wcel
    #
    @11
    @13
    @16
    @11
    @10
    com
    vf
    cv
    #
    wf1
    #
    vf
    wex
    @17
    @13
    @16
    wi
    #
    @10
    com
    vf
    omex
    brdom
    @17
    @19
    @20
    vf
    @17
    @19
    @20
    @17
    @19
    wa
    #
    cB
    @12
    @1
    cdif
    #
    wcel
    #
    vx
    cA
    wral
    #
    @8
    wa
    #
    @9
    wi
    @13
    @16
    @21
    @25
    @9
    com
    cvv
    wcel
    @21
    @25
    wa
    #
    cA
    com
    vx
    cA
    vn
    cv
    #
    @18
    ccnv
    #
    cfv
    #
    cB
    cpw
    #
    @1
    cdif
    #
    wcel
    #
    vn
    @18
    crn
    #
    crab
    #
    cint
    #
    cmpt
    #
    wf1
    #
    @9
    omex
    @26
    cA
    com
    @36
    wf
    #
    vw
    cv
    #
    vz
    cv
    #
    @36
    wbr
    #
    vw
    wmo
    #
    vz
    wal
    @37
    @26
    @35
    com
    wcel
    #
    vx
    cA
    wral
    #
    @38
    @21
    @24
    @44
    @8
    @21
    @24
    @44
    @21
    @23
    @43
    vx
    cA
    @21
    vx
    cv
    #
    cA
    wcel
    #
    @23
    @43
    @21
    @46
    @23
    wa
    #
    wa
    #
    @34
    com
    @35
    @21
    @34
    com
    wss
    @47
    @21
    @34
    @33
    com
    @32
    vn
    @33
    ssrab2
    @19
    @33
    com
    wss
    #
    @17
    @19
    @10
    com
    @18
    wf
    @49
    @10
    com
    @18
    f1f
    @10
    com
    @18
    frn
    syl
    adantl
    syl5ss
    #
    adantr
    @21
    @46
    @23
    @35
    @34
    wcel
    #
    @23
    cB
    @12
    wcel
    #
    cB
    c0
    wne
    #
    wa
    @21
    @46
    wa
    #
    @51
    cB
    @12
    c0
    eldifsn
    @54
    @52
    @53
    @51
    @53
    @6
    vy
    wex
    @54
    @52
    wa
    #
    @51
    vy
    cB
    n0
    @55
    @6
    @51
    vy
    @54
    @52
    @6
    @51
    @52
    @6
    wa
    vy
    vz
    wel
    #
    @40
    cB
    wss
    #
    wa
    #
    vz
    @10
    wrex
    @54
    @51
    vz
    cB
    @10
    @5
    tg2
    @54
    @58
    @51
    vz
    @10
    @54
    vz
    vb
    wel
    #
    @58
    wa
    #
    wa
    #
    @34
    con0
    wss
    #
    @34
    c0
    wne
    #
    @51
    @21
    @62
    @46
    @60
    @21
    @34
    com
    con0
    @50
    omsson
    syl6ss
    ad2antrr
    @61
    @32
    vn
    @33
    wrex
    #
    @63
    @61
    @40
    @18
    cfv
    #
    @33
    wcel
    #
    @65
    @28
    cfv
    #
    @31
    wcel
    #
    @64
    @61
    @18
    @10
    wfn
    #
    @59
    @66
    @19
    @69
    @17
    @46
    @60
    @10
    com
    @18
    f1fn
    ad3antlr
    @54
    @59
    @58
    simprl
    #
    @10
    @40
    @18
    fnfvelrn
    syl2anc
    @61
    @67
    @40
    @31
    @61
    @10
    @33
    @18
    wf1o
    #
    @59
    @67
    @40
    wceq
    @19
    @71
    @17
    @46
    @60
    @10
    com
    @18
    f1f1orn
    ad3antlr
    @70
    @10
    @33
    @40
    @18
    f1ocnvfv1
    syl2anc
    @61
    @40
    @30
    wcel
    #
    @40
    c0
    wne
    #
    @40
    @31
    wcel
    @61
    @57
    @72
    @54
    @59
    @56
    @57
    simprrr
    vz
    cB
    selpw
    sylibr
    @61
    @56
    @73
    @54
    @59
    @56
    @57
    simprrl
    @40
    @5
    ne0i
    syl
    @40
    @30
    c0
    eldifsn
    sylanbrc
    eqeltrd
    @32
    @68
    vn
    @65
    @33
    @27
    @65
    wceq
    @29
    @67
    @31
    @27
    @65
    @28
    fveq2
    eleq1d
    rspcev
    syl2anc
    @32
    vn
    @33
    rabn0
    sylibr
    @34
    onint
    syl2anc
    rexlimdvaa
    syl5
    expdimp
    exlimdv
    syl5bi
    expimpd
    syl5bi
    impr
    #
    sseldd
    expr
    ralimdva
    imp
    adantrr
    vx
    cA
    com
    @35
    @36
    @36
    eqid
    fmpt
    sylib
    @26
    @42
    vz
    @26
    @40
    @35
    wceq
    #
    vx
    cA
    wrmo
    #
    @42
    @21
    @24
    @8
    @76
    @8
    @5
    @40
    @28
    cfv
    #
    c0
    wne
    #
    @77
    c1o
    cif
    #
    wcel
    #
    @7
    wa
    #
    vy
    wex
    #
    @21
    @24
    wa
    #
    @76
    @80
    vy
    wex
    #
    @8
    @82
    @79
    c0
    wne
    #
    @84
    @78
    @85
    c1o
    c0
    wne
    @77
    c1o
    @77
    @79
    c0
    neeq1
    c1o
    @79
    c0
    neeq1
    1n0
    elimhyp
    vy
    @79
    n0
    mpbi
    @80
    @7
    vy
    19.29r
    mpan
    @83
    @81
    @76
    vy
    @83
    @80
    @7
    @76
    @83
    @80
    wa
    @75
    @6
    wi
    #
    vx
    cA
    wral
    #
    @7
    @76
    wi
    @21
    @80
    @24
    @87
    @21
    @80
    wa
    #
    @24
    @87
    @88
    @23
    @86
    vx
    cA
    @21
    @80
    @46
    @23
    @86
    wi
    @21
    @75
    @46
    @23
    @80
    @6
    @21
    @75
    @46
    @23
    @80
    @6
    wi
    #
    @21
    @47
    @75
    @89
    @21
    @47
    @75
    @89
    @48
    @75
    wa
    #
    @79
    cB
    @5
    @90
    @79
    @77
    cB
    @90
    @78
    @77
    c1o
    @90
    @77
    @30
    wcel
    #
    @78
    @90
    @77
    @31
    wcel
    #
    @91
    @78
    wa
    @90
    @40
    @34
    wcel
    #
    @92
    @48
    @75
    @93
    @48
    @93
    @75
    @51
    @74
    @40
    @35
    @34
    eleq1
    syl5ibrcom
    imp
    @93
    @40
    @33
    wcel
    @92
    @32
    @92
    vn
    @40
    @33
    vn
    vz
    weq
    @29
    @77
    @31
    @27
    @40
    @28
    fveq2
    eleq1d
    elrab
    simprbi
    syl
    @77
    @30
    c0
    eldifsn
    sylib
    #
    simprd
    iftrued
    @90
    @77
    cB
    @90
    @91
    @78
    @94
    simpld
    elpwid
    eqsstrd
    sseld
    exp31
    com23
    exp4a
    com25
    imp31
    ralimdva
    imp
    an32s
    @75
    @6
    vx
    cA
    rmoim
    syl
    expimpd
    exlimdv
    syl5
    impr
    @42
    @46
    @75
    wa
    #
    vx
    wmo
    @76
    @41
    @95
    vw
    vx
    vx
    @39
    @40
    @36
    vx
    @39
    nfcv
    vx
    cA
    @35
    nfmpt1
    vx
    @40
    nfcv
    nfbr
    @95
    vw
    nfv
    vw
    vx
    weq
    @41
    @45
    @40
    @36
    wbr
    #
    @95
    @39
    @45
    @40
    @36
    breq1
    @96
    @45
    @40
    cop
    #
    @36
    wcel
    @97
    @95
    vx
    vz
    copab
    #
    wcel
    @95
    @45
    @40
    @36
    df-br
    @36
    @98
    @97
    vx
    vz
    cA
    @35
    df-mpt
    eleq2i
    @95
    vx
    vz
    opabid
    3bitri
    syl6bb
    cbvmo
    @75
    vx
    cA
    df-rmo
    bitr4i
    sylibr
    alrimiv
    vw
    vz
    cA
    com
    @36
    dff12
    sylanbrc
    cA
    com
    cvv
    @36
    f1domg
    mpsyl
    ex
    @13
    @25
    @15
    @9
    @13
    @24
    @4
    @8
    @13
    @23
    @3
    vx
    cA
    @13
    @22
    @2
    cB
    @12
    cJ
    @1
    difeq1
    eleq2d
    ralbidv
    anbi1d
    imbi1d
    syl5ibcom
    ex
    exlimdv
    syl5bi
    impd
    rexlimiv
    sylbi
    3impib
end
