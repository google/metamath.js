include "wcel.mm"
include "cpconn.mm"
include "wf.mm"
include "wa.mm"
include "cpt.mm"
include "cfv.mm"
include "ctop.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "wss.mm"
include "pconntop.mm"
include "ssriv.mm"
include "fss.mm"
include "mpan2.mm"
include "pttop.mm"
include "sylan2.mm"
include "cid.mm"
include "wfn.mm"
include "wex.mm"
include "fvi.mm"
include "ad2antrr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "cixp.mm"
include "simprl.mm"
include "eqid.mm"
include "ptuni.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "vex.mm"
include "elixp.mm"
include "sylib.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "simprr.mm"
include "pconncn.mm"
include "syl3anc.mm"
include "df-rex.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "fvex.mm"
include "eleq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ac6s2.mm"
include "syl.mm"
include "cicc.mm"
include "cmpt.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "simplll.mm"
include "biimpar.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simpld.mm"
include "iiuni.mm"
include "cnf.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "ptcn.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "0elunit.mm"
include "mptexg.mm"
include "mpteq2dv.mm"
include "fvmptg.mm"
include "sylancr.mm"
include "dffn5.mm"
include "3eqtr4d.mm"
include "1elunit.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exlimddv.mm"
include "ralrimivva.mm"
include "ispconn.mm"
include "sylanbrc.mm"

theorem ptpconn
  let cA: class A
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cS: class S
  let vi: setvar i


  assert |- ( ( A e. V /\ F : A --> PConn ) -> ( Xt_ ` F ) e. PConn )

  proof
    cA
    cV
    wcel
    #
    cA
    cpconn
    cF
    wf
    #
    wa
    #
    cF
    cpt
    cfv
    #
    ctop
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    vx
    cv
    #
    wceq
    #
    c1
    @5
    cfv
    #
    vy
    cv
    #
    wceq
    #
    wa
    #
    vf
    cii
    @3
    ccn
    co
    #
    wrex
    #
    vy
    @3
    cuni
    #
    wral
    vx
    @15
    wral
    @3
    cpconn
    wcel
    @1
    @0
    cA
    ctop
    cF
    wf
    #
    @4
    @1
    cpconn
    ctop
    wss
    @16
    vx
    cpconn
    ctop
    @7
    pconntop
    ssriv
    cA
    cpconn
    ctop
    cF
    fss
    mpan2
    #
    cA
    cF
    cV
    pttop
    sylan2
    @2
    @14
    vx
    vy
    @15
    @15
    @2
    @7
    @15
    wcel
    #
    @10
    @15
    wcel
    #
    wa
    #
    wa
    #
    vg
    cv
    #
    cA
    cid
    cfv
    #
    wfn
    #
    vt
    cv
    #
    @22
    cfv
    #
    cii
    @25
    cF
    cfv
    #
    ccn
    co
    #
    wcel
    #
    cc0
    @26
    cfv
    #
    @25
    @7
    cfv
    #
    wceq
    #
    c1
    @26
    cfv
    #
    @25
    @10
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    vt
    @23
    wral
    #
    wa
    #
    @14
    vg
    @21
    @5
    @28
    wcel
    #
    @6
    @31
    wceq
    #
    @9
    @34
    wceq
    #
    wa
    #
    wa
    #
    vf
    wex
    #
    vt
    @23
    wral
    @39
    vg
    wex
    @21
    @45
    vt
    @23
    @21
    @25
    @23
    wcel
    #
    @25
    cA
    wcel
    #
    @45
    @21
    @46
    @47
    @21
    @23
    cA
    @25
    @0
    @23
    cA
    wceq
    #
    @1
    @20
    cA
    cV
    fvi
    ad2antrr
    #
    eleq2d
    biimpa
    @21
    @47
    wa
    #
    @43
    vf
    @28
    wrex
    #
    @45
    @50
    @27
    cpconn
    wcel
    @31
    @27
    cuni
    #
    wcel
    #
    @34
    @52
    wcel
    #
    @51
    @21
    cA
    cpconn
    @25
    cF
    @0
    @1
    @20
    simplr
    #
    ffvelrnda
    @21
    @53
    vt
    cA
    @21
    @7
    cA
    wfn
    #
    @53
    vt
    cA
    wral
    #
    @21
    @7
    vt
    cA
    @52
    cixp
    #
    wcel
    @56
    @57
    wa
    @21
    @7
    @15
    @58
    @2
    @18
    @19
    simprl
    @2
    @58
    @15
    wceq
    #
    @20
    @1
    @0
    @16
    @59
    @17
    vt
    cA
    cF
    @3
    cV
    @3
    eqid
    #
    ptuni
    sylan2
    adantr
    #
    eleqtrrd
    vt
    cA
    @52
    @7
    vx
    vex
    elixp
    sylib
    #
    simprd
    r19.21bi
    @21
    @54
    vt
    cA
    @21
    @10
    cA
    wfn
    #
    @54
    vt
    cA
    wral
    #
    @21
    @10
    @58
    wcel
    @63
    @64
    wa
    @21
    @10
    @15
    @58
    @2
    @18
    @19
    simprr
    @61
    eleqtrrd
    vt
    cA
    @52
    @10
    vy
    vex
    elixp
    sylib
    #
    simprd
    r19.21bi
    @31
    @34
    vf
    @27
    @52
    @52
    eqid
    pconncn
    syl3anc
    @43
    vf
    @28
    df-rex
    sylib
    syldan
    ralrimiva
    @44
    @37
    vt
    vf
    @23
    vg
    cA
    cid
    fvex
    @5
    @26
    wceq
    #
    @40
    @29
    @43
    @36
    @5
    @26
    @28
    eleq1
    @66
    @41
    @32
    @42
    @35
    @66
    @6
    @30
    @31
    cc0
    @5
    @26
    fveq1
    eqeq1d
    @66
    @9
    @33
    @34
    c1
    @5
    @26
    fveq1
    eqeq1d
    anbi12d
    anbi12d
    ac6s2
    syl
    @21
    @39
    wa
    #
    vz
    cc0
    c1
    cicc
    co
    #
    vi
    cA
    vz
    cv
    #
    vi
    cv
    #
    @22
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    @13
    wcel
    cc0
    @74
    cfv
    #
    @7
    wceq
    #
    c1
    @74
    cfv
    #
    @10
    wceq
    #
    @14
    @67
    vz
    @72
    vi
    cF
    cA
    cii
    @3
    cV
    @68
    @60
    cii
    @68
    ctopon
    cfv
    wcel
    @67
    iitopon
    a1i
    @0
    @1
    @20
    @39
    simplll
    #
    @67
    @1
    @16
    @21
    @1
    @39
    @55
    adantr
    @17
    syl
    @67
    @70
    cA
    wcel
    #
    wa
    #
    @71
    vz
    @68
    @72
    cmpt
    cii
    @70
    cF
    cfv
    #
    ccn
    co
    #
    @81
    vz
    @68
    @82
    cuni
    #
    @71
    @81
    @71
    @83
    wcel
    #
    @68
    @84
    @71
    wf
    @81
    @85
    cc0
    @71
    cfv
    #
    @70
    @7
    cfv
    #
    wceq
    #
    c1
    @71
    cfv
    #
    @70
    @10
    cfv
    #
    wceq
    #
    wa
    #
    @67
    @80
    @70
    @23
    wcel
    #
    @85
    @92
    wa
    #
    @67
    @93
    @80
    @67
    @23
    cA
    @70
    @21
    @48
    @39
    @49
    adantr
    eleq2d
    biimpar
    @67
    @38
    @93
    @94
    @21
    @24
    @38
    simprr
    @37
    @94
    vt
    @70
    @23
    @25
    @70
    wceq
    #
    @29
    @85
    @36
    @92
    @95
    @26
    @71
    @28
    @83
    @25
    @70
    @22
    fveq2
    #
    @95
    @27
    @82
    cii
    ccn
    @25
    @70
    cF
    fveq2
    oveq2d
    eleq12d
    @95
    @32
    @88
    @35
    @91
    @95
    @30
    @86
    @31
    @87
    @95
    cc0
    @26
    @71
    @96
    fveq1d
    @25
    @70
    @7
    fveq2
    eqeq12d
    @95
    @33
    @89
    @34
    @90
    @95
    c1
    @26
    @71
    @96
    fveq1d
    @25
    @70
    @10
    fveq2
    eqeq12d
    anbi12d
    anbi12d
    rspccva
    sylan
    syldan
    #
    simpld
    #
    @71
    cii
    @82
    @68
    @84
    iiuni
    @84
    eqid
    cnf
    syl
    feqmptd
    @98
    eqeltrrd
    ptcn
    @67
    vi
    cA
    @86
    cmpt
    #
    vi
    cA
    @87
    cmpt
    #
    @75
    @7
    @67
    vi
    cA
    @86
    @87
    @81
    @88
    @91
    @81
    @85
    @92
    @97
    simprd
    #
    simpld
    mpteq2dva
    @67
    cc0
    @68
    wcel
    @99
    cvv
    wcel
    #
    @75
    @99
    wceq
    0elunit
    @67
    @0
    @102
    @79
    vi
    cA
    @86
    cV
    mptexg
    syl
    vz
    cc0
    @73
    @99
    @68
    cvv
    @74
    @69
    cc0
    wceq
    vi
    cA
    @72
    @86
    @69
    cc0
    @71
    fveq2
    mpteq2dv
    @74
    eqid
    #
    fvmptg
    sylancr
    @67
    @56
    @7
    @100
    wceq
    @21
    @56
    @39
    @21
    @56
    @57
    @62
    simpld
    adantr
    vi
    cA
    @7
    dffn5
    sylib
    3eqtr4d
    @67
    vi
    cA
    @89
    cmpt
    #
    vi
    cA
    @90
    cmpt
    #
    @77
    @10
    @67
    vi
    cA
    @89
    @90
    @81
    @88
    @91
    @101
    simprd
    mpteq2dva
    @67
    c1
    @68
    wcel
    @104
    cvv
    wcel
    #
    @77
    @104
    wceq
    1elunit
    @67
    @0
    @106
    @79
    vi
    cA
    @89
    cV
    mptexg
    syl
    vz
    c1
    @73
    @104
    @68
    cvv
    @74
    @69
    c1
    wceq
    vi
    cA
    @72
    @89
    @69
    c1
    @71
    fveq2
    mpteq2dv
    @103
    fvmptg
    sylancr
    @67
    @63
    @10
    @105
    wceq
    @21
    @63
    @39
    @21
    @63
    @64
    @65
    simpld
    adantr
    vi
    cA
    @10
    dffn5
    sylib
    3eqtr4d
    @12
    @76
    @78
    wa
    vf
    @74
    @13
    @5
    @74
    wceq
    #
    @8
    @76
    @11
    @78
    @107
    @6
    @75
    @7
    cc0
    @5
    @74
    fveq1
    eqeq1d
    @107
    @9
    @77
    @10
    c1
    @5
    @74
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    exlimddv
    ralrimivva
    vx
    vy
    vf
    @3
    @15
    @15
    eqid
    ispconn
    sylanbrc
end
