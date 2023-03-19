include "cfinsum.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "wf1o.mm"
include "chash.mm"
include "cplusg.mm"
include "cn.mm"
include "cmpt.mm"
include "cseq.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cn0.mm"
include "wrex.mm"
include "cio.mm"
include "df-ov.mm"
include "c2nd.mm"
include "cdm.mm"
include "c1st.mm"
include "ccmn.mm"
include "wcel.mm"
include "cbs.mm"
include "wf.mm"
include "cfn.mm"
include "copab.mm"
include "cvv.mm"
include "df-bj-finsum.mm"
include "a1i.mm"
include "wb.mm"
include "wi.mm"
include "simpr.mm"
include "fveq2d.mm"
include "adantr.mm"
include "fex.mm"
include "syl2anc.mm"
include "op1stg.mm"
include "eqtrd.mm"
include "op2ndg.mm"
include "dmeqd.mm"
include "fdm.mm"
include "syl.mm"
include "f1oeq3.mm"
include "biimpd.mm"
include "ad2antll.mm"
include "adantrd.mm"
include "eqidd.mm"
include "simprl.mm"
include "adantrr.mm"
include "simprrl.mm"
include "fveq1d.mm"
include "mpteq2dva.mm"
include "seqeq123d.mm"
include "simprr.mm"
include "jca.mm"
include "hashfz1.mm"
include "eqcomd.mm"
include "ad2antrl.mm"
include "fzfid.mm"
include "19.8a.mm"
include "hasheqf1oi.mm"
include "sylc.mm"
include "3eqtrd.mm"
include "sylan2.mm"
include "fveq12d.mm"
include "eqeq2d.mm"
include "impancom.mm"
include "com12.mm"
include "jcad.mm"
include "biimprd.mm"
include "wtru.mm"
include "simpl.mm"
include "tru.mm"
include "jctir.mm"
include "adantlrr.mm"
include "impcom.mm"
include "syl12anc.mm"
include "impbid.mm"
include "ex.mm"
include "imp.mm"
include "exbidv.mm"
include "rexbidva.mm"
include "iotabidv.mm"
include "eleq1.mm"
include "feq2.mm"
include "anbi12d.mm"
include "ceqsexgv.mm"
include "mpbir2and.mm"
include "exsimpr.mm"
include "df-rex.mm"
include "sylibr.mm"
include "fveq2.mm"
include "feq3d.mm"
include "rexbidv.mm"
include "feq1.mm"
include "anbi2d.mm"
include "opelopabg.mm"
include "iotaex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem bj-finsumval0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cI: class I
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bj-finsumval0.1: |- ( ph -> A e. CMnd )
  assume bj-finsumval0.2: |- ( ph -> I e. Fin )
  assume bj-finsumval0.3: |- ( ph -> B : I --> ( Base ` A ) )

  disjoint A s
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint f s
  disjoint m s
  disjoint n s
  disjoint f m
  disjoint f n
  disjoint m n
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B s
  disjoint I f
  disjoint I n
  disjoint f ph
  disjoint m ph
  disjoint ph s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint f t
  disjoint m t
  disjoint n t
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint m x
  disjoint n x
  disjoint y z
  disjoint f y
  disjoint m y
  disjoint n y
  disjoint f z
  disjoint m z
  disjoint n z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B t
  disjoint I t
  disjoint I x
  disjoint ph x
  assert |- ( ph -> ( A FinSum B ) = ( iota s E. m e. NN0 E. f ( f : ( 1 ... m ) -1-1-onto-> I /\ s = ( seq 1 ( ( +g ` A ) , ( n e. NN |-> ( B ` ( f ` n ) ) ) ) ` ( # ` I ) ) ) ) )

  proof
    wph
    cA
    cB
    cfinsum
    co
    cA
    cB
    cop
    #
    cfinsum
    cfv
    c1
    vm
    cv
    #
    cfz
    co
    #
    cI
    vf
    cv
    #
    wf1o
    #
    vs
    cv
    #
    cI
    chash
    cfv
    #
    cA
    cplusg
    cfv
    #
    vn
    cn
    vn
    cv
    #
    @3
    cfv
    #
    cB
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn0
    wrex
    #
    vs
    cio
    #
    cA
    cB
    cfinsum
    df-ov
    wph
    vx
    @0
    @2
    vx
    cv
    #
    c2nd
    cfv
    #
    cdm
    #
    @3
    wf1o
    #
    @5
    @1
    @19
    c1st
    cfv
    #
    cplusg
    cfv
    #
    vn
    cn
    @9
    @20
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn0
    wrex
    #
    vs
    cio
    #
    @18
    vy
    cv
    #
    ccmn
    wcel
    #
    vt
    cv
    #
    @34
    cbs
    cfv
    #
    vz
    cv
    #
    wf
    #
    vt
    cfn
    wrex
    #
    wa
    #
    vy
    vz
    copab
    #
    cfinsum
    cvv
    cfinsum
    vx
    @42
    @33
    cmpt
    wceq
    wph
    vx
    vy
    vz
    vt
    vf
    vm
    vn
    vs
    df-bj-finsum
    a1i
    wph
    @19
    @0
    wceq
    #
    wa
    #
    @32
    @17
    vs
    @44
    @31
    @16
    vm
    cn0
    @44
    @1
    cn0
    wcel
    #
    wa
    @30
    @15
    vf
    @44
    @45
    @30
    @15
    wb
    #
    @44
    @23
    cA
    wceq
    #
    @20
    cB
    wceq
    #
    @21
    cI
    wceq
    #
    @45
    @46
    wi
    @44
    @23
    @0
    c1st
    cfv
    #
    cA
    @44
    @19
    @0
    c1st
    wph
    @43
    simpr
    #
    fveq2d
    @44
    cA
    ccmn
    wcel
    #
    cB
    cvv
    wcel
    #
    @50
    cA
    wceq
    wph
    @52
    @43
    bj-finsumval0.1
    adantr
    #
    wph
    @53
    @43
    wph
    cI
    cA
    cbs
    cfv
    #
    cB
    wf
    #
    cI
    cfn
    wcel
    #
    @53
    bj-finsumval0.3
    bj-finsumval0.2
    cI
    @55
    cfn
    cB
    fex
    syl2anc
    #
    adantr
    #
    cA
    cB
    ccmn
    cvv
    op1stg
    syl2anc
    eqtrd
    @44
    @20
    @0
    c2nd
    cfv
    #
    cB
    @44
    @19
    @0
    c2nd
    @51
    fveq2d
    @44
    @52
    @53
    @60
    cB
    wceq
    @54
    @59
    cA
    cB
    ccmn
    cvv
    op2ndg
    syl2anc
    eqtrd
    #
    @44
    @21
    cB
    cdm
    #
    cI
    @44
    @20
    cB
    @61
    dmeqd
    wph
    @62
    cI
    wceq
    #
    @43
    wph
    @56
    @63
    bj-finsumval0.3
    cI
    @55
    cB
    fdm
    syl
    adantr
    eqtrd
    @47
    @48
    @49
    wa
    #
    wa
    #
    @45
    @46
    @65
    @45
    wa
    #
    @30
    @15
    @66
    @30
    @4
    @14
    @65
    @30
    @4
    wi
    @45
    @65
    @22
    @4
    @29
    @49
    @22
    @4
    wi
    @47
    @48
    @49
    @22
    @4
    @21
    cI
    @2
    @3
    f1oeq3
    #
    biimpd
    ad2antll
    adantrd
    adantr
    @30
    @66
    @14
    @22
    @66
    @29
    @14
    @22
    @66
    wa
    #
    @29
    @14
    @68
    @28
    @13
    @5
    @68
    @1
    @6
    @27
    @12
    @68
    @24
    @7
    @26
    @11
    c1
    c1
    @68
    c1
    eqidd
    @22
    @65
    @24
    @7
    wceq
    @45
    @22
    @65
    wa
    #
    @23
    cA
    cplusg
    @22
    @47
    @64
    simprl
    fveq2d
    adantrr
    @22
    @65
    @26
    @11
    wceq
    @45
    @69
    vn
    cn
    @25
    @10
    @69
    @8
    cn
    wcel
    #
    wa
    @9
    @20
    cB
    @69
    @48
    @70
    @22
    @47
    @48
    @49
    simprrl
    adantr
    fveq1d
    mpteq2dva
    adantrr
    seqeq123d
    @66
    @22
    @45
    @49
    wa
    #
    @1
    @6
    wceq
    #
    @66
    @45
    @49
    @65
    @45
    simpr
    @65
    @49
    @45
    @47
    @48
    @49
    simprr
    #
    adantr
    jca
    @22
    @71
    wa
    #
    @1
    @2
    chash
    cfv
    #
    @21
    chash
    cfv
    #
    @6
    @45
    @1
    @75
    wceq
    @22
    @49
    @45
    @75
    @1
    @1
    hashfz1
    eqcomd
    ad2antrl
    @74
    @2
    cfn
    wcel
    @22
    vf
    wex
    #
    @75
    @76
    wceq
    @74
    c1
    @1
    fzfid
    @22
    @77
    @71
    @22
    vf
    19.8a
    adantr
    @2
    @21
    vf
    cfn
    hasheqf1oi
    sylc
    @74
    @21
    cI
    chash
    @22
    @45
    @49
    simprr
    fveq2d
    3eqtrd
    #
    sylan2
    fveq12d
    eqeq2d
    biimpd
    impancom
    com12
    jcad
    @66
    @15
    @22
    @29
    @66
    @4
    @22
    @14
    @65
    @4
    @22
    wi
    #
    @45
    @49
    @79
    @47
    @48
    @49
    @22
    @4
    @67
    biimprd
    ad2antll
    adantr
    #
    adantrd
    @15
    @66
    @29
    @4
    @66
    @14
    @29
    @4
    @66
    wa
    #
    @14
    @29
    @81
    @13
    @28
    @5
    @81
    @6
    @1
    @12
    @27
    @81
    @7
    @24
    @11
    @26
    c1
    c1
    @81
    c1
    eqidd
    @81
    cA
    @23
    cplusg
    @81
    @47
    wtru
    wa
    #
    cA
    @23
    wceq
    @65
    @82
    @4
    @45
    @65
    @47
    wtru
    @47
    @64
    simpl
    tru
    jctir
    ad2antrl
    @82
    @23
    cA
    @47
    wtru
    simpl
    eqcomd
    syl
    fveq2d
    @81
    vn
    cn
    @10
    @25
    @4
    @65
    @70
    @10
    @25
    wceq
    @45
    @4
    @65
    wa
    #
    @70
    wa
    @9
    cB
    @20
    @83
    cB
    @20
    wceq
    #
    @70
    @64
    @84
    @4
    @47
    @64
    @20
    cB
    @48
    @49
    simpl
    eqcomd
    ad2antll
    adantr
    fveq1d
    adantlrr
    mpteq2dva
    seqeq123d
    @81
    @1
    @6
    @81
    @22
    @45
    @49
    @72
    @66
    @4
    @22
    @80
    impcom
    @4
    @65
    @45
    simprr
    @65
    @49
    @4
    @45
    @73
    ad2antrl
    @78
    syl12anc
    eqcomd
    fveq12d
    eqeq2d
    biimpd
    impancom
    com12
    jcad
    impbid
    ex
    syl12anc
    imp
    exbidv
    rexbidva
    iotabidv
    wph
    @0
    @42
    wcel
    #
    @52
    @36
    @55
    cB
    wf
    #
    vt
    cfn
    wrex
    #
    bj-finsumval0.1
    wph
    @36
    cfn
    wcel
    #
    @86
    wa
    #
    vt
    wex
    #
    @87
    wph
    @36
    cI
    wceq
    #
    @89
    wa
    vt
    wex
    #
    @90
    wph
    @92
    @57
    @56
    bj-finsumval0.2
    bj-finsumval0.3
    wph
    @57
    @92
    @57
    @56
    wa
    #
    wb
    bj-finsumval0.2
    @89
    @93
    vt
    cI
    cfn
    @91
    @88
    @57
    @86
    @56
    @36
    cI
    cfn
    eleq1
    @36
    cI
    @55
    cB
    feq2
    anbi12d
    ceqsexgv
    syl
    mpbir2and
    @91
    @89
    vt
    exsimpr
    syl
    @86
    vt
    cfn
    df-rex
    sylibr
    wph
    @52
    @53
    @85
    @52
    @87
    wa
    #
    wb
    bj-finsumval0.1
    @58
    @41
    @52
    @36
    @55
    @38
    wf
    #
    vt
    cfn
    wrex
    #
    wa
    @94
    vy
    vz
    cA
    cB
    ccmn
    cvv
    @34
    cA
    wceq
    #
    @35
    @52
    @40
    @96
    @34
    cA
    ccmn
    eleq1
    @97
    @39
    @95
    vt
    cfn
    @97
    @37
    @55
    @38
    @36
    @34
    cA
    cbs
    fveq2
    feq3d
    rexbidv
    anbi12d
    @38
    cB
    wceq
    #
    @96
    @87
    @52
    @98
    @95
    @86
    vt
    cfn
    @36
    @55
    @38
    cB
    feq1
    rexbidv
    anbi2d
    opelopabg
    syl2anc
    mpbir2and
    @18
    cvv
    wcel
    wph
    @17
    vs
    iotaex
    a1i
    fvmptd
    syl5eq
end
