include "cr.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "citg1.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "itg10.mm"
include "cvv.mm"
include "wcel.mm"
include "reex.mm"
include "a1i.mm"
include "wf.mm"
include "cdm.mm"
include "i1ff.mm"
include "syl.mm"
include "adantr.mm"
include "0red.mm"
include "cv.mm"
include "simplr.mm"
include "oveq1d.mm"
include "mul02lem2.mm"
include "adantl.mm"
include "eqtrd.mm"
include "caofid2.mm"
include "fveq2d.mm"
include "simpr.mm"
include "itg1cl.mm"
include "recnd.mm"
include "mul02d.mm"
include "3eqtr4a.mm"
include "wne.mm"
include "crn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "csu.mm"
include "cdiv.mm"
include "wss.mm"
include "i1fmulc.mm"
include "frn.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "cc.mm"
include "divcan2d.mm"
include "i1fmulclem.mm"
include "syldan.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "redivcld.mm"
include "eldifsni.mm"
include "divne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "i1fima2sn.mm"
include "syl2anc.mm"
include "mulassd.mm"
include "eqtr3d.mm"
include "sumeq2dv.mm"
include "cfn.mm"
include "i1frn.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "mulcld.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "itg1val.mm"
include "cmpt.mm"
include "id.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eqid.mm"
include "eldifi.mm"
include "wral.mm"
include "wfn.mm"
include "ffn.mm"
include "eqidd.mm"
include "ofc1.mm"
include "adantlr.mm"
include "ffvelrnda.mm"
include "divcan3d.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "ralrn.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "eqeltrrd.mm"
include "oveq2.mm"
include "mulne0d.mm"
include "simpl.mm"
include "ssel2.mm"
include "syl2an.mm"
include "adantrl.mm"
include "divmuld.mm"
include "bicomd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1o2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "remulcld.mm"
include "fsumf1o.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "pm2.61dane.mm"

theorem itg1mulc
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume i1fmulc.2: |- ( ph -> F e. dom S.1 )
  assume i1fmulc.3: |- ( ph -> A e. RR )


  assert |- ( ph -> ( S.1 ` ( ( RR X. { A } ) oF x. F ) ) = ( A x. ( S.1 ` F ) ) )

  proof
    wph
    cr
    cA
    csn
    cxp
    cF
    cmul
    cof
    co
    #
    citg1
    cfv
    #
    cA
    cF
    citg1
    cfv
    #
    cmul
    co
    #
    wceq
    cA
    cc0
    wph
    cA
    cc0
    wceq
    #
    wa
    #
    cr
    cc0
    csn
    #
    cxp
    #
    citg1
    cfv
    cc0
    @1
    @3
    itg10
    @5
    @0
    @7
    citg1
    @5
    vx
    cr
    cA
    cc0
    cmul
    cr
    cF
    cvv
    cr
    cr
    cr
    cvv
    wcel
    #
    @5
    reex
    a1i
    wph
    cr
    cr
    cF
    wf
    #
    @4
    wph
    cF
    citg1
    cdm
    #
    wcel
    #
    @9
    i1fmulc.2
    cF
    i1ff
    syl
    #
    adantr
    wph
    cA
    cr
    wcel
    #
    @4
    i1fmulc.3
    adantr
    @5
    0red
    @5
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    cA
    @14
    cmul
    co
    cc0
    @14
    cmul
    co
    #
    cc0
    @16
    cA
    cc0
    @14
    cmul
    wph
    @4
    @15
    simplr
    oveq1d
    @15
    @17
    cc0
    wceq
    @5
    @14
    mul02lem2
    adantl
    eqtrd
    caofid2
    fveq2d
    @5
    @3
    cc0
    @2
    cmul
    co
    #
    cc0
    @5
    cA
    cc0
    @2
    cmul
    wph
    @4
    simpr
    oveq1d
    wph
    @18
    cc0
    wceq
    @4
    wph
    @2
    wph
    @2
    wph
    @11
    @2
    cr
    wcel
    i1fmulc.2
    cF
    itg1cl
    syl
    recnd
    mul02d
    adantr
    eqtrd
    3eqtr4a
    wph
    cA
    cc0
    wne
    #
    wa
    #
    @0
    crn
    #
    @6
    cdif
    #
    vm
    cv
    #
    @0
    ccnv
    @23
    csn
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    cA
    @22
    @23
    cA
    cdiv
    co
    #
    cF
    ccnv
    #
    @28
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    cmul
    co
    #
    @1
    @3
    @20
    @27
    @22
    cA
    @33
    cmul
    co
    #
    vm
    csu
    @35
    @20
    @22
    @26
    @36
    vm
    @20
    @23
    @22
    wcel
    #
    wa
    #
    cA
    @28
    cmul
    co
    #
    @32
    cmul
    co
    @26
    @36
    @38
    @39
    @23
    @32
    @25
    cmul
    @38
    @23
    cA
    @38
    @23
    @20
    @22
    cr
    @23
    @20
    @21
    cr
    @6
    @20
    cr
    cr
    @0
    wf
    #
    @21
    cr
    wss
    @20
    @0
    @10
    wcel
    #
    @40
    wph
    @41
    @19
    wph
    cA
    cF
    i1fmulc.2
    i1fmulc.3
    i1fmulc
    adantr
    #
    @0
    i1ff
    syl
    #
    cr
    cr
    @0
    frn
    syl
    ssdifssd
    #
    sselda
    #
    recnd
    #
    @20
    cA
    cc
    wcel
    #
    @37
    @20
    cA
    wph
    @13
    @19
    i1fmulc.3
    adantr
    recnd
    #
    adantr
    #
    wph
    @19
    @37
    simplr
    #
    divcan2d
    @38
    @25
    @32
    @38
    @24
    @31
    cvol
    @20
    @37
    @23
    cr
    wcel
    @24
    @31
    wceq
    @45
    wph
    cA
    @23
    cF
    i1fmulc.2
    i1fmulc.3
    i1fmulclem
    syldan
    fveq2d
    eqcomd
    oveq12d
    @38
    cA
    @28
    @32
    @49
    @38
    @28
    @38
    @23
    cA
    @45
    wph
    @13
    @19
    @37
    i1fmulc.3
    ad2antrr
    #
    @50
    redivcld
    #
    recnd
    #
    @38
    @32
    @38
    @11
    @28
    cr
    @6
    cdif
    wcel
    #
    @32
    cr
    wcel
    wph
    @11
    @19
    @37
    i1fmulc.2
    ad2antrr
    @38
    @28
    cr
    wcel
    @28
    cc0
    wne
    @54
    @52
    @38
    @23
    cA
    @46
    @38
    cA
    @51
    recnd
    @37
    @23
    cc0
    wne
    @20
    @23
    @21
    cc0
    eldifsni
    adantl
    @50
    divne0d
    @28
    cr
    cc0
    eldifsn
    sylanbrc
    @28
    cr
    cF
    i1fima2sn
    syl2anc
    recnd
    #
    mulassd
    eqtr3d
    sumeq2dv
    @20
    @22
    @33
    cA
    vm
    @20
    @21
    cfn
    wcel
    #
    @22
    @21
    wss
    @22
    cfn
    wcel
    @20
    @41
    @56
    @42
    @0
    i1frn
    syl
    @21
    @6
    difss
    @21
    @22
    ssfi
    sylancl
    #
    @48
    @38
    @28
    @32
    @53
    @55
    mulcld
    fsummulc2
    eqtr4d
    @20
    @41
    @1
    @27
    wceq
    @42
    vm
    @0
    itg1val
    syl
    @20
    @2
    @34
    cA
    cmul
    @20
    @2
    cF
    crn
    #
    @6
    cdif
    #
    vk
    cv
    #
    @29
    @60
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    @34
    @20
    @11
    @2
    @65
    wceq
    wph
    @11
    @19
    i1fmulc.2
    adantr
    #
    vk
    cF
    itg1val
    syl
    @20
    @59
    @64
    @22
    @33
    vk
    vm
    vn
    @22
    vn
    cv
    #
    cA
    cdiv
    co
    #
    cmpt
    #
    @28
    @60
    @28
    wceq
    #
    @60
    @28
    @63
    @32
    cmul
    @70
    id
    @70
    @62
    @31
    cvol
    @70
    @61
    @30
    @29
    @60
    @28
    sneq
    imaeq2d
    fveq2d
    oveq12d
    @57
    @20
    vn
    vk
    @22
    @59
    @68
    cA
    @60
    cmul
    co
    #
    @69
    @69
    eqid
    #
    @20
    @67
    @22
    wcel
    #
    wa
    #
    @68
    @58
    wcel
    #
    @68
    cc0
    wne
    @68
    @59
    wcel
    @73
    @20
    @67
    @21
    wcel
    @75
    @67
    @21
    @6
    eldifi
    @20
    @75
    vn
    @21
    @20
    @75
    vn
    @21
    wral
    #
    vy
    cv
    #
    @0
    cfv
    #
    cA
    cdiv
    co
    #
    @58
    wcel
    #
    vy
    cr
    wral
    #
    @20
    @80
    vy
    cr
    @20
    @77
    cr
    wcel
    #
    wa
    #
    @79
    @77
    cF
    cfv
    #
    @58
    @83
    @79
    cA
    @84
    cmul
    co
    #
    cA
    cdiv
    co
    @84
    @83
    @78
    @85
    cA
    cdiv
    wph
    @82
    @78
    @85
    wceq
    @19
    wph
    cr
    cA
    @84
    cmul
    cF
    cvv
    cr
    @77
    @8
    wph
    reex
    a1i
    i1fmulc.3
    wph
    @9
    cF
    cr
    wfn
    #
    @12
    cr
    cr
    cF
    ffn
    #
    syl
    wph
    @82
    wa
    @84
    eqidd
    ofc1
    adantlr
    #
    oveq1d
    @83
    @84
    cA
    @83
    @84
    @20
    cr
    cr
    @77
    cF
    wph
    @9
    @19
    @12
    adantr
    #
    ffvelrnda
    recnd
    @20
    @47
    @82
    @48
    adantr
    wph
    @19
    @82
    simplr
    divcan3d
    eqtrd
    @20
    @86
    @82
    @84
    @58
    wcel
    @20
    @9
    @86
    @89
    @87
    syl
    #
    cr
    @77
    cF
    fnfvelrn
    sylan
    eqeltrd
    ralrimiva
    @20
    @0
    cr
    wfn
    #
    @76
    @81
    wb
    @20
    @40
    @91
    @43
    cr
    cr
    @0
    ffn
    syl
    #
    @75
    @80
    vn
    vy
    cr
    @0
    @67
    @78
    wceq
    @68
    @79
    @58
    @67
    @78
    cA
    cdiv
    oveq1
    eleq1d
    ralrn
    syl
    mpbird
    r19.21bi
    sylan2
    @74
    @67
    cA
    @74
    @67
    @20
    @22
    cr
    @67
    @44
    sselda
    recnd
    @20
    @47
    @73
    @48
    adantr
    @73
    @67
    cc0
    wne
    @20
    @67
    @21
    cc0
    eldifsni
    adantl
    wph
    @19
    @73
    simplr
    divne0d
    @68
    @58
    cc0
    eldifsn
    sylanbrc
    @20
    @60
    @59
    wcel
    #
    wa
    #
    @71
    @21
    wcel
    #
    @71
    cc0
    wne
    @71
    @22
    wcel
    @93
    @20
    @60
    @58
    wcel
    @95
    @60
    @58
    @6
    eldifi
    @20
    @95
    vk
    @58
    @20
    @95
    vk
    @58
    wral
    #
    @85
    @21
    wcel
    #
    vy
    cr
    wral
    #
    @20
    @97
    vy
    cr
    @83
    @78
    @85
    @21
    @88
    @20
    @91
    @82
    @78
    @21
    wcel
    @92
    cr
    @77
    @0
    fnfvelrn
    sylan
    eqeltrrd
    ralrimiva
    @20
    @86
    @96
    @98
    wb
    @90
    @95
    @97
    vk
    vy
    cr
    cF
    @60
    @84
    wceq
    @71
    @85
    @21
    @60
    @84
    cA
    cmul
    oveq2
    eleq1d
    ralrn
    syl
    mpbird
    r19.21bi
    sylan2
    @94
    cA
    @60
    @20
    @47
    @93
    @48
    adantr
    @94
    @60
    @20
    @59
    cr
    @60
    @20
    @58
    cr
    @6
    @20
    @9
    @58
    cr
    wss
    @89
    cr
    cr
    cF
    frn
    syl
    ssdifssd
    sselda
    #
    recnd
    wph
    @19
    @93
    simplr
    @93
    @60
    cc0
    wne
    @20
    @60
    @58
    cc0
    eldifsni
    adantl
    mulne0d
    @71
    @21
    cc0
    eldifsn
    sylanbrc
    @20
    @73
    @93
    wa
    #
    wa
    #
    @71
    @67
    wceq
    #
    @68
    @60
    wceq
    #
    @67
    @71
    wceq
    @60
    @68
    wceq
    @101
    @103
    @102
    @101
    @67
    cA
    @60
    @101
    @67
    @20
    @22
    cr
    wss
    @73
    @67
    cr
    wcel
    @100
    @44
    @73
    @93
    simpl
    @22
    cr
    @67
    ssel2
    syl2an
    recnd
    @101
    cA
    wph
    @13
    @19
    @100
    i1fmulc.3
    ad2antrr
    recnd
    @101
    @60
    @20
    @93
    @60
    cr
    wcel
    @73
    @99
    adantrl
    recnd
    wph
    @19
    @100
    simplr
    divmuld
    bicomd
    @67
    @71
    eqcom
    @60
    @68
    eqcom
    3bitr4g
    f1o2d
    @37
    @23
    @69
    cfv
    @28
    wceq
    @20
    vn
    @23
    @68
    @28
    @22
    @69
    @67
    @23
    cA
    cdiv
    oveq1
    @72
    @23
    cA
    cdiv
    ovex
    fvmpt
    adantl
    @94
    @64
    @94
    @60
    @63
    @99
    @20
    @11
    @93
    @63
    cr
    wcel
    @66
    @60
    @58
    cF
    i1fima2sn
    sylan
    remulcld
    recnd
    fsumf1o
    eqtrd
    oveq2d
    3eqtr4d
    pm2.61dane
end
