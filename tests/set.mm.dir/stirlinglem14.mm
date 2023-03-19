include "cv.mm"
include "cli.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "stirlinglem13.mm"
include "wcel.mm"
include "wa.mm"
include "ce.mm"
include "cfv.mm"
include "simpl.mm"
include "rpefcld.mm"
include "ccom.mm"
include "cc.mm"
include "c1.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "ccncf.mm"
include "co.mm"
include "efcn.mm"
include "a1i.mm"
include "wf.mm"
include "clog.mm"
include "cfa.mm"
include "c2.mm"
include "cmul.mm"
include "csqrt.mm"
include "ceu.mm"
include "cdiv.mm"
include "cexp.mm"
include "wceq.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "nncn.mm"
include "3syl.mm"
include "2cnd.mm"
include "mulcld.mm"
include "sqrtcld.mm"
include "epr.mm"
include "rpcn.mm"
include "ax-mp.mm"
include "cc0.mm"
include "wne.mm"
include "0re.mm"
include "epos.mm"
include "gtneii.mm"
include "divcld.mm"
include "expcld.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpmulcld.mm"
include "sqrtgt0d.mm"
include "gt0ne0d.mm"
include "nnne0.mm"
include "divne0d.mm"
include "nnz.mm"
include "expne0d.mm"
include "mulne0d.mm"
include "fvmpt2.mm"
include "mpdan.mm"
include "eqeltrd.mm"
include "eqnetrd.mm"
include "logcld.mm"
include "fmpti.mm"
include "simpr.mm"
include "recnd.mm"
include "climcncf.mm"
include "wb.mm"
include "wtru.mm"
include "cvv.mm"
include "elexi.mm"
include "cmpt.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "coex.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt2.mm"
include "id.mm"
include "crab.mm"
include "rabid2.mm"
include "stirlinglem2.mm"
include "relogcl.mm"
include "elex.mm"
include "mprgbir.mm"
include "dmmpt.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "fvco.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "fvmptd.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "fveq2.mm"
include "fvmptf.mm"
include "eflog.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "adantl.mm"
include "climeq.mm"
include "trud.mm"
include "sylib.mm"
include "breq2.mm"
include "rspcev.mm"
include "rexlimiva.mm"

theorem stirlinglem14
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  assume stirlinglem14.1: |- A = ( n e. NN |-> ( ( ! ` n ) / ( ( sqrt ` ( 2 x. n ) ) x. ( ( n / _e ) ^ n ) ) ) )
  assume stirlinglem14.2: |- B = ( n e. NN |-> ( log ` ( A ` n ) ) )

  disjoint A c
  disjoint c d
  disjoint d k
  disjoint k n
  disjoint A d
  disjoint A k
  disjoint B d
  disjoint B k
  disjoint k x
  assert |- E. c e. RR+ A ~~> c

  proof
    cB
    vd
    cv
    #
    cli
    wbr
    #
    vd
    cr
    wrex
    cA
    vc
    cv
    #
    cli
    wbr
    #
    vc
    crp
    wrex
    #
    cA
    cB
    vn
    vd
    stirlinglem14.1
    stirlinglem14.2
    stirlinglem13
    @1
    @4
    vd
    cr
    @0
    cr
    wcel
    #
    @1
    wa
    #
    @0
    ce
    cfv
    #
    crp
    wcel
    cA
    @7
    cli
    wbr
    #
    @4
    @6
    @0
    @5
    @1
    simpl
    #
    rpefcld
    @6
    ce
    cB
    ccom
    #
    @7
    cli
    wbr
    #
    @8
    @6
    cc
    cc
    @0
    ce
    cB
    c1
    cn
    nnuz
    @6
    1zzd
    ce
    cc
    cc
    ccncf
    co
    #
    wcel
    @6
    efcn
    a1i
    cn
    cc
    cB
    wf
    @6
    vn
    cn
    cc
    vn
    cv
    #
    cA
    cfv
    #
    clog
    cfv
    #
    cB
    stirlinglem14.2
    @13
    cn
    wcel
    #
    @14
    @16
    @14
    @13
    cfa
    cfv
    #
    c2
    @13
    cmul
    co
    #
    csqrt
    cfv
    #
    @13
    ceu
    cdiv
    co
    #
    @13
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cc
    @16
    @23
    cc
    wcel
    @14
    @23
    wceq
    @16
    @17
    @22
    @16
    @13
    cn0
    wcel
    #
    @17
    cn
    wcel
    #
    @17
    cc
    wcel
    @13
    nnnn0
    #
    @13
    faccl
    #
    @17
    nncn
    3syl
    #
    @16
    @19
    @21
    @16
    @18
    @16
    c2
    @13
    @16
    2cnd
    @13
    nncn
    #
    mulcld
    sqrtcld
    #
    @16
    @20
    @13
    @16
    @13
    ceu
    @29
    ceu
    cc
    wcel
    #
    @16
    ceu
    crp
    wcel
    @31
    epr
    ceu
    rpcn
    ax-mp
    #
    a1i
    #
    ceu
    cc0
    wne
    #
    @16
    cc0
    ceu
    0re
    epos
    gtneii
    #
    a1i
    #
    divcld
    #
    @26
    expcld
    #
    mulcld
    #
    @16
    @19
    @21
    @30
    @38
    @16
    @19
    @16
    @18
    @16
    c2
    @13
    c2
    crp
    wcel
    #
    @16
    2rp
    a1i
    @13
    nnrp
    rpmulcld
    sqrtgt0d
    gt0ne0d
    @16
    @20
    @13
    @37
    @16
    @13
    ceu
    @29
    @33
    @13
    nnne0
    @36
    divne0d
    @13
    nnz
    expne0d
    mulne0d
    #
    divcld
    #
    vn
    cn
    @23
    cc
    cA
    stirlinglem14.1
    fvmpt2
    mpdan
    #
    @42
    eqeltrd
    @16
    @14
    @23
    cc0
    @43
    @16
    @17
    @22
    @28
    @39
    @16
    @24
    @25
    @17
    cc0
    wne
    @26
    @27
    @17
    nnne0
    3syl
    @41
    divne0d
    eqnetrd
    logcld
    fmpti
    a1i
    @5
    @1
    simpr
    @6
    @0
    @9
    recnd
    climcncf
    @11
    @8
    wb
    wtru
    @7
    vk
    @10
    cA
    c1
    cvv
    cvv
    cn
    nnuz
    @10
    cvv
    wcel
    wtru
    ce
    cB
    ce
    @12
    efcn
    elexi
    cB
    vn
    cn
    @15
    cmpt
    cvv
    stirlinglem14.2
    vn
    cn
    @15
    nnex
    mptex
    eqeltri
    coex
    a1i
    cA
    cvv
    wcel
    wtru
    cA
    vn
    cn
    @23
    cmpt
    #
    cvv
    stirlinglem14.1
    vn
    cn
    @23
    nnex
    mptex
    eqeltri
    a1i
    wtru
    1zzd
    vk
    cv
    #
    cn
    wcel
    #
    @45
    @10
    cfv
    #
    @45
    cA
    cfv
    #
    wceq
    wtru
    @46
    @47
    @45
    cB
    cfv
    #
    ce
    cfv
    #
    @48
    clog
    cfv
    #
    ce
    cfv
    #
    @48
    @46
    cB
    wfun
    @45
    cB
    cdm
    #
    wcel
    @47
    @50
    wceq
    vn
    cn
    @15
    cB
    stirlinglem14.2
    funmpt2
    @46
    @45
    cn
    @53
    @46
    id
    #
    cn
    @15
    cvv
    wcel
    #
    vn
    cn
    crab
    #
    @53
    cn
    @56
    wceq
    @55
    vn
    cn
    @55
    vn
    cn
    rabid2
    @16
    @14
    crp
    wcel
    @15
    cr
    wcel
    @55
    cA
    vn
    @13
    stirlinglem14.1
    stirlinglem2
    @14
    relogcl
    @15
    cr
    elex
    3syl
    mprgbir
    vn
    cn
    @15
    cB
    stirlinglem14.2
    dmmpt
    eqtr4i
    syl6eleq
    @45
    ce
    cB
    fvco
    sylancr
    @46
    @49
    @51
    ce
    @46
    @51
    cc
    wcel
    @49
    @51
    wceq
    @46
    @48
    @46
    @48
    @45
    cfa
    cfv
    #
    c2
    @45
    cmul
    co
    #
    csqrt
    cfv
    #
    @45
    ceu
    cdiv
    co
    #
    @45
    cexp
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cc
    @46
    vn
    @45
    @23
    @63
    cn
    cA
    cc
    cA
    @44
    wceq
    @46
    stirlinglem14.1
    a1i
    @46
    @13
    @45
    wceq
    #
    wa
    #
    @17
    @57
    @22
    @62
    cdiv
    @65
    @13
    @45
    cfa
    @46
    @64
    simpr
    #
    fveq2d
    @65
    @19
    @59
    @21
    @61
    cmul
    @65
    @18
    @58
    csqrt
    @65
    @13
    @45
    c2
    cmul
    @66
    oveq2d
    fveq2d
    @65
    @20
    @60
    @13
    @45
    cexp
    @65
    @13
    @45
    ceu
    cdiv
    @66
    oveq1d
    @66
    oveq12d
    oveq12d
    oveq12d
    @54
    @46
    @57
    @62
    @46
    @45
    cn0
    wcel
    #
    @57
    cn
    wcel
    #
    @57
    cc
    wcel
    @45
    nnnn0
    #
    @45
    faccl
    #
    @57
    nncn
    3syl
    #
    @46
    @59
    @61
    @46
    @58
    @46
    c2
    @45
    @46
    2cnd
    @45
    nncn
    #
    mulcld
    sqrtcld
    #
    @46
    @60
    @45
    @46
    @45
    ceu
    @72
    @31
    @46
    @32
    a1i
    #
    @34
    @46
    @35
    a1i
    #
    divcld
    #
    @69
    expcld
    #
    mulcld
    #
    @46
    @59
    @61
    @73
    @77
    @46
    @59
    @46
    @58
    @46
    c2
    @45
    @40
    @46
    2rp
    a1i
    @45
    nnrp
    rpmulcld
    sqrtgt0d
    gt0ne0d
    @46
    @60
    @45
    @76
    @46
    @45
    ceu
    @72
    @74
    @45
    nnne0
    @75
    divne0d
    @45
    nnz
    expne0d
    mulne0d
    #
    divcld
    #
    fvmptd
    #
    @80
    eqeltrd
    #
    @46
    @48
    @63
    cc0
    @81
    @46
    @57
    @62
    @71
    @78
    @46
    @67
    @68
    @57
    cc0
    wne
    @69
    @70
    @57
    nnne0
    3syl
    @79
    divne0d
    eqnetrd
    #
    logcld
    vn
    @45
    @15
    @51
    cn
    cB
    cc
    vn
    @45
    nfcv
    #
    vn
    @48
    clog
    vn
    clog
    nfcv
    vn
    @45
    cA
    vn
    cA
    @44
    stirlinglem14.1
    vn
    cn
    @23
    nfmpt1
    nfcxfr
    @84
    nffv
    nffv
    @64
    @14
    @48
    clog
    @13
    @45
    cA
    fveq2
    fveq2d
    stirlinglem14.2
    fvmptf
    mpdan
    fveq2d
    @46
    @48
    cc
    wcel
    @48
    cc0
    wne
    @52
    @48
    wceq
    @82
    @83
    @48
    eflog
    syl2anc
    3eqtrd
    adantl
    climeq
    trud
    sylib
    @3
    @8
    vc
    @7
    crp
    @2
    @7
    cA
    cli
    breq2
    rspcev
    syl2anc
    rexlimiva
    ax-mp
end
