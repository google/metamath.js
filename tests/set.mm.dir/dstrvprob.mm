include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cprb.mm"
include "cbrsiga.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cep.mm"
include "corvc.mm"
include "adantr.mm"
include "crrv.mm"
include "simpr.mm"
include "orvcelel.mm"
include "prob01.mm"
include "syl2anc.mm"
include "cxr.mm"
include "cle.mm"
include "elunitrn.mm"
include "rexrd.mm"
include "elunitge0.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "syl.mm"
include "fmpt3d.mm"
include "ccnv.mm"
include "cima.mm"
include "cr.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "csiga.mm"
include "brsigarn.mm"
include "elrnsiga.mm"
include "0elsiga.mm"
include "mp2b.mm"
include "a1i.mm"
include "probvalrnd.mm"
include "fvmptd.mm"
include "orvcelval.mm"
include "ima0.mm"
include "fveq2i.mm"
include "probnul.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "ciun.mm"
include "wfun.mm"
include "rrvvf.mm"
include "ad2antrr.mm"
include "ffun.mm"
include "unipreima.mm"
include "domprobmeas.mm"
include "nfv.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "simplll.mm"
include "simpllr.mm"
include "elelpwi.mm"
include "rrvfinvima.mm"
include "r19.21bi.mm"
include "ex.mm"
include "ralrimi.mm"
include "simprl.mm"
include "simprr.mm"
include "disjpreima.mm"
include "measvuni.mm"
include "syl112anc.mm"
include "eqtrd.mm"
include "cmpt.mm"
include "mp1i.mm"
include "simplr.mm"
include "sigaclcu.mm"
include "syl3anc.mm"
include "dstrvval.mm"
include "fvmpt2d.mm"
include "esumeq2d.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "wb.mm"
include "ismeas.mm"
include "syl3anbrc.mm"
include "dmeqd.mm"
include "dmmptg.mm"
include "eleqtrrd.mm"
include "measbasedom.mm"
include "sylibr.mm"
include "unieqd.mm"
include "unibrsiga.mm"
include "syl6eq.mm"
include "baselsiga.mm"
include "fimacnv.mm"
include "probtot.mm"
include "1red.mm"
include "elprob.mm"

theorem dstrvprob
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume dstrvprob.1: |- ( ph -> P e. Prob )
  assume dstrvprob.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume dstrvprob.3: |- ( ph -> D = ( a e. BrSiga |-> ( P ` ( X oRVC _E a ) ) ) )

  disjoint P a
  disjoint X a
  disjoint D a
  disjoint a ph
  disjoint a x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> D e. Prob )

  proof
    wph
    cD
    cmeas
    crn
    cuni
    wcel
    #
    cD
    cdm
    #
    cuni
    #
    cD
    cfv
    #
    c1
    wceq
    cD
    cprb
    wcel
    wph
    cD
    @1
    cmeas
    cfv
    #
    wcel
    @0
    wph
    cD
    cbrsiga
    cmeas
    cfv
    #
    @4
    wph
    cbrsiga
    cc0
    cpnf
    cicc
    co
    #
    cD
    wf
    #
    c0
    cD
    cfv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    va
    @10
    va
    cv
    #
    wdisj
    #
    wa
    #
    @10
    cuni
    #
    cD
    cfv
    #
    @10
    @12
    cD
    cfv
    #
    va
    cesum
    #
    wceq
    #
    wi
    #
    vx
    cbrsiga
    cpw
    #
    wral
    #
    cD
    @5
    wcel
    #
    wph
    va
    cbrsiga
    cX
    @12
    cep
    corvc
    #
    co
    #
    cP
    cfv
    #
    @6
    cD
    dstrvprob.3
    wph
    @12
    cbrsiga
    wcel
    #
    wa
    #
    @26
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    @26
    @6
    wcel
    #
    @28
    cP
    cprb
    wcel
    #
    @25
    cP
    cdm
    #
    wcel
    @30
    wph
    @32
    @27
    dstrvprob.1
    adantr
    #
    @28
    @12
    cP
    cX
    @34
    wph
    cX
    cP
    crrv
    cfv
    wcel
    #
    @27
    dstrvprob.2
    adantr
    wph
    @27
    simpr
    orvcelel
    @25
    cP
    prob01
    syl2anc
    #
    @30
    @26
    cxr
    wcel
    cc0
    @26
    cle
    wbr
    @31
    @30
    @26
    @26
    elunitrn
    rexrd
    @26
    elunitge0
    @26
    elxrge0
    sylanbrc
    syl
    #
    fmpt3d
    wph
    @8
    cX
    c0
    @24
    co
    #
    cP
    cfv
    #
    cX
    ccnv
    #
    c0
    cima
    #
    cP
    cfv
    #
    cc0
    wph
    va
    c0
    @26
    @39
    cbrsiga
    cD
    cr
    dstrvprob.3
    wph
    @12
    c0
    wceq
    #
    wa
    #
    @25
    @38
    cP
    @44
    @12
    c0
    cX
    @24
    wph
    @43
    simpr
    oveq2d
    fveq2d
    c0
    cbrsiga
    wcel
    #
    wph
    cbrsiga
    cr
    csiga
    cfv
    wcel
    #
    cbrsiga
    csiga
    crn
    cuni
    wcel
    #
    @45
    brsigarn
    cbrsiga
    cr
    elrnsiga
    #
    cbrsiga
    0elsiga
    mp2b
    a1i
    #
    wph
    @38
    cP
    dstrvprob.1
    wph
    c0
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    @49
    orvcelel
    probvalrnd
    fvmptd
    wph
    @38
    @41
    cP
    wph
    c0
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    @49
    orvcelval
    fveq2d
    wph
    @42
    c0
    cP
    cfv
    #
    cc0
    @41
    c0
    cP
    @40
    ima0
    fveq2i
    wph
    @32
    @50
    cc0
    wceq
    dstrvprob.1
    cP
    probnul
    syl
    syl5eq
    3eqtrd
    wph
    @20
    vx
    @21
    wph
    @10
    @21
    wcel
    #
    wa
    #
    @14
    @19
    @52
    @14
    wa
    #
    @40
    @15
    cima
    #
    cP
    cfv
    #
    @10
    @40
    @12
    cima
    #
    cP
    cfv
    #
    va
    cesum
    #
    @16
    @18
    @53
    @55
    va
    @10
    @56
    ciun
    #
    cP
    cfv
    #
    @58
    @53
    cX
    wfun
    #
    @55
    @60
    wceq
    @53
    @33
    cuni
    #
    cr
    cX
    wf
    #
    @61
    wph
    @63
    @51
    @14
    wph
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    rrvvf
    #
    ad2antrr
    @62
    cr
    cX
    ffun
    syl
    #
    @61
    @54
    @59
    cP
    va
    @10
    cX
    unipreima
    fveq2d
    syl
    @53
    cP
    @33
    cmeas
    cfv
    wcel
    #
    @56
    @33
    wcel
    #
    va
    @10
    wral
    @11
    va
    @10
    @56
    wdisj
    #
    @60
    @58
    wceq
    @53
    @32
    @66
    wph
    @32
    @51
    @14
    dstrvprob.1
    ad2antrr
    #
    cP
    domprobmeas
    syl
    @53
    @67
    va
    @10
    @52
    @14
    va
    @52
    va
    nfv
    @11
    @13
    va
    @11
    va
    nfv
    va
    @10
    @12
    nfdisj1
    nfan
    nfan
    #
    @53
    @12
    @10
    wcel
    #
    @67
    @53
    @71
    wa
    #
    wph
    @27
    @67
    wph
    @51
    @14
    @71
    simplll
    #
    @72
    @71
    @51
    @27
    @53
    @71
    simpr
    wph
    @51
    @14
    @71
    simpllr
    @12
    @10
    cbrsiga
    elelpwi
    syl2anc
    #
    wph
    @67
    va
    cbrsiga
    wph
    va
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    rrvfinvima
    r19.21bi
    syl2anc
    ex
    ralrimi
    @52
    @11
    @13
    simprl
    #
    @53
    @61
    @13
    @68
    @65
    @52
    @11
    @13
    simprr
    va
    @10
    @12
    cX
    disjpreima
    syl2anc
    va
    @10
    @56
    @33
    cP
    measvuni
    syl112anc
    eqtrd
    @53
    @15
    cD
    cP
    cX
    va
    @69
    wph
    @35
    @51
    @14
    dstrvprob.2
    ad2antrr
    #
    wph
    cD
    va
    cbrsiga
    @26
    cmpt
    #
    wceq
    @51
    @14
    dstrvprob.3
    ad2antrr
    @53
    @47
    @51
    @11
    @15
    cbrsiga
    wcel
    @46
    @47
    @53
    brsigarn
    @48
    mp1i
    wph
    @51
    @14
    simplr
    @75
    @10
    cbrsiga
    sigaclcu
    syl3anc
    dstrvval
    @53
    @10
    @17
    @57
    va
    @70
    @53
    @17
    @57
    wceq
    #
    va
    @10
    @70
    @53
    @71
    @78
    @72
    @17
    @26
    @57
    @72
    wph
    @27
    @17
    @26
    wceq
    @73
    @74
    wph
    va
    cbrsiga
    @26
    cD
    @29
    dstrvprob.3
    @36
    fvmpt2d
    syl2anc
    @72
    @25
    @56
    cP
    @72
    @12
    cP
    cX
    @53
    @32
    @71
    @69
    adantr
    @53
    @35
    @71
    @76
    adantr
    @74
    orvcelval
    fveq2d
    eqtrd
    ex
    ralrimi
    esumeq2d
    3eqtr4d
    ex
    ralrimiva
    @46
    @47
    @23
    @7
    @9
    @22
    w3a
    wb
    brsigarn
    @48
    vx
    va
    cbrsiga
    cD
    ismeas
    mp2b
    syl3anbrc
    wph
    @1
    cbrsiga
    cmeas
    wph
    @1
    @77
    cdm
    #
    cbrsiga
    wph
    cD
    @77
    dstrvprob.3
    dmeqd
    wph
    @31
    va
    cbrsiga
    wral
    @79
    cbrsiga
    wceq
    wph
    @31
    va
    cbrsiga
    @37
    ralrimiva
    va
    cbrsiga
    @26
    @6
    dmmptg
    syl
    eqtrd
    #
    fveq2d
    eleqtrrd
    cD
    measbasedom
    sylibr
    wph
    @3
    cr
    cD
    cfv
    c1
    wph
    @2
    cr
    cD
    wph
    @2
    cbrsiga
    cuni
    cr
    wph
    @1
    cbrsiga
    @80
    unieqd
    unibrsiga
    syl6eq
    fveq2d
    wph
    va
    cr
    @26
    c1
    cbrsiga
    cD
    cr
    dstrvprob.3
    wph
    @12
    cr
    wceq
    #
    wa
    #
    @26
    @40
    cr
    cima
    #
    cP
    cfv
    #
    c1
    @82
    @25
    @83
    cP
    @82
    @25
    cX
    cr
    @24
    co
    #
    @83
    @82
    @12
    cr
    cX
    @24
    wph
    @81
    simpr
    oveq2d
    wph
    @85
    @83
    wceq
    @81
    wph
    cr
    cP
    cX
    dstrvprob.1
    dstrvprob.2
    @46
    cr
    cbrsiga
    wcel
    wph
    brsigarn
    cr
    cbrsiga
    baselsiga
    mp1i
    #
    orvcelval
    adantr
    eqtrd
    fveq2d
    wph
    @84
    c1
    wceq
    @81
    wph
    @84
    @62
    cP
    cfv
    #
    c1
    wph
    @83
    @62
    cP
    wph
    @63
    @83
    @62
    wceq
    @64
    @62
    cr
    cX
    fimacnv
    syl
    fveq2d
    wph
    @32
    @87
    c1
    wceq
    dstrvprob.1
    cP
    probtot
    syl
    eqtrd
    adantr
    eqtrd
    @86
    wph
    1red
    fvmptd
    eqtrd
    cD
    elprob
    sylanbrc
end
