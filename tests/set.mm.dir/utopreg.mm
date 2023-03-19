include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cha.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "ccl.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "creg.mm"
include "cutop.mm"
include "utoptop.mm"
include "adantr.mm"
include "syl5eqel.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cnei.mm"
include "simp-4l.mm"
include "ad2antrr.mm"
include "syl.mm"
include "simplr.mm"
include "simpr.mm"
include "cuni.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "eqid.mm"
include "eltopss.mm"
include "syl2anc.mm"
include "utopbas.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "sseqtr4d.mm"
include "sseldd.mm"
include "utopsnnei.mm"
include "syl3anc.mm"
include "neii2.mm"
include "simprl.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "simplll.mm"
include "ad6antr.mm"
include "ustimasn.mm"
include "sseqtrd.mm"
include "simprr.mm"
include "clsss.mm"
include "ctx.mm"
include "co.mm"
include "cxp.mm"
include "ustssxp.mm"
include "sqxpeqd.mm"
include "simp-5r.mm"
include "imasncls.mm"
include "syl22anc.mm"
include "utop3cls.mm"
include "sstrd.mm"
include "imass1.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "simp-5l.mm"
include "ustex3sym.mm"
include "r19.29a.mm"
include "cmpt.mm"
include "crn.mm"
include "opnneip.mm"
include "utopsnneip.mm"
include "eleqtrd.mm"
include "wb.mm"
include "elrnmpt.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "isreg.mm"
include "sylanbrc.mm"

theorem utopreg
  let cU: class U
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  assume utopreg.1: |- J = ( unifTop ` U )


  assert |- ( ( U e. ( UnifOn ` X ) /\ J e. Haus ) -> J e. Reg )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cJ
    cha
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    vx
    cv
    #
    vb
    cv
    #
    wcel
    #
    @5
    cJ
    ccl
    cfv
    #
    cfv
    #
    va
    cv
    #
    wss
    #
    wa
    #
    vb
    cJ
    wrex
    #
    vx
    @9
    wral
    #
    va
    cJ
    wral
    cJ
    creg
    wcel
    @2
    cJ
    cU
    cutop
    cfv
    #
    ctop
    utopreg.1
    @0
    @14
    ctop
    wcel
    @1
    cU
    cX
    utoptop
    adantr
    syl5eqel
    #
    @2
    @13
    va
    cJ
    @2
    @9
    cJ
    wcel
    #
    wa
    #
    @12
    vx
    @9
    @17
    @4
    @9
    wcel
    #
    wa
    #
    @9
    vv
    cv
    #
    @4
    csn
    #
    cima
    #
    wceq
    #
    @12
    vv
    cU
    @19
    @20
    cU
    wcel
    #
    wa
    #
    @23
    wa
    #
    vw
    cv
    #
    ccnv
    @27
    wceq
    #
    @27
    @27
    @27
    ccom
    ccom
    #
    @20
    wss
    #
    wa
    #
    @12
    vw
    cU
    @26
    @27
    cU
    wcel
    #
    wa
    #
    @31
    wa
    #
    @21
    @5
    wss
    #
    @5
    @27
    @21
    cima
    #
    wss
    #
    wa
    #
    vb
    cJ
    wrex
    #
    @12
    @34
    @3
    @36
    @21
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    @39
    @34
    @19
    @3
    @19
    @24
    @23
    @32
    @31
    simp-4l
    #
    @2
    @3
    @16
    @18
    @15
    ad2antrr
    #
    syl
    #
    @34
    @19
    @32
    @41
    @42
    @26
    @32
    @31
    simplr
    #
    @19
    @32
    wa
    #
    @0
    @32
    @4
    cX
    wcel
    #
    @41
    @0
    @1
    @16
    @18
    @32
    simp-4l
    #
    @19
    @32
    simpr
    @46
    @9
    cX
    @4
    @46
    @9
    cJ
    cuni
    #
    cX
    @46
    @3
    @16
    @9
    @49
    wss
    #
    @2
    @3
    @16
    @18
    @32
    @15
    ad3antrrr
    @2
    @16
    @18
    @32
    simpllr
    @9
    cJ
    @49
    @49
    eqid
    #
    eltopss
    #
    syl2anc
    @46
    @0
    cX
    @49
    wceq
    #
    @48
    @0
    cX
    @14
    cuni
    @49
    cU
    cX
    utopbas
    cJ
    @14
    utopreg.1
    unieqi
    syl6eqr
    #
    syl
    sseqtr4d
    @17
    @18
    @32
    simplr
    sseldd
    @4
    cU
    cJ
    @27
    cX
    utopreg.1
    utopsnnei
    syl3anc
    syl2anc
    @21
    vb
    cJ
    @36
    neii2
    syl2anc
    @34
    @38
    @11
    vb
    cJ
    @34
    @5
    cJ
    wcel
    #
    wa
    #
    @38
    @11
    @56
    @38
    wa
    #
    @6
    @10
    @57
    @35
    @6
    @56
    @35
    @37
    simprl
    @4
    @5
    vx
    vex
    snss
    sylibr
    @57
    @8
    @22
    @9
    @57
    @8
    @36
    @7
    cfv
    #
    @22
    @57
    @3
    @36
    @49
    wss
    @37
    @8
    @58
    wss
    @34
    @3
    @55
    @38
    @44
    ad2antrr
    @57
    @36
    cX
    @49
    @57
    @0
    @32
    @47
    @36
    cX
    wss
    @34
    @0
    @55
    @38
    @34
    @19
    @0
    @42
    @0
    @1
    @16
    @18
    simplll
    #
    syl
    #
    ad2antrr
    #
    @34
    @32
    @55
    @38
    @45
    ad2antrr
    @19
    @47
    @24
    @23
    @32
    @31
    @55
    @38
    @19
    @9
    cX
    @4
    @19
    @9
    @49
    cX
    @19
    @3
    @16
    @50
    @43
    @2
    @16
    @18
    simplr
    #
    @52
    syl2anc
    #
    @19
    @0
    @53
    @59
    @54
    syl
    sseqtr4d
    @17
    @18
    simpr
    #
    sseldd
    #
    ad6antr
    @4
    cU
    @27
    cX
    ustimasn
    syl3anc
    @57
    @0
    @53
    @61
    @54
    syl
    sseqtrd
    @56
    @35
    @37
    simprr
    @36
    @5
    cJ
    @49
    @51
    clsss
    syl3anc
    @34
    @58
    @22
    wss
    @55
    @38
    @34
    @58
    @27
    cJ
    cJ
    ctx
    co
    ccl
    cfv
    cfv
    #
    @21
    cima
    #
    @22
    @34
    @3
    @3
    @27
    @49
    @49
    cxp
    #
    wss
    @4
    @49
    wcel
    @58
    @67
    wss
    @44
    @44
    @34
    @27
    cX
    cX
    cxp
    #
    @68
    @34
    @0
    @32
    @27
    @69
    wss
    #
    @60
    @45
    cU
    @27
    cX
    ustssxp
    syl2anc
    #
    @34
    cX
    @49
    @34
    @0
    @53
    @60
    @54
    syl
    sqxpeqd
    sseqtrd
    @34
    @9
    @49
    @4
    @34
    @19
    @50
    @42
    @63
    syl
    @17
    @18
    @24
    @23
    @32
    @31
    simp-5r
    sseldd
    @4
    @27
    cJ
    cJ
    @49
    @49
    @51
    @51
    imasncls
    syl22anc
    @34
    @66
    @20
    wss
    @67
    @22
    wss
    @34
    @66
    @29
    @20
    @34
    @0
    @70
    @32
    @28
    @66
    @29
    wss
    @60
    @71
    @45
    @33
    @28
    @30
    simprl
    cU
    cJ
    @27
    @27
    cX
    utopreg.1
    utop3cls
    syl22anc
    @33
    @28
    @30
    simprr
    sstrd
    @66
    @20
    @21
    imass1
    syl
    sstrd
    ad2antrr
    sstrd
    @25
    @23
    @32
    @31
    @55
    @38
    simp-5r
    sseqtr4d
    jca
    ex
    reximdva
    mpd
    @26
    @0
    @24
    @31
    vw
    cU
    wrex
    @0
    @1
    @16
    @18
    @24
    @23
    simp-5l
    @19
    @24
    @23
    simplr
    vw
    cU
    @20
    cX
    ustex3sym
    syl2anc
    r19.29a
    @19
    @9
    vv
    cU
    @22
    cmpt
    #
    crn
    #
    wcel
    #
    @23
    vv
    cU
    wrex
    #
    @19
    @9
    @40
    @73
    @19
    @3
    @16
    @18
    @9
    @40
    wcel
    @43
    @62
    @64
    @4
    cJ
    @9
    opnneip
    syl3anc
    @19
    @0
    @47
    @40
    @73
    wceq
    @59
    @65
    vv
    @4
    cU
    cJ
    cX
    utopreg.1
    utopsnneip
    syl2anc
    eleqtrd
    @19
    @16
    @74
    @75
    wb
    @62
    vv
    cU
    @22
    @9
    @72
    cJ
    @72
    eqid
    elrnmpt
    syl
    mpbid
    r19.29a
    ralrimiva
    ralrimiva
    va
    vx
    vb
    cJ
    isreg
    sylanbrc
end
