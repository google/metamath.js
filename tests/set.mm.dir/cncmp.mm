include "ccmp.mm"
include "wcel.mm"
include "wfo.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cntop2.mm"
include "3ad2ant3.mm"
include "wss.mm"
include "elpwi.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "simpl1.mm"
include "wf.mm"
include "simprl.mm"
include "sselda.mm"
include "simpl3.mm"
include "cnima.mm"
include "sylan.mm"
include "syldan.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "simprr.mm"
include "imaeq2d.mm"
include "cnf.mm"
include "fimacnv.mm"
include "ciun.mm"
include "cab.mm"
include "ralrimiva.mm"
include "dfiun2g.mm"
include "imauni.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "3eqtr4g.mm"
include "3eqtr3d.mm"
include "cmpcov.mm"
include "syl3anc.mm"
include "elfpw.mm"
include "simprll.mm"
include "simpll2.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "wb.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "ralrnmpt.mm"
include "mpbird.mm"
include "adantr.mm"
include "r19.21bi.mm"
include "simprlr.mm"
include "abrexfi.mm"
include "syl5eqel.mm"
include "sylanbrc.mm"
include "cdm.mm"
include "fdm.mm"
include "fof.mm"
include "3syl.mm"
include "foima.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expr.mm"
include "sylan2b.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "sylan2.mm"
include "iscmp.mm"

theorem cncmp
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume cncmp.2: |- Y = U. K


  assert |- ( ( J e. Comp /\ F : X -onto-> Y /\ F e. ( J Cn K ) ) -> K e. Comp )

  proof
    cJ
    ccmp
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cK
    ctop
    wcel
    #
    cY
    vu
    cv
    #
    cuni
    #
    wceq
    #
    cY
    vv
    cv
    #
    cuni
    #
    wceq
    #
    vv
    @5
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vu
    cK
    cpw
    #
    wral
    cK
    ccmp
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    cntop2
    3ad2ant3
    @3
    @13
    vu
    @14
    @5
    @14
    wcel
    @3
    @5
    cK
    wss
    #
    @13
    @5
    cK
    elpwi
    @3
    @15
    @7
    @12
    @3
    @15
    @7
    wa
    #
    wa
    #
    cJ
    cuni
    #
    vs
    cv
    #
    cuni
    #
    wceq
    #
    vs
    vy
    @5
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cpw
    cfn
    cin
    #
    wrex
    #
    @12
    @17
    @0
    @26
    cJ
    wss
    #
    @18
    @26
    cuni
    #
    wceq
    @28
    @0
    @1
    @2
    @16
    simpl1
    @17
    @5
    cJ
    @25
    wf
    @29
    @17
    vy
    @5
    @24
    cJ
    @25
    @17
    @23
    @5
    wcel
    #
    @23
    cK
    wcel
    #
    @24
    cJ
    wcel
    #
    @17
    @5
    cK
    @23
    @3
    @15
    @7
    simprl
    sselda
    #
    @17
    @2
    @32
    @33
    @0
    @1
    @2
    @16
    simpl3
    #
    @23
    cF
    cJ
    cK
    cnima
    sylan
    syldan
    #
    @25
    eqid
    #
    fmptd
    @5
    cJ
    @25
    frn
    syl
    @17
    @22
    cY
    cima
    #
    @22
    @6
    cima
    #
    @18
    @30
    @17
    cY
    @6
    @22
    @3
    @15
    @7
    simprr
    imaeq2d
    @17
    @18
    cY
    cF
    wf
    #
    @38
    @18
    wceq
    @17
    @2
    @40
    @35
    cF
    cJ
    cK
    @18
    cY
    @18
    eqid
    #
    cncmp.2
    cnf
    syl
    #
    @18
    cY
    cF
    fimacnv
    syl
    @17
    vy
    @5
    @24
    ciun
    #
    vx
    cv
    @24
    wceq
    vy
    @5
    wrex
    vx
    cab
    #
    cuni
    #
    @39
    @30
    @17
    @33
    vy
    @5
    wral
    #
    @43
    @45
    wceq
    @17
    @33
    vy
    @5
    @36
    ralrimiva
    #
    vy
    vx
    @5
    @24
    cJ
    dfiun2g
    syl
    vy
    @22
    @5
    imauni
    @26
    @44
    vy
    vx
    @5
    @24
    @25
    @37
    rnmpt
    unieqi
    3eqtr4g
    3eqtr3d
    @26
    cJ
    @18
    vs
    @41
    cmpcov
    syl3anc
    @17
    @21
    @12
    vs
    @27
    @19
    @27
    wcel
    @17
    @19
    @26
    wss
    #
    @19
    cfn
    wcel
    #
    wa
    #
    @21
    @12
    wi
    @19
    @26
    elfpw
    @17
    @50
    @21
    @12
    @17
    @50
    @21
    wa
    #
    wa
    #
    vc
    @19
    cF
    vc
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    @11
    wcel
    #
    cY
    @56
    cuni
    #
    wceq
    #
    @12
    @52
    @56
    @5
    wss
    #
    @56
    cfn
    wcel
    #
    @57
    @52
    @19
    @5
    @55
    wf
    @60
    @52
    vc
    @19
    @54
    @5
    @55
    @52
    @53
    @19
    wcel
    @53
    @26
    wcel
    @54
    @5
    wcel
    #
    @52
    @19
    @26
    @53
    @17
    @48
    @49
    @21
    simprll
    sselda
    @52
    @62
    vc
    @26
    @17
    @62
    vc
    @26
    wral
    #
    @51
    @17
    @63
    cF
    @24
    cima
    #
    @5
    wcel
    #
    vy
    @5
    wral
    #
    @17
    @65
    vy
    @5
    @17
    @31
    wa
    #
    @64
    @23
    @5
    @67
    @1
    @23
    cY
    wss
    #
    @64
    @23
    wceq
    @0
    @1
    @2
    @16
    @31
    simpll2
    @67
    @32
    @68
    @34
    @32
    @23
    cK
    cuni
    cY
    @23
    cK
    elssuni
    cncmp.2
    syl6sseqr
    syl
    cX
    cY
    @23
    cF
    foimacnv
    syl2anc
    @17
    @31
    simpr
    eqeltrd
    ralrimiva
    @17
    @46
    @63
    @66
    wb
    @47
    @62
    @65
    vy
    vc
    @5
    @24
    @25
    cJ
    @37
    @53
    @24
    wceq
    @54
    @64
    @5
    @53
    @24
    cF
    imaeq2
    eleq1d
    ralrnmpt
    syl
    mpbird
    adantr
    r19.21bi
    syldan
    #
    @55
    eqid
    #
    fmptd
    @19
    @5
    @55
    frn
    syl
    @52
    @49
    @61
    @17
    @48
    @49
    @21
    simprlr
    @49
    @56
    vd
    cv
    @54
    wceq
    vc
    @19
    wrex
    vd
    cab
    #
    cfn
    vc
    vd
    @19
    @54
    @55
    @70
    rnmpt
    #
    vc
    vd
    @19
    @54
    abrexfi
    syl5eqel
    syl
    @56
    @5
    elfpw
    sylanbrc
    @52
    cF
    cX
    cima
    #
    cF
    @20
    cima
    #
    cY
    @58
    @52
    cX
    @20
    cF
    @52
    cF
    cdm
    #
    @18
    cX
    @20
    @52
    @40
    @75
    @18
    wceq
    @17
    @40
    @51
    @42
    adantr
    @18
    cY
    cF
    fdm
    syl
    @52
    @1
    cX
    cY
    cF
    wf
    @75
    cX
    wceq
    @0
    @1
    @2
    @16
    @51
    simpll2
    #
    cX
    cY
    cF
    fof
    cX
    cY
    cF
    fdm
    3syl
    @17
    @50
    @21
    simprr
    3eqtr3d
    imaeq2d
    @52
    @1
    @73
    cY
    wceq
    @76
    cX
    cY
    cF
    foima
    syl
    @52
    vc
    @19
    @54
    ciun
    #
    @71
    cuni
    #
    @74
    @58
    @52
    @62
    vc
    @19
    wral
    @77
    @78
    wceq
    @52
    @62
    vc
    @19
    @69
    ralrimiva
    vc
    vd
    @19
    @54
    @5
    dfiun2g
    syl
    vc
    cF
    @19
    imauni
    @56
    @71
    @72
    unieqi
    3eqtr4g
    3eqtr3d
    @10
    @59
    vv
    @56
    @11
    @8
    @56
    wceq
    @9
    @58
    cY
    @8
    @56
    unieq
    eqeq2d
    rspcev
    syl2anc
    expr
    sylan2b
    rexlimdva
    mpd
    expr
    sylan2
    ralrimiva
    vu
    vv
    cK
    cY
    cncmp.2
    iscmp
    sylanbrc
end
