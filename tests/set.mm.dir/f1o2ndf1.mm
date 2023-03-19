include "wf1.mm"
include "crn.mm"
include "c2nd.mm"
include "cres.mm"
include "wfo.mm"
include "ccnv.mm"
include "wfun.mm"
include "wf1o.mm"
include "wf.mm"
include "f1f.mm"
include "fo2ndf.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "f2ndf.mm"
include "cxp.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "fssxp.mm"
include "cop.mm"
include "wrex.mm"
include "ssel2.mm"
include "elxp2.mm"
include "sylib.mm"
include "anim12dan.mm"
include "fvres.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "eqeq12d.mm"
include "vex.mm"
include "op2nd.mm"
include "eqeq12i.mm"
include "f1fun.mm"
include "funopfv.mm"
include "anim12d.mm"
include "eqcom.mm"
include "biimpi.mm"
include "eqeqan12d.mm"
include "simpl.mm"
include "anim12i.mm"
include "f1veqaeq.mm"
include "sylan2.mm"
include "opeq12.mm"
include "ex.mm"
include "syl6.mm"
include "com23.mm"
include "com14.mm"
include "syl6bi.mm"
include "pm2.43i.mm"
include "syld.mm"
include "com13.mm"
include "impcom.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "adantl.mm"
include "com12.mm"
include "adantlr.mm"
include "wb.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "simpllr.mm"
include "simpr.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "3imtr4d.mm"
include "rexlimdvva.mm"
include "rexlimivv.mm"
include "imp.mm"
include "mpcom.mm"
include "ralrimivv.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "df-f1.mm"
include "simprbi.mm"
include "dff1o3.mm"

theorem f1o2ndf1
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- ( F : A -1-1-> B -> ( 2nd |` F ) : F -1-1-onto-> ran F )

  proof
    cA
    cB
    cF
    wf1
    #
    cF
    cF
    crn
    #
    c2nd
    cF
    cres
    #
    wfo
    #
    @2
    ccnv
    wfun
    #
    cF
    @1
    @2
    wf1o
    @0
    cA
    cB
    cF
    wf
    #
    @3
    cA
    cB
    cF
    f1f
    #
    cA
    cB
    cF
    fo2ndf
    syl
    @0
    cF
    cB
    @2
    wf1
    #
    @4
    @0
    cF
    cB
    @2
    wf
    #
    vx
    cv
    #
    @2
    cfv
    #
    vy
    cv
    #
    @2
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cF
    wral
    vx
    cF
    wral
    @7
    @0
    @5
    @8
    @6
    cA
    cB
    cF
    f2ndf
    syl
    @0
    @15
    vx
    vy
    cF
    cF
    cF
    cA
    cB
    cxp
    #
    wss
    #
    @0
    @9
    cF
    wcel
    #
    @11
    cF
    wcel
    #
    wa
    #
    @15
    wi
    @0
    @5
    @17
    @6
    cA
    cB
    cF
    fssxp
    syl
    @17
    @20
    @0
    @15
    @17
    @20
    @0
    @15
    wi
    #
    @9
    va
    cv
    #
    vv
    cv
    #
    cop
    #
    wceq
    #
    vv
    cB
    wrex
    va
    cA
    wrex
    #
    @11
    vb
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    vw
    cB
    wrex
    vb
    cA
    wrex
    #
    wa
    @17
    @20
    wa
    #
    @21
    @17
    @18
    @26
    @19
    @31
    @17
    @18
    wa
    @9
    @16
    wcel
    @26
    cF
    @16
    @9
    ssel2
    va
    vv
    @9
    cA
    cB
    elxp2
    sylib
    @17
    @19
    wa
    @11
    @16
    wcel
    @31
    cF
    @16
    @11
    ssel2
    vb
    vw
    @11
    cA
    cB
    elxp2
    sylib
    anim12dan
    @26
    @31
    @32
    @21
    wi
    #
    @25
    @31
    @33
    wi
    #
    va
    vv
    cA
    cB
    @22
    cA
    wcel
    #
    @23
    cB
    wcel
    #
    wa
    #
    @25
    @34
    @37
    @25
    wa
    #
    @30
    @33
    vb
    vw
    cA
    cB
    @38
    @27
    cA
    wcel
    #
    @28
    cB
    wcel
    #
    wa
    #
    wa
    #
    @30
    @33
    @42
    @30
    wa
    #
    @17
    @24
    cF
    wcel
    #
    @29
    cF
    wcel
    #
    wa
    #
    wa
    #
    @0
    @24
    @2
    cfv
    #
    @29
    @2
    cfv
    #
    wceq
    #
    @24
    @29
    wceq
    #
    wi
    #
    wi
    #
    @32
    @21
    @42
    @47
    @53
    wi
    #
    @30
    @37
    @41
    @54
    @25
    @47
    @37
    @41
    wa
    #
    @53
    @46
    @55
    @53
    wi
    @17
    @46
    @55
    @53
    @46
    @55
    wa
    #
    @50
    @0
    @51
    @56
    @50
    @24
    c2nd
    cfv
    #
    @29
    c2nd
    cfv
    #
    wceq
    #
    @0
    @51
    wi
    #
    @56
    @48
    @57
    @49
    @58
    @46
    @48
    @57
    wceq
    #
    @55
    @44
    @61
    @45
    @24
    cF
    c2nd
    fvres
    adantr
    adantr
    @45
    @49
    @58
    wceq
    @44
    @55
    @29
    cF
    c2nd
    fvres
    ad2antlr
    eqeq12d
    @59
    vv
    vw
    weq
    #
    @56
    @60
    @57
    @23
    @58
    @28
    @22
    @23
    va
    vex
    vv
    vex
    op2nd
    @27
    @28
    vb
    vex
    vw
    vex
    op2nd
    eqeq12i
    @56
    @0
    @62
    @51
    @55
    @46
    @0
    @62
    @51
    wi
    #
    wi
    @0
    @46
    @55
    @63
    @0
    @46
    @22
    cF
    cfv
    #
    @23
    wceq
    #
    @27
    cF
    cfv
    #
    @28
    wceq
    #
    wa
    #
    @55
    @63
    wi
    @0
    cF
    wfun
    #
    @46
    @68
    wi
    cA
    cB
    cF
    f1fun
    @69
    @44
    @65
    @45
    @67
    @22
    @23
    cF
    funopfv
    @27
    @28
    cF
    funopfv
    anim12d
    syl
    @0
    @55
    @68
    @63
    @62
    @55
    @68
    @0
    @51
    @62
    @55
    @68
    @60
    wi
    wi
    @68
    @62
    @55
    @62
    @60
    @68
    @62
    @64
    @66
    wceq
    #
    @55
    @62
    @60
    wi
    wi
    @65
    @67
    @23
    @64
    @28
    @66
    @65
    @23
    @64
    wceq
    @64
    @23
    eqcom
    biimpi
    @67
    @28
    @66
    wceq
    @66
    @28
    eqcom
    biimpi
    eqeqan12d
    @0
    @55
    @62
    @70
    @51
    @0
    @55
    @62
    @70
    @51
    wi
    wi
    @0
    @55
    wa
    #
    @70
    @62
    @51
    @71
    @70
    va
    vb
    weq
    #
    @63
    @55
    @0
    @35
    @39
    wa
    @70
    @72
    wi
    @37
    @35
    @41
    @39
    @35
    @36
    simpl
    @39
    @40
    simpl
    anim12i
    cA
    cB
    @22
    @27
    cF
    f1veqaeq
    sylan2
    @72
    @62
    @51
    @22
    @23
    @27
    @28
    opeq12
    ex
    syl6
    com23
    ex
    com14
    syl6bi
    com14
    pm2.43i
    com14
    com23
    syld
    com13
    impcom
    com23
    syl5bi
    sylbid
    com23
    ex
    adantl
    com12
    adantlr
    adantr
    @43
    @20
    @46
    @17
    @42
    @18
    @44
    @30
    @19
    @45
    @25
    @18
    @44
    wb
    @37
    @41
    @9
    @24
    cF
    eleq1
    ad2antlr
    @11
    @29
    cF
    eleq1
    bi2anan9
    anbi2d
    @43
    @15
    @52
    @0
    @43
    @13
    @50
    @14
    @51
    @42
    @30
    @10
    @48
    @12
    @49
    @25
    @10
    @48
    wceq
    @37
    @41
    @9
    @24
    @2
    fveq2
    ad2antlr
    @11
    @29
    @2
    fveq2
    eqeqan12d
    @43
    @9
    @24
    @11
    @29
    @37
    @25
    @41
    @30
    simpllr
    @42
    @30
    simpr
    eqeq12d
    imbi12d
    imbi2d
    3imtr4d
    ex
    rexlimdvva
    ex
    rexlimivv
    imp
    mpcom
    ex
    com23
    mpcom
    ralrimivv
    vx
    vy
    cF
    cB
    @2
    dff13
    sylanbrc
    @7
    @8
    @4
    cF
    cB
    @2
    df-f1
    simprbi
    syl
    cF
    @1
    @2
    dff1o3
    sylanbrc
end
