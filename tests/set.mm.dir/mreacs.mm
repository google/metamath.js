include "cv.mm"
include "cacs.mm"
include "cfv.mm"
include "cpw.mm"
include "cmre.mm"
include "wcel.mm"
include "wceq.mm"
include "fveq2.mm"
include "pweq.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "wtru.mm"
include "wss.mm"
include "acsmre.mm"
include "mresspw.mm"
include "syl.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "a1i.mm"
include "cint.mm"
include "cin.mm"
include "wf.mm"
include "cfn.mm"
include "cima.mm"
include "cuni.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "vex.mm"
include "mremre.mm"
include "mp1i.mm"
include "sstr.mm"
include "mpan2.mm"
include "mrerintcl.mm"
include "syl2anc.mm"
include "cmrc.mm"
include "ciun.mm"
include "cmpt.mm"
include "cxp.mm"
include "wel.mm"
include "ssel2.mm"
include "acsmred.mm"
include "eqid.mm"
include "mrcssvd.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "iunss.mm"
include "elpw2.mm"
include "fmptd.mm"
include "fssxp.mm"
include "vpwex.mm"
include "xpex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "adantlr.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "acsfiel2.mm"
include "ralbidva.mm"
include "ralbii.mm"
include "ralcom.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "elrint2.mm"
include "adantl.mm"
include "wfun.mm"
include "funmpt.mm"
include "funiunfv.mm"
include "ax-mp.mm"
include "sseq1i.mm"
include "inss1.mm"
include "sspwb.mm"
include "sylib.mm"
include "syl5ss.mm"
include "sselda.mm"
include "ad2antrr.mm"
include "weq.mm"
include "iuneq2d.mm"
include "fvmptg.mm"
include "sseq1d.mm"
include "syl5bb.mm"
include "syl5bbr.mm"
include "3bitr4d.mm"
include "jca.mm"
include "feq1.mm"
include "imaeq1.mm"
include "unieqd.mm"
include "bibi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "isacs.mm"
include "sylanbrc.mm"
include "ismred2.mm"
include "trud.mm"
include "vtoclg.mm"

theorem mreacs
  let cV: class V
  let cX: class X
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cT: class T
  let vx: setvar x
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f


  assert |- ( X e. V -> ( ACS ` X ) e. ( Moore ` ~P X ) )

  proof
    vx
    cv
    #
    cacs
    cfv
    #
    @0
    cpw
    #
    cmre
    cfv
    #
    wcel
    #
    cX
    cacs
    cfv
    #
    cX
    cpw
    #
    cmre
    cfv
    #
    wcel
    vx
    cX
    cV
    @0
    cX
    wceq
    #
    @1
    @5
    @3
    @7
    @0
    cX
    cacs
    fveq2
    @8
    @2
    @6
    cmre
    @0
    cX
    pweq
    fveq2d
    eleq12d
    @4
    wtru
    @1
    @2
    va
    @1
    @2
    cpw
    #
    wss
    wtru
    va
    @1
    @9
    va
    cv
    #
    @1
    wcel
    #
    @10
    @2
    wss
    #
    @10
    @9
    wcel
    @11
    @10
    @0
    cmre
    cfv
    #
    wcel
    @12
    @10
    @0
    acsmre
    #
    @10
    @0
    mresspw
    syl
    va
    @2
    selpw
    sylibr
    ssriv
    a1i
    @10
    @1
    wss
    #
    @2
    @10
    cint
    cin
    #
    @1
    wcel
    #
    wtru
    @15
    @16
    @13
    wcel
    #
    @2
    @2
    vf
    cv
    #
    wf
    #
    vb
    cv
    #
    @16
    wcel
    #
    @19
    @21
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    @21
    wss
    #
    wb
    #
    vb
    @2
    wral
    #
    wa
    #
    vf
    wex
    #
    @17
    @15
    @13
    @3
    wcel
    #
    @10
    @13
    wss
    #
    @18
    @0
    cvv
    wcel
    #
    @32
    @15
    vx
    vex
    #
    cvv
    @0
    mremre
    mp1i
    @15
    @1
    @13
    wss
    @33
    va
    @1
    @13
    @14
    ssriv
    @10
    @1
    @13
    sstr
    mpan2
    @13
    @10
    @2
    mrerintcl
    syl2anc
    @15
    vc
    @2
    vd
    @10
    vc
    cv
    #
    vd
    cv
    #
    cmrc
    cfv
    #
    cfv
    #
    ciun
    #
    cmpt
    #
    cvv
    wcel
    #
    @2
    @2
    @41
    wf
    #
    @22
    @41
    @24
    cima
    #
    cuni
    #
    @21
    wss
    #
    wb
    #
    vb
    @2
    wral
    #
    wa
    #
    @31
    @15
    @41
    @2
    @2
    cxp
    #
    wss
    #
    @50
    cvv
    wcel
    @42
    @15
    @43
    @51
    @15
    vc
    @2
    @40
    @2
    @41
    @15
    @36
    @2
    wcel
    #
    wa
    #
    @40
    @0
    wss
    #
    @40
    @2
    wcel
    @53
    @39
    @0
    wss
    #
    vd
    @10
    wral
    #
    @54
    @15
    @56
    @52
    @15
    @55
    vd
    @10
    @15
    vd
    va
    wel
    #
    wa
    #
    @37
    @36
    @38
    @0
    @58
    @37
    @0
    @10
    @1
    @37
    ssel2
    #
    acsmred
    #
    @38
    eqid
    #
    mrcssvd
    ralrimiva
    adantr
    vd
    @10
    @39
    @0
    iunss
    sylibr
    @40
    @0
    @35
    elpw2
    sylibr
    @41
    eqid
    #
    fmptd
    #
    @2
    @2
    @41
    fssxp
    syl
    @2
    @2
    vx
    vpwex
    #
    @64
    xpex
    @41
    @50
    cvv
    ssexg
    sylancl
    @15
    @43
    @48
    @63
    @15
    @47
    vb
    @2
    @15
    @21
    @2
    wcel
    #
    wa
    #
    vb
    vd
    wel
    #
    vd
    @10
    wral
    #
    vd
    @10
    ve
    cv
    #
    @38
    cfv
    #
    ciun
    #
    @21
    wss
    #
    ve
    @24
    wral
    #
    @22
    @46
    @66
    @68
    @70
    @21
    wss
    #
    ve
    @24
    wral
    #
    vd
    @10
    wral
    #
    @73
    @66
    @67
    @75
    vd
    @10
    @66
    @57
    wa
    @37
    @1
    wcel
    #
    @21
    @0
    wss
    #
    @67
    @75
    wb
    @15
    @57
    @77
    @65
    @59
    adantlr
    @65
    @78
    @15
    @57
    @21
    @0
    elpwi
    #
    ad2antlr
    ve
    @37
    @21
    @38
    @0
    @61
    acsfiel2
    syl2anc
    ralbidva
    @73
    @74
    vd
    @10
    wral
    #
    ve
    @24
    wral
    @76
    @72
    @80
    ve
    @24
    vd
    @10
    @70
    @21
    iunss
    ralbii
    @74
    ve
    vd
    @24
    @10
    ralcom
    bitri
    syl6bbr
    @65
    @22
    @68
    wb
    @15
    vd
    @2
    @10
    @21
    elrint2
    adantl
    @46
    ve
    @24
    @69
    @41
    cfv
    #
    ciun
    #
    @21
    wss
    #
    @66
    @73
    @82
    @45
    @21
    @41
    wfun
    @82
    @45
    wceq
    vc
    @2
    @40
    funmpt
    ve
    @24
    @41
    funiunfv
    ax-mp
    sseq1i
    @83
    @81
    @21
    wss
    #
    ve
    @24
    wral
    @66
    @73
    ve
    @24
    @81
    @21
    iunss
    @66
    @84
    @72
    ve
    @24
    @66
    @69
    @24
    wcel
    #
    wa
    #
    @81
    @71
    @21
    @86
    @69
    @2
    wcel
    @71
    cvv
    wcel
    #
    @81
    @71
    wceq
    @66
    @24
    @2
    @69
    @66
    @24
    @23
    @2
    @23
    cfn
    inss1
    @65
    @23
    @2
    wss
    #
    @15
    @65
    @78
    @88
    @79
    @21
    @0
    sspwb
    sylib
    adantl
    syl5ss
    sselda
    @86
    @71
    @0
    wss
    #
    @34
    @87
    @86
    @70
    @0
    wss
    #
    vd
    @10
    wral
    #
    @89
    @15
    @91
    @65
    @85
    @15
    @90
    vd
    @10
    @58
    @37
    @69
    @38
    @0
    @60
    @61
    mrcssvd
    ralrimiva
    ad2antrr
    vd
    @10
    @70
    @0
    iunss
    sylibr
    @35
    @71
    @0
    cvv
    ssexg
    sylancl
    vc
    @69
    @40
    @71
    @2
    cvv
    @41
    vc
    ve
    weq
    vd
    @10
    @39
    @70
    @36
    @69
    @38
    fveq2
    iuneq2d
    @62
    fvmptg
    syl2anc
    sseq1d
    ralbidva
    syl5bb
    syl5bbr
    3bitr4d
    ralrimiva
    jca
    @30
    @49
    vf
    @41
    cvv
    @19
    @41
    wceq
    #
    @20
    @43
    @29
    @48
    @2
    @2
    @19
    @41
    feq1
    @92
    @28
    @47
    vb
    @2
    @92
    @27
    @46
    @22
    @92
    @26
    @45
    @21
    @92
    @25
    @44
    @19
    @41
    @24
    imaeq1
    unieqd
    sseq1d
    bibi2d
    ralbidv
    anbi12d
    spcegv
    sylc
    @16
    vf
    @0
    vb
    isacs
    sylanbrc
    adantl
    ismred2
    trud
    vtoclg
end
