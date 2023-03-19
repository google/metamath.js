include "cpw.mm"
include "wss.mm"
include "crpss.mm"
include "wor.mm"
include "cuni.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "cfn.mm"
include "wa.mm"
include "cdif.mm"
include "cfin2.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "simpll1.mm"
include "wceq.mm"
include "wrex.mm"
include "ssel2.mm"
include "elpwid.mm"
include "ssdifd.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "selpw.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "syl.mm"
include "simplrr.mm"
include "difid.mm"
include "eqcomi.mm"
include "difeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "0ex.mm"
include "sylibr.mm"
include "ne0i.mm"
include "3syl.mm"
include "simpll2.mm"
include "wo.mm"
include "wral.mm"
include "weq.mm"
include "cbvrexv.mm"
include "wi.mm"
include "sorpssi.mm"
include "ssdif.mm"
include "orim12i.mm"
include "sseq2.mm"
include "orbi12d.mm"
include "expr.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ralbidv.mm"
include "sorpss.mm"
include "fin2i.mm"
include "syl22anc.mm"
include "simpll3.mm"
include "cbvmptv.mm"
include "ibi.mm"
include "adantl.mm"
include "difexg.mm"
include "mp2b.mm"
include "elssuni.mm"
include "simplr.mm"
include "sseqtrd.mm"
include "adantll.mm"
include "cun.mm"
include "unss2.mm"
include "uncom.mm"
include "undif1.mm"
include "eqtri.mm"
include "a1i.mm"
include "ad2antrr.mm"
include "simpllr.mm"
include "ssdif0.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "uni0c.mm"
include "sylib.mm"
include "eqeq1.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "eqssd.mm"
include "simpll.mm"
include "eqeltrd.mm"
include "ex.mm"
include "mtod.mm"
include "simplrl.mm"
include "syl12anc.mm"
include "orel1.mm"
include "sylc.mm"
include "undif.mm"
include "sseq12d.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "syl6bi.mm"
include "syl5.mm"
include "mpd.mm"
include "ad2antrl.mm"
include "simprl.mm"
include "rexlimdvaa.mm"
include "pm2.65da.mm"

theorem fin1a2lem13
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cX: class X


  assert |- ( ( ( A C_ ~P B /\ [C.] Or A /\ -. U. A e. A ) /\ ( -. C e. Fin /\ C e. A ) ) -> -. ( B \ C ) e. Fin2 )

  proof
    cA
    cB
    cpw
    #
    wss
    #
    cA
    crpss
    wor
    #
    cA
    cuni
    #
    cA
    wcel
    #
    wn
    #
    w3a
    #
    cC
    cfn
    wcel
    wn
    #
    cC
    cA
    wcel
    #
    wa
    #
    wa
    #
    cB
    cC
    cdif
    #
    cfin2
    wcel
    #
    vg
    cA
    vg
    cv
    #
    cC
    cdif
    #
    cmpt
    #
    crn
    #
    cuni
    #
    @16
    wcel
    #
    @10
    @12
    wa
    #
    @12
    @16
    @11
    cpw
    #
    wss
    #
    @16
    c0
    wne
    #
    @16
    crpss
    wor
    #
    @18
    @10
    @12
    simpr
    @19
    @1
    @21
    @1
    @2
    @5
    @9
    @12
    simpll1
    @1
    vf
    @16
    @20
    @1
    vf
    cv
    #
    @14
    wceq
    #
    vg
    cA
    wrex
    #
    @24
    @11
    wss
    #
    @24
    @16
    wcel
    #
    @24
    @20
    wcel
    @1
    @25
    @27
    vg
    cA
    @1
    @13
    cA
    wcel
    #
    wa
    #
    @27
    @25
    @14
    @11
    wss
    @30
    @13
    cB
    cC
    @30
    @13
    cB
    cA
    @0
    @13
    ssel2
    elpwid
    ssdifd
    @24
    @14
    @11
    sseq1
    syl5ibrcom
    rexlimdva
    @24
    cvv
    wcel
    @28
    @26
    wb
    vf
    vex
    vg
    cA
    @14
    @24
    @15
    cvv
    @15
    eqid
    #
    elrnmpt
    ax-mp
    #
    vf
    @11
    selpw
    3imtr4g
    ssrdv
    syl
    @19
    @8
    c0
    @16
    wcel
    #
    @22
    @6
    @7
    @8
    @12
    simplrr
    #
    @8
    c0
    @14
    wceq
    #
    vg
    cA
    wrex
    #
    @33
    @8
    c0
    cC
    cC
    cdif
    #
    wceq
    #
    @36
    @37
    c0
    cC
    difid
    eqcomi
    @35
    @38
    vg
    cC
    cA
    @13
    cC
    wceq
    @14
    @37
    c0
    @13
    cC
    cC
    difeq1
    eqeq2d
    rspcev
    mpan2
    c0
    cvv
    wcel
    @33
    @36
    wb
    0ex
    vg
    cA
    @14
    c0
    @15
    cvv
    @31
    elrnmpt
    ax-mp
    sylibr
    @16
    c0
    ne0i
    3syl
    @19
    @2
    @23
    @1
    @2
    @5
    @9
    @12
    simpll2
    #
    @2
    vx
    cv
    #
    @24
    wss
    #
    @24
    @40
    wss
    #
    wo
    #
    vf
    @16
    wral
    #
    vx
    @16
    wral
    @23
    @2
    @44
    vx
    @16
    @40
    @16
    wcel
    #
    @40
    @14
    wceq
    #
    vg
    cA
    wrex
    #
    @2
    @44
    @40
    cvv
    wcel
    #
    @45
    @47
    wb
    vx
    vex
    #
    vg
    cA
    @14
    @40
    @15
    cvv
    @31
    elrnmpt
    ax-mp
    @47
    @40
    ve
    cv
    #
    cC
    cdif
    #
    wceq
    #
    ve
    cA
    wrex
    @2
    @44
    @46
    @52
    vg
    ve
    cA
    vg
    ve
    weq
    @14
    @51
    @40
    @13
    @50
    cC
    difeq1
    eqeq2d
    cbvrexv
    @2
    @52
    @44
    ve
    cA
    @2
    @50
    cA
    wcel
    #
    wa
    #
    @44
    @52
    @51
    @24
    wss
    #
    @24
    @51
    wss
    #
    wo
    #
    vf
    @16
    wral
    @54
    @57
    vf
    @16
    @28
    @26
    @54
    @57
    @32
    @54
    @25
    @57
    vg
    cA
    @2
    @53
    @29
    @25
    @57
    wi
    @2
    @53
    @29
    wa
    wa
    #
    @57
    @25
    @51
    @14
    wss
    #
    @14
    @51
    wss
    #
    wo
    #
    @58
    @50
    @13
    wss
    #
    @13
    @50
    wss
    #
    wo
    @61
    cA
    @50
    @13
    sorpssi
    @62
    @59
    @63
    @60
    @50
    @13
    cC
    ssdif
    @13
    @50
    cC
    ssdif
    orim12i
    syl
    @25
    @55
    @59
    @56
    @60
    @24
    @14
    @51
    sseq2
    @24
    @14
    @51
    sseq1
    orbi12d
    syl5ibrcom
    expr
    rexlimdv
    syl5bi
    ralrimiv
    @52
    @43
    @57
    vf
    @16
    @52
    @41
    @55
    @42
    @56
    @40
    @51
    @24
    sseq1
    @40
    @51
    @24
    sseq2
    orbi12d
    ralbidv
    syl5ibrcom
    rexlimdva
    syl5bi
    syl5bi
    ralrimiv
    vx
    vf
    @16
    sorpss
    sylibr
    syl
    @11
    @16
    fin2i
    syl22anc
    @19
    @18
    @4
    @1
    @2
    @5
    @9
    @12
    simpll3
    #
    @18
    @17
    @24
    cC
    cdif
    #
    wceq
    #
    vf
    cA
    wrex
    #
    @19
    @4
    @18
    @67
    vf
    cA
    @65
    @17
    @15
    @16
    vg
    vf
    cA
    @14
    @65
    @13
    @24
    cC
    difeq1
    cbvmptv
    elrnmpt
    ibi
    @19
    @66
    @4
    vf
    cA
    @19
    @24
    cA
    wcel
    #
    @66
    wa
    #
    wa
    #
    @3
    @24
    cA
    @70
    @3
    @24
    @70
    vh
    cv
    #
    @24
    wss
    #
    vh
    cA
    wral
    @3
    @24
    wss
    @70
    @72
    vh
    cA
    @70
    @71
    cA
    wcel
    #
    wa
    #
    @71
    cC
    cdif
    #
    @65
    wss
    #
    @72
    @69
    @73
    @76
    @19
    @69
    @73
    wa
    #
    @75
    @17
    @65
    @77
    @75
    @16
    wcel
    #
    @75
    @17
    wss
    @77
    @75
    @14
    wceq
    #
    vg
    cA
    wrex
    #
    @78
    @73
    @80
    @69
    @73
    @75
    @75
    wceq
    #
    @80
    @75
    eqid
    @79
    @81
    vg
    @71
    cA
    vg
    vh
    weq
    @14
    @75
    @75
    @13
    @71
    cC
    difeq1
    eqeq2d
    rspcev
    mpan2
    adantl
    @71
    cvv
    wcel
    @75
    cvv
    wcel
    @78
    @80
    wb
    vh
    vex
    @71
    cC
    cvv
    difexg
    vg
    cA
    @14
    @75
    @15
    cvv
    @31
    elrnmpt
    mp2b
    sylibr
    @75
    @16
    elssuni
    syl
    @68
    @66
    @73
    simplr
    sseqtrd
    adantll
    @76
    cC
    @75
    cun
    #
    cC
    @65
    cun
    #
    wss
    #
    @74
    @72
    @75
    @65
    cC
    unss2
    @74
    @84
    @71
    cC
    cun
    #
    @24
    wss
    #
    @72
    @74
    @82
    @85
    @83
    @24
    @82
    @85
    wceq
    @74
    @82
    @75
    cC
    cun
    @85
    cC
    @75
    uncom
    @71
    cC
    undif1
    eqtri
    a1i
    @74
    cC
    @24
    wss
    #
    @83
    @24
    wceq
    @74
    @24
    cC
    wss
    #
    wn
    @88
    @87
    wo
    #
    @87
    @74
    @88
    @4
    @19
    @5
    @69
    @73
    @64
    ad2antrr
    @74
    @8
    @66
    @88
    @4
    wi
    @19
    @8
    @69
    @73
    @34
    ad2antrr
    #
    @19
    @68
    @66
    @73
    simplrr
    @8
    @66
    wa
    #
    @88
    @4
    @91
    @88
    wa
    #
    @3
    cC
    cA
    @92
    @3
    cC
    @92
    @40
    cC
    wss
    #
    vx
    cA
    wral
    @3
    cC
    wss
    @92
    @93
    vx
    cA
    @92
    @40
    cA
    wcel
    #
    wa
    #
    @40
    cC
    cdif
    #
    c0
    wceq
    #
    @93
    @95
    @96
    @16
    wcel
    #
    @50
    c0
    wceq
    #
    ve
    @16
    wral
    #
    @97
    @94
    @98
    @92
    @94
    @96
    @14
    wceq
    #
    vg
    cA
    wrex
    #
    @98
    @94
    @96
    @96
    wceq
    #
    @102
    @96
    eqid
    @101
    @103
    vg
    @40
    cA
    vg
    vx
    weq
    @14
    @96
    @96
    @13
    @40
    cC
    difeq1
    eqeq2d
    rspcev
    mpan2
    @48
    @96
    cvv
    wcel
    @98
    @102
    wb
    @49
    @40
    cC
    cvv
    difexg
    vg
    cA
    @14
    @96
    @15
    cvv
    @31
    elrnmpt
    mp2b
    sylibr
    adantl
    @95
    @17
    c0
    wceq
    @100
    @95
    @17
    @65
    c0
    @8
    @66
    @88
    @94
    simpllr
    @88
    @65
    c0
    wceq
    #
    @91
    @94
    @88
    @104
    @24
    cC
    ssdif0
    biimpi
    ad2antlr
    eqtrd
    ve
    @16
    uni0c
    sylib
    @99
    @97
    ve
    @96
    @16
    @50
    @96
    c0
    eqeq1
    rspcva
    syl2anc
    @40
    cC
    ssdif0
    sylibr
    ralrimiva
    vx
    cA
    cC
    unissb
    sylibr
    @8
    cC
    @3
    wss
    @66
    @88
    cC
    cA
    elssuni
    ad2antrr
    eqssd
    @8
    @66
    @88
    simpll
    eqeltrd
    ex
    syl2anc
    mtod
    @74
    @2
    @68
    @8
    @89
    @19
    @2
    @69
    @73
    @39
    ad2antrr
    @19
    @68
    @66
    @73
    simplrl
    @90
    cA
    @24
    cC
    sorpssi
    syl12anc
    @88
    @87
    orel1
    sylc
    cC
    @24
    undif
    sylib
    sseq12d
    @71
    @85
    wss
    @86
    @72
    @71
    cC
    ssun1
    @71
    @85
    @24
    sstr
    mpan
    syl6bi
    syl5
    mpd
    ralrimiva
    vh
    cA
    @24
    unissb
    sylibr
    @68
    @24
    @3
    wss
    @19
    @66
    @24
    cA
    elssuni
    ad2antrl
    eqssd
    @19
    @68
    @66
    simprl
    eqeltrd
    rexlimdvaa
    syl5
    mtod
    pm2.65da
end
