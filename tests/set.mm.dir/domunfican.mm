include "cfn.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "cdom.mm"
include "wb.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wi.mm"
include "ensym.mm"
include "bren.mm"
include "sylib.mm"
include "w3a.mm"
include "cima.mm"
include "wss.mm"
include "ssid.mm"
include "csn.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "uneq1.mm"
include "imaeq2.mm"
include "uneq1d.mm"
include "breq12d.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "ima0.mm"
include "uneq1i.mm"
include "breq12i.mm"
include "a1i.mm"
include "wn.mm"
include "ssun1.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "anim1i.mm"
include "imim1i.mm"
include "cfv.mm"
include "unass.mm"
include "imaundi.mm"
include "wfn.mm"
include "simprlr.mm"
include "f1ofn.mm"
include "syl.mm"
include "ssun2.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "fnsnfv.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "syl6eq.mm"
include "simplr.mm"
include "incom.mm"
include "simprrl.mm"
include "minel.mm"
include "wo.mm"
include "ioran.mm"
include "elun.mm"
include "xchnxbir.mm"
include "sylanbrc.mm"
include "wf1.mm"
include "f1of1.mm"
include "adantl.mm"
include "f1elima.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "mtod.mm"
include "adantrr.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnd.mm"
include "simprrr.mm"
include "fvex.mm"
include "domunsncan.mm"
include "bitrd.mm"
include "bitr.mm"
include "ex.mm"
include "a2d.mm"
include "syl5.mm"
include "findcard2s.mm"
include "expd.mm"
include "mpani.mm"
include "3imp.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "breq2d.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "3exp.mm"
include "exlimdv.mm"
include "imp31.mm"

theorem domunfican
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f


  assert |- ( ( ( A e. Fin /\ B ~~ A ) /\ ( ( A i^i X ) = (/) /\ ( B i^i Y ) = (/) ) ) -> ( ( A u. X ) ~<_ ( B u. Y ) <-> X ~<_ Y ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    cen
    wbr
    #
    cA
    cX
    cin
    #
    c0
    wceq
    #
    cB
    cY
    cin
    #
    c0
    wceq
    #
    wa
    #
    cA
    cX
    cun
    #
    cB
    cY
    cun
    #
    cdom
    wbr
    #
    cX
    cY
    cdom
    wbr
    #
    wb
    #
    @1
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @0
    @6
    @11
    wi
    #
    @1
    cA
    cB
    cen
    wbr
    @14
    cB
    cA
    ensym
    cA
    cB
    vf
    bren
    sylib
    @0
    @13
    @15
    vf
    @0
    @13
    @6
    @11
    @0
    @13
    @6
    w3a
    @7
    @12
    cA
    cima
    #
    cY
    cun
    #
    cdom
    wbr
    #
    @10
    wb
    #
    @11
    @0
    @13
    @6
    @19
    @0
    cA
    cA
    wss
    #
    @13
    @6
    @19
    wi
    cA
    ssid
    @0
    @20
    @13
    wa
    #
    @6
    @19
    va
    cv
    #
    cA
    wss
    #
    @13
    wa
    #
    @6
    wa
    #
    @22
    cX
    cun
    #
    @12
    @22
    cima
    #
    cY
    cun
    #
    cdom
    wbr
    #
    @10
    wb
    #
    wi
    c0
    cA
    wss
    #
    @13
    wa
    #
    @6
    wa
    #
    c0
    cX
    cun
    #
    @12
    c0
    cima
    #
    cY
    cun
    #
    cdom
    wbr
    #
    @10
    wb
    #
    wi
    vb
    cv
    #
    cA
    wss
    #
    @13
    wa
    #
    @6
    wa
    #
    @39
    cX
    cun
    #
    @12
    @39
    cima
    #
    cY
    cun
    #
    cdom
    wbr
    #
    @10
    wb
    #
    wi
    #
    @39
    vc
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    @13
    wa
    #
    @6
    wa
    #
    @51
    cX
    cun
    #
    @12
    @51
    cima
    #
    cY
    cun
    #
    cdom
    wbr
    #
    @10
    wb
    #
    wi
    #
    @21
    @6
    wa
    #
    @19
    wi
    va
    vb
    vc
    cA
    @22
    c0
    wceq
    #
    @25
    @33
    @30
    @38
    @62
    @24
    @32
    @6
    @62
    @23
    @31
    @13
    @22
    c0
    cA
    sseq1
    anbi1d
    anbi1d
    @62
    @29
    @37
    @10
    @62
    @26
    @34
    @28
    @36
    cdom
    @22
    c0
    cX
    uneq1
    @62
    @27
    @35
    cY
    @22
    c0
    @12
    imaeq2
    uneq1d
    breq12d
    bibi1d
    imbi12d
    @22
    @39
    wceq
    #
    @25
    @42
    @30
    @47
    @63
    @24
    @41
    @6
    @63
    @23
    @40
    @13
    @22
    @39
    cA
    sseq1
    anbi1d
    anbi1d
    @63
    @29
    @46
    @10
    @63
    @26
    @43
    @28
    @45
    cdom
    @22
    @39
    cX
    uneq1
    @63
    @27
    @44
    cY
    @22
    @39
    @12
    imaeq2
    uneq1d
    breq12d
    bibi1d
    imbi12d
    @22
    @51
    wceq
    #
    @25
    @54
    @30
    @59
    @64
    @24
    @53
    @6
    @64
    @23
    @52
    @13
    @22
    @51
    cA
    sseq1
    anbi1d
    anbi1d
    @64
    @29
    @58
    @10
    @64
    @26
    @55
    @28
    @57
    cdom
    @22
    @51
    cX
    uneq1
    @64
    @27
    @56
    cY
    @22
    @51
    @12
    imaeq2
    uneq1d
    breq12d
    bibi1d
    imbi12d
    @22
    cA
    wceq
    #
    @25
    @61
    @30
    @19
    @65
    @24
    @21
    @6
    @65
    @23
    @20
    @13
    @22
    cA
    cA
    sseq1
    anbi1d
    anbi1d
    @65
    @29
    @18
    @10
    @65
    @26
    @7
    @28
    @17
    cdom
    @22
    cA
    cX
    uneq1
    @65
    @27
    @16
    cY
    @22
    cA
    @12
    imaeq2
    uneq1d
    breq12d
    bibi1d
    imbi12d
    @38
    @33
    @34
    cX
    @36
    cY
    cdom
    @34
    cX
    c0
    cun
    cX
    c0
    cX
    uncom
    cX
    un0
    eqtri
    @36
    c0
    cY
    cun
    #
    cY
    @35
    c0
    cY
    @12
    ima0
    uneq1i
    @66
    cY
    c0
    cun
    cY
    c0
    cY
    uncom
    cY
    un0
    eqtri
    eqtri
    breq12i
    a1i
    @48
    @54
    @47
    wi
    @39
    cfn
    wcel
    #
    @49
    @39
    wcel
    #
    wn
    #
    wa
    #
    @60
    @54
    @42
    @47
    @53
    @41
    @6
    @52
    @40
    @13
    @39
    @51
    wss
    @52
    @40
    wi
    @39
    @50
    ssun1
    @39
    @51
    cA
    sstr2
    ax-mp
    #
    anim1i
    anim1i
    imim1i
    @70
    @54
    @47
    @59
    @70
    @54
    @47
    @59
    wi
    #
    @70
    @54
    wa
    #
    @58
    @46
    wb
    #
    @72
    @73
    @58
    @50
    @43
    cun
    #
    @49
    @12
    cfv
    #
    csn
    #
    @45
    cun
    #
    cdom
    wbr
    #
    @46
    @73
    @55
    @75
    @57
    @78
    cdom
    @55
    @75
    wceq
    @73
    @55
    @50
    @39
    cun
    #
    cX
    cun
    @75
    @51
    @80
    cX
    @39
    @50
    uncom
    uneq1i
    @50
    @39
    cX
    unass
    eqtri
    a1i
    @73
    @57
    @44
    @77
    cun
    #
    cY
    cun
    #
    @78
    @73
    @56
    @81
    cY
    @73
    @56
    @44
    @12
    @50
    cima
    #
    cun
    @81
    @12
    @39
    @50
    imaundi
    @73
    @83
    @77
    @44
    @73
    @77
    @83
    @73
    @12
    cA
    wfn
    #
    @49
    cA
    wcel
    #
    @77
    @83
    wceq
    @73
    @13
    @84
    @70
    @52
    @13
    @6
    simprlr
    #
    cA
    cB
    @12
    f1ofn
    syl
    @53
    @85
    @70
    @6
    @52
    @85
    @13
    @52
    @50
    cA
    wss
    #
    @85
    @50
    @51
    wss
    @52
    @87
    wi
    @50
    @39
    ssun2
    @50
    @51
    cA
    sstr2
    ax-mp
    @49
    cA
    vc
    vex
    #
    snss
    sylibr
    adantr
    #
    ad2antrl
    #
    cA
    @49
    @12
    fnsnfv
    syl2anc
    eqcomd
    uneq2d
    syl5eq
    uneq1d
    @82
    @77
    @44
    cun
    #
    cY
    cun
    @78
    @81
    @91
    cY
    @44
    @77
    uncom
    uneq1i
    @77
    @44
    cY
    unass
    eqtri
    syl6eq
    breq12d
    @73
    @49
    @43
    wcel
    #
    wn
    #
    @76
    @45
    wcel
    #
    wn
    #
    @79
    @46
    wb
    @73
    @69
    @49
    cX
    wcel
    #
    wn
    #
    @93
    @67
    @69
    @54
    simplr
    @73
    @85
    cX
    cA
    cin
    #
    c0
    wceq
    @97
    @90
    @73
    @98
    @2
    c0
    cX
    cA
    incom
    @70
    @53
    @3
    @5
    simprrl
    syl5eq
    @49
    cA
    cX
    minel
    syl2anc
    @68
    @96
    wo
    @69
    @97
    wa
    @92
    @68
    @96
    ioran
    @49
    @39
    cX
    elun
    xchnxbir
    sylanbrc
    @73
    @76
    @44
    wcel
    #
    wn
    #
    @76
    cY
    wcel
    #
    wn
    #
    @95
    @70
    @53
    @100
    @6
    @70
    @53
    wa
    @99
    @68
    @67
    @69
    @53
    simplr
    @53
    @99
    @68
    wi
    @70
    @53
    @99
    @68
    @53
    cA
    cB
    @12
    wf1
    #
    @85
    @40
    @99
    @68
    wb
    @13
    @103
    @52
    cA
    cB
    @12
    f1of1
    adantl
    @89
    @52
    @40
    @13
    @71
    adantr
    cA
    cB
    @12
    @49
    @39
    f1elima
    syl3anc
    biimpd
    adantl
    mtod
    adantrr
    @73
    @76
    cB
    wcel
    cY
    cB
    cin
    #
    c0
    wceq
    @102
    @73
    cA
    cB
    @49
    @12
    @73
    @13
    cA
    cB
    @12
    wf
    @86
    cA
    cB
    @12
    f1of
    syl
    @90
    ffvelrnd
    @73
    @104
    @4
    c0
    cY
    cB
    incom
    @70
    @53
    @3
    @5
    simprrr
    syl5eq
    @76
    cB
    cY
    minel
    syl2anc
    @99
    @101
    wo
    @100
    @102
    wa
    @94
    @99
    @101
    ioran
    @76
    @44
    cY
    elun
    xchnxbir
    sylanbrc
    @49
    @76
    @43
    @45
    @88
    @49
    @12
    fvex
    domunsncan
    syl2anc
    bitrd
    @74
    @47
    @59
    @58
    @46
    @10
    bitr
    ex
    syl
    ex
    a2d
    syl5
    findcard2s
    expd
    mpani
    3imp
    @13
    @0
    @19
    @11
    wb
    @6
    @13
    @18
    @9
    @10
    @13
    @17
    @8
    @7
    cdom
    @13
    @16
    cB
    cY
    @13
    cA
    cB
    @12
    wfo
    @16
    cB
    wceq
    cA
    cB
    @12
    f1ofo
    cA
    cB
    @12
    foima
    syl
    uneq1d
    breq2d
    bibi1d
    3ad2ant2
    mpbid
    3exp
    exlimdv
    syl5
    imp31
end
