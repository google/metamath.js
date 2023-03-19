include "com.mm"
include "wcel.mm"
include "wpss.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "wss.mm"
include "pssss.mm"
include "ssexg.mm"
include "sylan.mm"
include "ancoms.mm"
include "wi.mm"
include "wal.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "psseq2.mm"
include "rexeq.mm"
include "imbi12d.mm"
include "albidv.mm"
include "weq.mm"
include "npss0.mm"
include "pm2.21i.mm"
include "ax-gen.mm"
include "nfv.mm"
include "nfa1.mm"
include "wel.mm"
include "wn.mm"
include "elequ1.mm"
include "biimpcd.mm"
include "con3d.mm"
include "adantl.mm"
include "sseld.mm"
include "elsuci.mm"
include "ord.mm"
include "con1d.mm"
include "syl6.mm"
include "imp.mm"
include "syld.mm"
include "impancom.mm"
include "ssrdv.mm"
include "anim1i.mm"
include "dfpss2.mm"
include "sylibr.mm"
include "elelsuc.mm"
include "reximi2.mm"
include "imim12i.mm"
include "exp4c.mm"
include "sps.mm"
include "com4t.mm"
include "csn.mm"
include "cdif.mm"
include "anidm.mm"
include "ssdif.mm"
include "word.mm"
include "nnord.mm"
include "orddif.mm"
include "syl.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "syl5.mm"
include "wex.mm"
include "pssnel.mm"
include "eleq2.mm"
include "eldifi.mm"
include "syl6bir.mm"
include "eleq1a.mm"
include "sylan9r.mm"
include "adantr.mm"
include "pm2.61d.mm"
include "ex.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "im2anan9r.mm"
include "syl5bir.mm"
include "syl6ibr.mm"
include "psseq1.mm"
include "breq1.mm"
include "rexbidv.mm"
include "cbvalv.mm"
include "vex.mm"
include "difss.mm"
include "ssexi.mm"
include "spcv.mm"
include "sylbi.mm"
include "sylan9.mm"
include "ordsucelsuc.mm"
include "biimpd.mm"
include "adantrd.mm"
include "elnn.mm"
include "cun.mm"
include "cin.mm"
include "cop.mm"
include "wf1o.mm"
include "snex.mm"
include "f1osn.mm"
include "f1oen3g.mm"
include "mp2an.mm"
include "jctr.mm"
include "orddisj.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtr3i.mm"
include "jctil.mm"
include "unen.mm"
include "syl2an.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "df-suc.mm"
include "a1i.mm"
include "breq12d.mm"
include "sylan2i.mm"
include "exp4d.mm"
include "com24.mm"
include "imp4b.mm"
include "jcad.mm"
include "breq2.mm"
include "rspcev.mm"
include "df-rex.mm"
include "cbvrexv.mm"
include "3imtr4g.mm"
include "expl.mm"
include "eqelsuc.mm"
include "enref.mm"
include "sylancl.mm"
include "2a1d.mm"
include "pm2.61ii.mm"
include "alrimd.mm"
include "finds.mm"
include "spcgv.mm"
include "com3l.mm"
include "mpd.mm"

theorem pssnn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( ( A e. _om /\ B C. A ) -> E. x e. A B ~~ x )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wpss
    #
    wa
    cB
    cvv
    wcel
    #
    cB
    vx
    cv
    #
    cen
    wbr
    #
    vx
    cA
    wrex
    #
    @1
    @0
    @2
    @1
    cB
    cA
    wss
    @0
    @2
    cB
    cA
    pssss
    cB
    cA
    com
    ssexg
    sylan
    ancoms
    @0
    @1
    @2
    @5
    wi
    @2
    @0
    @1
    @5
    @0
    vw
    cv
    #
    cA
    wpss
    #
    @6
    @3
    cen
    wbr
    #
    vx
    cA
    wrex
    #
    wi
    #
    vw
    wal
    #
    @2
    @1
    @5
    wi
    #
    @6
    vz
    cv
    #
    wpss
    #
    @8
    vx
    @13
    wrex
    #
    wi
    #
    vw
    wal
    @6
    c0
    wpss
    #
    @8
    vx
    c0
    wrex
    #
    wi
    #
    vw
    wal
    @6
    vy
    cv
    #
    wpss
    #
    @8
    vx
    @20
    wrex
    #
    wi
    #
    vw
    wal
    #
    @6
    @20
    csuc
    #
    wpss
    #
    @8
    vx
    @25
    wrex
    #
    wi
    #
    vw
    wal
    @11
    vz
    vy
    cA
    @13
    c0
    wceq
    #
    @16
    @19
    vw
    @29
    @14
    @17
    @15
    @18
    @13
    c0
    @6
    psseq2
    @8
    vx
    @13
    c0
    rexeq
    imbi12d
    albidv
    vz
    vy
    weq
    #
    @16
    @23
    vw
    @30
    @14
    @21
    @15
    @22
    @13
    @20
    @6
    psseq2
    @8
    vx
    @13
    @20
    rexeq
    imbi12d
    albidv
    @13
    @25
    wceq
    #
    @16
    @28
    vw
    @31
    @14
    @26
    @15
    @27
    @13
    @25
    @6
    psseq2
    @8
    vx
    @13
    @25
    rexeq
    imbi12d
    albidv
    @13
    cA
    wceq
    #
    @16
    @10
    vw
    @32
    @14
    @7
    @15
    @9
    @13
    cA
    @6
    psseq2
    @8
    vx
    @13
    cA
    rexeq
    imbi12d
    albidv
    @19
    vw
    @17
    @18
    @6
    npss0
    pm2.21i
    ax-gen
    @20
    com
    wcel
    #
    @24
    @28
    vw
    @33
    vw
    nfv
    @23
    vw
    nfa1
    @33
    @24
    @28
    vy
    vw
    wel
    #
    vw
    vy
    weq
    #
    @33
    @24
    wa
    #
    @28
    wi
    @36
    @26
    @34
    wn
    #
    @35
    wn
    #
    @27
    @24
    @26
    @37
    @38
    @27
    wi
    wi
    wi
    #
    @33
    @23
    @39
    vw
    @23
    @26
    @37
    @38
    @27
    @26
    @37
    wa
    #
    @38
    wa
    #
    @21
    @22
    @27
    @41
    @6
    @20
    wss
    #
    @38
    wa
    @21
    @40
    @42
    @38
    @40
    vz
    @6
    @20
    @26
    vz
    vw
    wel
    #
    @37
    vz
    vy
    wel
    #
    @26
    @43
    wa
    @37
    @30
    wn
    #
    @44
    @43
    @37
    @45
    wi
    @26
    @43
    @30
    @34
    @30
    @43
    @34
    vz
    vy
    vw
    elequ1
    biimpcd
    con3d
    adantl
    @26
    @43
    @45
    @44
    wi
    #
    @26
    @43
    @13
    @25
    wcel
    #
    @46
    @26
    @6
    @25
    @13
    @6
    @25
    pssss
    #
    sseld
    @47
    @44
    @30
    @47
    @44
    @30
    @13
    @20
    elsuci
    ord
    #
    con1d
    syl6
    imp
    syld
    impancom
    ssrdv
    anim1i
    @6
    @20
    dfpss2
    sylibr
    @8
    @8
    vx
    @20
    @25
    vx
    vy
    wel
    #
    @3
    @25
    wcel
    @8
    @3
    @20
    elelsuc
    anim1i
    reximi2
    imim12i
    exp4c
    sps
    adantl
    com4t
    @34
    @33
    @24
    @28
    @34
    @33
    wa
    #
    @24
    wa
    @26
    @6
    @20
    csn
    #
    cdif
    #
    @3
    cen
    wbr
    #
    vx
    @20
    wrex
    #
    @27
    @51
    @26
    @53
    @20
    wpss
    #
    @24
    @55
    @51
    @26
    @53
    @20
    wss
    #
    @53
    @20
    wceq
    #
    wn
    #
    wa
    #
    @56
    @26
    @26
    @26
    wa
    @51
    @60
    @26
    anidm
    @33
    @26
    @57
    @34
    @26
    @59
    @26
    @6
    @25
    wss
    #
    @33
    @57
    @48
    @61
    @57
    @33
    @53
    @25
    @52
    cdif
    #
    wss
    @6
    @25
    @52
    ssdif
    @33
    @20
    @62
    @53
    @33
    @20
    word
    #
    @20
    @62
    wceq
    @20
    nnord
    #
    @20
    orddif
    syl
    sseq2d
    syl5ibr
    syl5
    @26
    @47
    @43
    wn
    #
    wa
    #
    vz
    wex
    @34
    @59
    vz
    @6
    @25
    pssnel
    @34
    @66
    @59
    vz
    @34
    @47
    @65
    @59
    @34
    @47
    wa
    #
    @58
    @43
    @67
    @58
    @43
    @67
    @58
    wa
    @44
    @43
    @58
    @44
    @43
    wi
    @67
    @58
    @44
    @13
    @53
    wcel
    @43
    @53
    @20
    @13
    eleq2
    @13
    @6
    @52
    eldifi
    syl6bir
    adantl
    @67
    @44
    wn
    #
    @43
    wi
    @58
    @47
    @68
    @30
    @34
    @43
    @49
    @20
    @6
    @13
    eleq1a
    sylan9r
    adantr
    pm2.61d
    ex
    con3d
    expimpd
    exlimdv
    syl5
    im2anan9r
    syl5bir
    @53
    @20
    dfpss2
    syl6ibr
    @24
    @13
    @20
    wpss
    #
    @13
    @3
    cen
    wbr
    #
    vx
    @20
    wrex
    #
    wi
    #
    vz
    wal
    @56
    @55
    wi
    #
    @23
    @72
    vw
    vz
    vw
    vz
    weq
    #
    @21
    @69
    @22
    @71
    @6
    @13
    @20
    psseq1
    @74
    @8
    @70
    vx
    @20
    @6
    @13
    @3
    cen
    breq1
    rexbidv
    imbi12d
    cbvalv
    @72
    @73
    vz
    @53
    @53
    @6
    vw
    vex
    #
    @6
    @52
    difss
    ssexi
    @13
    @53
    wceq
    #
    @69
    @56
    @71
    @55
    @13
    @53
    @20
    psseq1
    @76
    @70
    @54
    vx
    @20
    @13
    @53
    @3
    cen
    breq1
    rexbidv
    imbi12d
    spcv
    sylbi
    sylan9
    @51
    @55
    @27
    wi
    @24
    @51
    @50
    @54
    wa
    #
    vx
    wex
    @6
    @13
    cen
    wbr
    #
    vz
    @25
    wrex
    #
    @55
    @27
    @51
    @77
    @79
    vx
    @51
    @77
    @3
    csuc
    #
    @25
    wcel
    #
    @6
    @80
    cen
    wbr
    #
    wa
    @79
    @51
    @77
    @81
    @82
    @51
    @50
    @81
    @54
    @33
    @50
    @81
    wi
    #
    @34
    @33
    @63
    @83
    @64
    @63
    @50
    @81
    @3
    @20
    ordsucelsuc
    biimpd
    syl
    adantl
    adantrd
    @34
    @33
    @50
    @54
    @82
    @34
    @54
    @50
    @33
    @82
    @34
    @54
    @50
    @33
    @82
    @50
    @33
    wa
    @34
    @54
    @3
    com
    wcel
    #
    @82
    @3
    @20
    elnn
    @54
    @84
    wa
    @82
    @34
    @53
    @52
    cun
    #
    @3
    @3
    csn
    #
    cun
    #
    cen
    wbr
    #
    @54
    @54
    @52
    @86
    cen
    wbr
    #
    wa
    @53
    @52
    cin
    #
    c0
    wceq
    #
    @3
    @86
    cin
    c0
    wceq
    #
    wa
    @88
    @84
    @54
    @89
    @20
    @3
    cop
    #
    csn
    #
    cvv
    wcel
    @52
    @86
    @94
    wf1o
    @89
    @93
    snex
    @20
    @3
    vy
    vex
    vx
    vex
    f1osn
    @52
    @86
    @94
    cvv
    f1oen3g
    mp2an
    jctr
    @84
    @92
    @91
    @84
    @3
    word
    @92
    @3
    nnord
    @3
    orddisj
    syl
    @52
    @53
    cin
    @90
    c0
    @52
    @53
    incom
    @52
    @6
    disjdif
    eqtr3i
    jctil
    @53
    @3
    @52
    @86
    unen
    syl2an
    @34
    @6
    @85
    @80
    @87
    cen
    @34
    @85
    @6
    @6
    @20
    difsnid
    eqcomd
    @80
    @87
    wceq
    @34
    @3
    df-suc
    a1i
    breq12d
    syl5ibr
    sylan2i
    exp4d
    com24
    imp4b
    jcad
    @78
    @82
    vz
    @80
    @25
    @13
    @80
    @6
    cen
    breq2
    rspcev
    syl6
    exlimdv
    @54
    vx
    @20
    df-rex
    @8
    @78
    vx
    vz
    @25
    @3
    @13
    @6
    cen
    breq2
    cbvrexv
    3imtr4g
    adantr
    syld
    expl
    @35
    @27
    @36
    @26
    @35
    @6
    @25
    wcel
    @6
    @6
    cen
    wbr
    #
    @27
    @6
    @20
    @75
    eqelsuc
    @6
    @75
    enref
    @8
    @95
    vx
    @6
    @25
    @3
    @6
    @6
    cen
    breq2
    rspcev
    sylancl
    2a1d
    pm2.61ii
    ex
    alrimd
    finds
    @10
    @12
    vw
    cB
    cvv
    @6
    cB
    wceq
    #
    @7
    @1
    @9
    @5
    @6
    cB
    cA
    psseq1
    @96
    @8
    @4
    vx
    cA
    @6
    cB
    @3
    cen
    breq1
    rexbidv
    imbi12d
    spcgv
    syl5
    com3l
    imp
    mpd
end
