include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfn.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "isfi.mm"
include "ensym.mm"
include "csuc.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "albidv.mm"
include "weq.mm"
include "en0.mm"
include "sylib.mm"
include "anim1i.mm"
include "ancoms.mm"
include "adantll.mm"
include "wn.mm"
include "df-ne.mm"
include "pm3.24.mm"
include "pm2.21i.mm"
include "sylan2b.mm"
include "syl.mm"
include "ax-gen.mm"
include "a1i.mm"
include "nfv.mm"
include "nfa1.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "cima.mm"
include "cfv.mm"
include "ssel.mm"
include "wf.mm"
include "f1of.mm"
include "vex.mm"
include "sucid.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "impel.mm"
include "adantr.mm"
include "crn.mm"
include "imassrn.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "dff1o2.mm"
include "simp3bi.mm"
include "syl5sseq.mm"
include "sstr2.mm"
include "anim1d.mm"
include "wf1.mm"
include "cvv.mm"
include "f1of1.mm"
include "sssucid.mm"
include "f1imaen2g.mm"
include "mpanr12.mm"
include "ensymd.mm"
include "jctird.mm"
include "imaex.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "breq2.mm"
include "inteq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylan9.mm"
include "ineq1.mm"
include "ineq2.mm"
include "rspc2v.mm"
include "ex.mm"
include "syl6.mm"
include "com4r.mm"
include "exp5c.mm"
include "com14.mm"
include "imp43.mm"
include "syl5bir.mm"
include "int0.mm"
include "syl6eq.mm"
include "ineq1d.mm"
include "ssv.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "biimprd.mm"
include "pm2.61d2.mm"
include "mpd.mm"
include "wb.mm"
include "csn.mm"
include "cun.mm"
include "fvex.mm"
include "intunsn.mm"
include "f1ofn.mm"
include "fnsnfv.mm"
include "uneq2d.mm"
include "df-suc.mm"
include "imaeq2i.mm"
include "imaundi.mm"
include "eqtr2i.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "eqtrd.mm"
include "inteqd.mm"
include "syl5eqr.mm"
include "ad2antlr.mm"
include "mpbid.mm"
include "exp43.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "adantlr.mm"
include "com13.mm"
include "alrimd.mm"
include "finds2.mm"
include "sp.mm"
include "exp4a.mm"
include "com24.mm"
include "syl5.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "impd.mm"
include "alrimiv.mm"
include "cpr.mm"
include "zfpair2.mm"
include "eleq1.mm"
include "prss.mm"
include "prnz.mm"
include "biantru.mm"
include "prfi.mm"
include "3bitrri.mm"
include "intpr.mm"
include "eleq1i.mm"
include "3imtr3g.mm"
include "ralrimivv.mm"
include "impbii.mm"
include "cbvral2v.mm"
include "df-3an.mm"
include "imbi1i.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem fiint
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint f y
  disjoint w z
  disjoint v z
  disjoint f z
  disjoint A z
  disjoint v w
  disjoint f w
  disjoint A w
  disjoint f v
  disjoint A v
  disjoint A f
  assert |- ( A. x e. A A. y e. A ( x i^i y ) e. A <-> A. x ( ( x C_ A /\ x =/= (/) /\ x e. Fin ) -> |^| x e. A ) )

  proof
    vz
    cv
    #
    vw
    cv
    #
    cin
    #
    cA
    wcel
    #
    vw
    cA
    wral
    vz
    cA
    wral
    #
    vx
    cv
    #
    cA
    wss
    #
    @5
    c0
    wne
    #
    wa
    #
    @5
    cfn
    wcel
    #
    wa
    #
    @5
    cint
    #
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    @5
    vy
    cv
    #
    cin
    #
    cA
    wcel
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @6
    @7
    @9
    w3a
    #
    @12
    wi
    #
    vx
    wal
    @4
    @14
    @4
    @13
    vx
    @4
    @8
    @9
    @12
    @9
    @8
    @4
    @12
    @9
    @5
    @15
    cen
    wbr
    #
    vy
    com
    wrex
    @8
    @4
    @12
    wi
    #
    wi
    #
    vy
    @5
    isfi
    @20
    @22
    vy
    com
    @20
    @15
    @5
    cen
    wbr
    #
    @15
    com
    wcel
    #
    @22
    @5
    @15
    ensym
    @24
    @4
    @8
    @23
    @12
    @24
    @4
    @8
    @23
    @12
    @24
    @4
    @8
    @23
    wa
    #
    @12
    wi
    #
    vx
    wal
    #
    @26
    @27
    @8
    c0
    @5
    cen
    wbr
    #
    wa
    #
    @12
    wi
    #
    vx
    wal
    #
    @8
    vv
    cv
    #
    @5
    cen
    wbr
    #
    wa
    #
    @12
    wi
    #
    vx
    wal
    #
    @8
    @32
    csuc
    #
    @5
    cen
    wbr
    #
    wa
    #
    @12
    wi
    #
    vx
    wal
    #
    @4
    vy
    vv
    @15
    c0
    wceq
    #
    @26
    @30
    vx
    @42
    @25
    @29
    @12
    @42
    @23
    @28
    @8
    @15
    c0
    @5
    cen
    breq1
    anbi2d
    imbi1d
    albidv
    vy
    vv
    weq
    #
    @26
    @35
    vx
    @43
    @25
    @34
    @12
    @43
    @23
    @33
    @8
    @15
    @32
    @5
    cen
    breq1
    anbi2d
    imbi1d
    albidv
    @15
    @37
    wceq
    #
    @26
    @40
    vx
    @44
    @25
    @39
    @12
    @44
    @23
    @38
    @8
    @15
    @37
    @5
    cen
    breq1
    anbi2d
    imbi1d
    albidv
    @31
    @4
    @30
    vx
    @29
    @5
    c0
    wceq
    #
    @7
    wa
    #
    @12
    @7
    @28
    @46
    @6
    @28
    @7
    @46
    @28
    @45
    @7
    @28
    @5
    c0
    cen
    wbr
    @45
    c0
    @5
    ensym
    @5
    en0
    sylib
    anim1i
    ancoms
    adantll
    @7
    @45
    @45
    wn
    #
    @12
    @5
    c0
    df-ne
    @45
    @47
    wa
    @12
    @45
    pm3.24
    pm2.21i
    sylan2b
    syl
    ax-gen
    a1i
    @4
    @36
    @41
    wi
    wi
    @32
    com
    wcel
    @4
    @36
    @40
    vx
    @4
    vx
    nfv
    @35
    vx
    nfa1
    @39
    @36
    @4
    @12
    @6
    @38
    @36
    @21
    wi
    #
    @7
    @6
    @38
    @48
    @38
    @37
    @5
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @6
    @48
    @37
    @5
    vf
    bren
    @6
    @50
    @48
    vf
    @6
    @50
    @36
    @4
    @12
    @6
    @50
    wa
    #
    @36
    @4
    wa
    #
    wa
    #
    @49
    @32
    cima
    #
    cint
    #
    @32
    @49
    cfv
    #
    cin
    #
    cA
    wcel
    #
    @12
    @53
    @56
    cA
    wcel
    #
    @58
    @51
    @59
    @52
    @6
    @56
    @5
    wcel
    #
    @59
    @50
    @5
    cA
    @56
    ssel
    @50
    @37
    @5
    @49
    wf
    @32
    @37
    wcel
    #
    @60
    @37
    @5
    @49
    f1of
    @32
    vv
    vex
    #
    sucid
    #
    @37
    @5
    @32
    @49
    ffvelrn
    sylancl
    impel
    adantr
    @53
    @54
    c0
    wceq
    #
    @59
    @58
    wi
    #
    @64
    wn
    @54
    c0
    wne
    #
    @53
    @65
    @54
    c0
    df-ne
    @6
    @50
    @36
    @4
    @66
    @65
    wi
    #
    @4
    @50
    @36
    @6
    @67
    @4
    @50
    @36
    @6
    @66
    @65
    @50
    @36
    wa
    #
    @6
    @66
    wa
    #
    @59
    @4
    @58
    @68
    @69
    @55
    cA
    wcel
    #
    @59
    @4
    @58
    wi
    #
    wi
    @50
    @69
    @54
    cA
    wss
    #
    @66
    wa
    #
    @32
    @54
    cen
    wbr
    #
    wa
    #
    @36
    @70
    @50
    @69
    @73
    @74
    @50
    @6
    @72
    @66
    @50
    @54
    @5
    wss
    @6
    @72
    wi
    @50
    @49
    crn
    #
    @54
    @5
    @49
    @32
    imassrn
    @50
    @49
    @37
    wfn
    #
    @49
    ccnv
    wfun
    @76
    @5
    wceq
    @37
    @5
    @49
    dff1o2
    simp3bi
    syl5sseq
    @54
    @5
    cA
    sstr2
    syl
    anim1d
    @50
    @54
    @32
    @50
    @37
    @5
    @49
    wf1
    #
    @5
    cvv
    wcel
    #
    @54
    @32
    cen
    wbr
    #
    @37
    @5
    @49
    f1of1
    vx
    vex
    @78
    @79
    wa
    @32
    @37
    wss
    @32
    cvv
    wcel
    @80
    @32
    sssucid
    @62
    @37
    @5
    @32
    @49
    cvv
    f1imaen2g
    mpanr12
    sylancl
    ensymd
    jctird
    @35
    @75
    @70
    wi
    vx
    @54
    @49
    @32
    vf
    vex
    imaex
    @5
    @54
    wceq
    #
    @34
    @75
    @12
    @70
    @81
    @8
    @73
    @33
    @74
    @81
    @6
    @72
    @7
    @66
    @5
    @54
    cA
    sseq1
    @5
    @54
    c0
    neeq1
    anbi12d
    @5
    @54
    @32
    cen
    breq2
    anbi12d
    @81
    @11
    @55
    cA
    @5
    @54
    inteq
    eleq1d
    imbi12d
    spcv
    sylan9
    @70
    @59
    @71
    @3
    @58
    @55
    @1
    cin
    #
    cA
    wcel
    vz
    vw
    @55
    @56
    cA
    cA
    @0
    @55
    wceq
    @2
    @82
    cA
    @0
    @55
    @1
    ineq1
    eleq1d
    @1
    @56
    wceq
    @82
    @57
    cA
    @1
    @56
    @55
    ineq2
    eleq1d
    rspc2v
    ex
    syl6
    com4r
    exp5c
    com14
    imp43
    syl5bir
    @64
    @58
    @59
    @64
    @57
    @56
    cA
    @64
    @57
    cvv
    @56
    cin
    #
    @56
    @64
    @55
    cvv
    @56
    @64
    @55
    c0
    cint
    cvv
    @54
    c0
    inteq
    int0
    syl6eq
    ineq1d
    @56
    cvv
    wss
    @83
    @56
    wceq
    @56
    ssv
    @56
    cvv
    sseqin2
    mpbi
    syl6eq
    eleq1d
    biimprd
    pm2.61d2
    mpd
    @50
    @58
    @12
    wb
    @6
    @52
    @50
    @57
    @11
    cA
    @50
    @57
    @54
    @56
    csn
    #
    cun
    #
    cint
    @11
    @54
    @56
    @32
    @49
    fvex
    intunsn
    @50
    @85
    @5
    @50
    @85
    @49
    @37
    cima
    #
    @5
    @50
    @85
    @54
    @49
    @32
    csn
    #
    cima
    #
    cun
    #
    @86
    @50
    @84
    @88
    @54
    @50
    @77
    @61
    @84
    @88
    wceq
    @37
    @5
    @49
    f1ofn
    @63
    @37
    @32
    @49
    fnsnfv
    sylancl
    uneq2d
    @86
    @49
    @32
    @87
    cun
    #
    cima
    @89
    @37
    @90
    @49
    @32
    df-suc
    imaeq2i
    @49
    @32
    @87
    imaundi
    eqtr2i
    syl6eq
    @50
    @37
    @5
    @49
    wfo
    @86
    @5
    wceq
    @37
    @5
    @49
    f1ofo
    @37
    @5
    @49
    foima
    syl
    eqtrd
    inteqd
    syl5eqr
    eleq1d
    ad2antlr
    mpbid
    exp43
    exlimdv
    syl5bi
    imp
    adantlr
    com13
    alrimd
    a1i
    finds2
    @26
    vx
    sp
    syl6
    exp4a
    com24
    syl5
    rexlimiv
    sylbi
    com13
    impd
    alrimiv
    @14
    @3
    vz
    vw
    cA
    cA
    @14
    @0
    @1
    cpr
    #
    cA
    wss
    #
    @91
    c0
    wne
    #
    wa
    #
    @91
    cfn
    wcel
    #
    wa
    #
    @91
    cint
    #
    cA
    wcel
    #
    @0
    cA
    wcel
    @1
    cA
    wcel
    wa
    #
    @3
    @13
    @96
    @98
    wi
    vx
    @91
    vz
    vw
    zfpair2
    @5
    @91
    wceq
    #
    @10
    @96
    @12
    @98
    @100
    @8
    @94
    @9
    @95
    @100
    @6
    @92
    @7
    @93
    @5
    @91
    cA
    sseq1
    @5
    @91
    c0
    neeq1
    anbi12d
    @5
    @91
    cfn
    eleq1
    anbi12d
    @100
    @11
    @97
    cA
    @5
    @91
    inteq
    eleq1d
    imbi12d
    spcv
    @99
    @92
    @94
    @96
    @0
    @1
    cA
    vz
    vex
    #
    vw
    vex
    #
    prss
    @93
    @92
    @0
    @1
    @101
    prnz
    biantru
    @95
    @94
    @0
    @1
    prfi
    biantru
    3bitrri
    @97
    @2
    cA
    @0
    @1
    @101
    @102
    intpr
    eleq1i
    3imtr3g
    ralrimivv
    impbii
    @17
    @3
    @0
    @15
    cin
    #
    cA
    wcel
    vx
    vy
    vz
    vw
    cA
    cA
    vx
    vz
    weq
    @16
    @103
    cA
    @5
    @0
    @15
    ineq1
    eleq1d
    vy
    vw
    weq
    @103
    @2
    cA
    @15
    @1
    @0
    ineq2
    eleq1d
    cbvral2v
    @19
    @13
    vx
    @18
    @10
    @12
    @6
    @7
    @9
    df-3an
    imbi1i
    albii
    3bitr4i
end
