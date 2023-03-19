include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wral.mm"
include "ralcom.mm"
include "cdm.mm"
include "cres.mm"
include "wn.mm"
include "wb.mm"
include "simplll.mm"
include "simpllr.mm"
include "simprl.mm"
include "sselda.mm"
include "nosupbnd2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "cun.mm"
include "word.mm"
include "simpl.mm"
include "ssel2.mm"
include "syl2an.mm"
include "nodmord.mm"
include "ordirr.mm"
include "3syl.mm"
include "ssun2.mm"
include "cfv.mm"
include "bdayval.mm"
include "syl.mm"
include "wfn.mm"
include "con0.mm"
include "wfo.mm"
include "bdayfo.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fnfvima.mm"
include "mp3an1.mm"
include "eqeltrrd.mm"
include "elssuni.mm"
include "nodmon.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "sseqtri.mm"
include "ssorduni.mm"
include "ordsssuc.mm"
include "mpan2.mm"
include "mpbid.mm"
include "sseldi.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "cdif.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "dmeqi.mm"
include "dmun.mm"
include "eqtri.mm"
include "c0.mm"
include "wne.mm"
include "1on.mm"
include "elexi.mm"
include "snnz.mm"
include "dmxp.mm"
include "uneq2i.mm"
include "undif2.mm"
include "3eqtri.mm"
include "dmeq.mm"
include "syl5eqr.mm"
include "nsyl.mm"
include "df-ne.mm"
include "crab.mm"
include "cint.mm"
include "wo.mm"
include "notnotr.mm"
include "wrex.mm"
include "simpr.mm"
include "fvresd.mm"
include "reseq1i.mm"
include "resundir.mm"
include "cin.mm"
include "df-res.mm"
include "incom.mm"
include "disjdif.mm"
include "xpdisj1.mm"
include "un0.mm"
include "wfun.mm"
include "wrel.mm"
include "nosupno.mm"
include "adantr.mm"
include "nofun.mm"
include "funrel.mm"
include "resdm.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simplrr.mm"
include "noetalem1.mm"
include "simplr.mm"
include "nosepne.mm"
include "eqnetrrd.mm"
include "neeqtrrd.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "necom.mm"
include "3bitr3g.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexeq.mm"
include "syl5ibrcom.mm"
include "rexnal.mm"
include "syl6ib.mm"
include "syl5.mm"
include "orrd.mm"
include "funres.mm"
include "eqfunfv.mm"
include "ianor.mm"
include "con1bii.mm"
include "syl6bbr.mm"
include "con2bid.mm"
include "pm2.21d.mm"
include "breq1d.mm"
include "wi.mm"
include "sltres.mm"
include "sylbird.mm"
include "noreson.mm"
include "wor.mm"
include "sltso.mm"
include "sotric.mm"
include "mpan.mm"
include "mpbird.mm"
include "mpjaod.mm"
include "fveq1i.mm"
include "funfn.mm"
include "sylib.mm"
include "wf.mm"
include "fconst.mm"
include "ffn.mm"
include "a1i.mm"
include "rabbii.mm"
include "inteqi.mm"
include "necomd.mm"
include "nosepssdm.mm"
include "syl5eqss.mm"
include "simplrl.mm"
include "nosepon.mm"
include "eloni.mm"
include "ordsuc.mm"
include "mpbi.mm"
include "ordtr2.mm"
include "mp2and.mm"
include "ontri1.mm"
include "eldifd.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "fvconst2.mm"
include "eqtrd.mm"
include "nosep1o.mm"
include "syl31anc.mm"
include "ordtri2or.mm"
include "mpjaodan.mm"
include "ex.mm"
include "syl5bir.mm"
include "mpd.mm"
include "expr.mm"
include "sylbid.mm"
include "ralimdva.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem noetalem3
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vq: setvar q
  assume noetalem.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )
  assume noetalem.2: |- Z = ( S u. ( ( suc U. ( bday " B ) \ dom S ) X. { 1o } ) )

  disjoint A a
  disjoint a b
  disjoint A b
  disjoint a g
  disjoint A g
  disjoint a u
  disjoint A u
  disjoint a v
  disjoint A v
  disjoint a x
  disjoint A x
  disjoint a y
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint b g
  disjoint b x
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint S a
  disjoint S g
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint S q
  disjoint Z p
  disjoint Z q
  assert |- ( ( ( A C_ No /\ A e. _V ) /\ ( B C_ No /\ B e. _V ) /\ A. a e. A A. b e. B a <s b ) -> A. b e. B Z <s b )

  proof
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cB
    csur
    wss
    #
    cB
    cvv
    wcel
    #
    wa
    #
    va
    cv
    vb
    cv
    #
    cslt
    wbr
    #
    vb
    cB
    wral
    va
    cA
    wral
    #
    cZ
    @6
    cslt
    wbr
    #
    vb
    cB
    wral
    #
    @8
    @7
    va
    cA
    wral
    #
    vb
    cB
    wral
    @2
    @5
    wa
    #
    @10
    @7
    va
    vb
    cA
    cB
    ralcom
    @12
    @11
    @9
    vb
    cB
    @12
    @6
    cB
    wcel
    #
    wa
    #
    @11
    @6
    cS
    cdm
    #
    cres
    #
    cS
    cslt
    wbr
    #
    wn
    #
    @9
    @14
    @0
    @1
    @6
    csur
    wcel
    #
    @11
    @18
    wb
    @0
    @1
    @5
    @13
    simplll
    @0
    @1
    @5
    @13
    simpllr
    @12
    cB
    csur
    @6
    @2
    @3
    @4
    simprl
    #
    sselda
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    @6
    va
    noetalem.1
    nosupbnd2
    syl3anc
    @12
    @13
    @18
    @9
    @12
    @13
    @18
    wa
    #
    wa
    #
    cZ
    @6
    wceq
    #
    wn
    #
    @9
    @22
    @15
    cbday
    cB
    cima
    #
    cuni
    #
    csuc
    #
    cun
    #
    @6
    cdm
    #
    wceq
    #
    @23
    @22
    @30
    @29
    @29
    wcel
    #
    @22
    @19
    @29
    word
    @31
    wn
    @12
    @3
    @13
    @19
    @21
    @20
    @13
    @18
    simpl
    #
    cB
    csur
    @6
    ssel2
    syl2an
    #
    @6
    nodmord
    @29
    ordirr
    3syl
    @22
    @29
    @28
    wcel
    @30
    @31
    @22
    @27
    @28
    @29
    @27
    @15
    ssun2
    @22
    @29
    @26
    wss
    #
    @29
    @27
    wcel
    #
    @22
    @29
    @25
    wcel
    #
    @34
    @22
    @6
    cbday
    cfv
    #
    @29
    @25
    @22
    @19
    @37
    @29
    wceq
    #
    @33
    @6
    bdayval
    #
    syl
    @12
    @3
    @13
    @37
    @25
    wcel
    #
    @21
    @20
    @32
    cbday
    csur
    wfn
    #
    @3
    @13
    @40
    csur
    con0
    cbday
    wfo
    #
    @41
    bdayfo
    csur
    con0
    cbday
    fofn
    ax-mp
    csur
    cB
    cbday
    @6
    fnfvima
    mp3an1
    #
    syl2an
    eqeltrrd
    @29
    @25
    elssuni
    #
    syl
    @22
    @19
    @29
    con0
    wcel
    #
    @34
    @35
    wb
    #
    @33
    @6
    nodmon
    #
    @45
    @26
    word
    #
    @46
    @25
    con0
    wss
    @48
    @25
    cbday
    crn
    #
    con0
    cbday
    cB
    imassrn
    @42
    @49
    con0
    wceq
    bdayfo
    csur
    con0
    cbday
    forn
    ax-mp
    sseqtri
    @25
    ssorduni
    ax-mp
    #
    @29
    @26
    ordsssuc
    mpan2
    #
    3syl
    mpbid
    sseldi
    @28
    @29
    @29
    eleq2
    syl5ibcom
    mtod
    @23
    @28
    cZ
    cdm
    #
    @29
    @52
    @15
    @27
    @15
    cdif
    #
    c1o
    csn
    #
    cxp
    #
    cdm
    #
    cun
    #
    @15
    @53
    cun
    @28
    @52
    cS
    @55
    cun
    #
    cdm
    @57
    cZ
    @58
    noetalem.2
    dmeqi
    cS
    @55
    dmun
    eqtri
    @56
    @53
    @15
    @54
    c0
    wne
    @56
    @53
    wceq
    c1o
    c1o
    con0
    1on
    elexi
    #
    snnz
    @53
    @54
    dmxp
    ax-mp
    uneq2i
    @15
    @27
    undif2
    3eqtri
    cZ
    @6
    dmeq
    syl5eqr
    nsyl
    @24
    cZ
    @6
    wne
    #
    @22
    @9
    cZ
    @6
    df-ne
    @22
    @60
    @9
    @22
    @60
    wa
    #
    vp
    cv
    #
    cZ
    cfv
    #
    @62
    @6
    cfv
    #
    wne
    #
    vp
    con0
    crab
    #
    cint
    #
    @15
    wcel
    #
    @9
    @15
    @67
    wss
    #
    @61
    @68
    wa
    #
    @16
    cS
    wceq
    #
    @9
    cS
    @16
    cslt
    wbr
    #
    @70
    @71
    @9
    @70
    @16
    cdm
    #
    @15
    wceq
    #
    wn
    #
    vq
    cv
    #
    @16
    cfv
    #
    @76
    cS
    cfv
    #
    wceq
    #
    vq
    @73
    wral
    #
    wn
    #
    wo
    #
    @71
    wn
    @70
    @75
    @81
    @75
    wn
    @74
    @70
    @81
    @74
    notnotr
    @70
    @74
    @79
    wn
    #
    vq
    @73
    wrex
    #
    @81
    @70
    @84
    @74
    @83
    vq
    @15
    wrex
    #
    @70
    @68
    @67
    cS
    cfv
    #
    @67
    @16
    cfv
    #
    wne
    #
    @85
    @61
    @68
    simpr
    #
    @70
    @86
    @67
    @6
    cfv
    #
    @87
    @70
    @67
    cZ
    cfv
    #
    @86
    @90
    @70
    @67
    cZ
    @15
    cres
    #
    cfv
    @91
    @86
    @70
    @67
    @15
    cZ
    @89
    fvresd
    @70
    @67
    @92
    cS
    @70
    @92
    cS
    @15
    cres
    #
    cS
    @92
    @58
    @15
    cres
    @93
    @55
    @15
    cres
    #
    cun
    #
    @93
    cZ
    @58
    @15
    noetalem.2
    reseq1i
    cS
    @55
    @15
    resundir
    @95
    @93
    c0
    cun
    @93
    @94
    c0
    @93
    @94
    @55
    @15
    cvv
    cxp
    cin
    #
    c0
    @55
    @15
    df-res
    @53
    @15
    cin
    #
    c0
    wceq
    @96
    c0
    wceq
    @97
    @15
    @53
    cin
    #
    c0
    @53
    @15
    incom
    @15
    @27
    disjdif
    #
    eqtri
    @53
    @15
    @54
    cvv
    xpdisj1
    ax-mp
    eqtri
    uneq2i
    @93
    un0
    eqtri
    3eqtri
    @70
    cS
    wfun
    #
    cS
    wrel
    @93
    cS
    wceq
    @70
    cS
    csur
    wcel
    #
    @100
    @61
    @101
    @68
    @61
    @2
    @101
    @2
    @5
    @21
    @60
    simplll
    #
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    noetalem.1
    nosupno
    #
    syl
    adantr
    #
    cS
    nofun
    #
    syl
    #
    cS
    funrel
    cS
    resdm
    3syl
    syl5eq
    #
    fveq1d
    eqtr3d
    @70
    cZ
    csur
    wcel
    #
    @19
    @60
    @91
    @90
    wne
    @61
    @108
    @68
    @61
    @0
    @1
    @4
    @108
    @0
    @1
    @5
    @21
    @60
    simp-4l
    @0
    @1
    @5
    @21
    @60
    simp-4r
    @22
    @4
    @60
    @2
    @3
    @4
    @21
    simplrr
    adantr
    vx
    vy
    vv
    vu
    cA
    cB
    cS
    vg
    cZ
    noetalem.1
    noetalem.2
    noetalem1
    syl3anc
    #
    adantr
    #
    @61
    @19
    @68
    @22
    @19
    @60
    @33
    adantr
    #
    adantr
    #
    @22
    @60
    @68
    simplr
    vp
    cZ
    @6
    nosepne
    syl3anc
    eqnetrrd
    @70
    @67
    @15
    @6
    @89
    fvresd
    neeqtrrd
    @83
    @88
    vq
    @67
    @15
    @76
    @67
    wceq
    #
    @77
    @78
    wne
    @87
    @86
    wne
    @83
    @88
    @113
    @77
    @87
    @78
    @86
    @76
    @67
    @16
    fveq2
    @76
    @67
    cS
    fveq2
    neeq12d
    @77
    @78
    df-ne
    @87
    @86
    necom
    3bitr3g
    rspcev
    syl2anc
    @83
    vq
    @73
    @15
    rexeq
    syl5ibrcom
    @79
    vq
    @73
    rexnal
    syl6ib
    syl5
    orrd
    @70
    @71
    @82
    @70
    @71
    @74
    @80
    wa
    #
    @82
    wn
    @70
    @16
    wfun
    #
    @100
    @71
    @114
    wb
    @70
    @19
    @6
    wfun
    @115
    @112
    @6
    nofun
    @15
    @6
    funres
    3syl
    @106
    vq
    @16
    cS
    eqfunfv
    syl2anc
    @114
    @82
    @74
    @80
    ianor
    con1bii
    syl6bbr
    con2bid
    mpbid
    pm2.21d
    @70
    @72
    @92
    @16
    cslt
    wbr
    #
    @9
    @70
    @92
    cS
    @16
    cslt
    @107
    breq1d
    @70
    @108
    @19
    @15
    con0
    wcel
    #
    @116
    @9
    wi
    @110
    @112
    @70
    @101
    @117
    @104
    cS
    nodmon
    #
    syl
    #
    cZ
    @6
    @15
    sltres
    syl3anc
    sylbird
    @70
    @71
    @72
    wo
    #
    @18
    @61
    @18
    @68
    @12
    @13
    @18
    @60
    simplrr
    adantr
    @70
    @17
    @120
    @70
    @16
    csur
    wcel
    #
    @101
    @17
    @120
    wn
    wb
    #
    @70
    @19
    @117
    @121
    @112
    @119
    @6
    @15
    noreson
    syl2anc
    @104
    csur
    cslt
    wor
    @121
    @101
    wa
    @122
    sltso
    csur
    @16
    cS
    cslt
    sotric
    mpan
    syl2anc
    con2bid
    mpbird
    mpjaod
    @61
    @69
    wa
    #
    @108
    @19
    @60
    @91
    c1o
    wceq
    @9
    @61
    @108
    @69
    @109
    adantr
    #
    @61
    @19
    @69
    @111
    adantr
    #
    @22
    @60
    @69
    simplr
    #
    @123
    @91
    @67
    @55
    cfv
    #
    c1o
    @123
    @91
    @67
    @58
    cfv
    #
    @127
    @67
    cZ
    @58
    noetalem.2
    fveq1i
    @123
    cS
    @15
    wfn
    #
    @55
    @53
    wfn
    #
    @98
    c0
    wceq
    #
    @67
    @53
    wcel
    #
    @128
    @127
    wceq
    @123
    @100
    @129
    @123
    @2
    @101
    @100
    @2
    @5
    @21
    @60
    @69
    simp-4l
    #
    @103
    @105
    3syl
    cS
    funfn
    sylib
    @130
    @123
    @53
    @54
    @55
    wf
    @130
    @53
    c1o
    @59
    fconst
    @53
    @54
    @55
    ffn
    ax-mp
    a1i
    @131
    @123
    @99
    a1i
    @123
    @67
    @27
    @15
    @123
    @67
    @29
    wss
    #
    @35
    @67
    @27
    wcel
    #
    @123
    @67
    @64
    @63
    wne
    #
    vp
    con0
    crab
    #
    cint
    #
    @29
    @66
    @137
    @65
    @136
    vp
    con0
    @63
    @64
    necom
    rabbii
    inteqi
    @123
    @19
    @108
    @6
    cZ
    wne
    @138
    @29
    wss
    @125
    @124
    @123
    cZ
    @6
    @126
    necomd
    vp
    @6
    cZ
    nosepssdm
    syl3anc
    syl5eqss
    @123
    @34
    @35
    @123
    @36
    @34
    @123
    @37
    @29
    @25
    @123
    @19
    @38
    @125
    @39
    syl
    @123
    @3
    @13
    @40
    @61
    @3
    @69
    @22
    @3
    @60
    @2
    @3
    @4
    @21
    simplrl
    adantr
    adantr
    @61
    @13
    @69
    @12
    @13
    @18
    @60
    simplrl
    adantr
    @43
    syl2anc
    eqeltrrd
    @44
    syl
    @123
    @19
    @45
    @46
    @125
    @47
    @51
    3syl
    mpbid
    @123
    @67
    con0
    wcel
    #
    @67
    word
    #
    @134
    @35
    wa
    @135
    wi
    #
    @123
    @108
    @19
    @60
    @139
    @124
    @125
    @126
    vp
    cZ
    @6
    nosepon
    #
    syl3anc
    #
    @67
    eloni
    #
    @140
    @27
    word
    #
    @141
    @48
    @145
    @50
    @26
    ordsuc
    mpbi
    @67
    @29
    @27
    ordtr2
    mpan2
    3syl
    mp2and
    @123
    @69
    @68
    wn
    #
    @61
    @69
    simpr
    @123
    @117
    @139
    @69
    @146
    wb
    @123
    @2
    @101
    @117
    @133
    @103
    @118
    3syl
    @143
    @15
    @67
    ontri1
    syl2anc
    mpbid
    eldifd
    #
    @15
    @53
    cS
    @55
    @67
    fvun2
    syl112anc
    syl5eq
    @123
    @132
    @127
    c1o
    wceq
    @147
    @53
    c1o
    @67
    @59
    fvconst2
    syl
    eqtrd
    vp
    cZ
    @6
    nosep1o
    syl31anc
    @61
    @140
    @15
    word
    #
    @68
    @69
    wo
    @61
    @139
    @140
    @61
    @108
    @19
    @60
    @139
    @109
    @111
    @22
    @60
    simpr
    @142
    syl3anc
    @144
    syl
    @61
    @2
    @101
    @148
    @102
    @103
    cS
    nodmord
    3syl
    @67
    @15
    ordtri2or
    syl2anc
    mpjaodan
    ex
    syl5bir
    mpd
    expr
    sylbid
    ralimdva
    syl5bi
    3impia
end
