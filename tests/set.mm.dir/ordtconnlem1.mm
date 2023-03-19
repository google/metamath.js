include "ctos.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "wn.mm"
include "wrex.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfra2.mm"
include "nfral.mm"
include "nfn.mm"
include "nfan.mm"
include "crab.mm"
include "ctopon.mm"
include "cfv.mm"
include "cpo.mm"
include "cpreset.mm"
include "tospos.mm"
include "posprs.mm"
include "cordt.mm"
include "cdm.mm"
include "cvv.mm"
include "cple.mm"
include "cxp.mm"
include "cin.mm"
include "fvex.mm"
include "inex1.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ordttopon.mm"
include "ax-mp.mm"
include "prsdm.mm"
include "fveq2d.mm"
include "syl5eleq.mm"
include "syl5eqel.mm"
include "3syl.mm"
include "ad3antrrr.mm"
include "adantlr.mm"
include "simpllr.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "simpll.mm"
include "csn.mm"
include "cfi.mm"
include "ctg.mm"
include "snex.mm"
include "cbs.mm"
include "mptex.mm"
include "rnex.mm"
include "unex.mm"
include "ssfii.mm"
include "bastg.mm"
include "sstri.mm"
include "ordtprsval.mm"
include "syl5eq.mm"
include "syl5sseqr.mm"
include "unssbd.mm"
include "syl.mm"
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "cbvrabv.mm"
include "breq1.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "wb.mm"
include "rabex.mm"
include "elrnmpt.mm"
include "sylibr.mm"
include "adantl.mm"
include "sseldd.mm"
include "ad2antrr.mm"
include "unssad.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "jca.mm"
include "simplrl.mm"
include "ssel.mm"
include "ancrd.mm"
include "anim1d.mm"
include "impl.mm"
include "elin.mm"
include "elrab.mm"
include "anbi1i.mm"
include "an32.mm"
include "3bitri.mm"
include "ne0i.mm"
include "sylanl1.mm"
include "r19.29an.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "w3a.mm"
include "wo.mm"
include "trleile.mm"
include "oran.mm"
include "sylib.mm"
include "3expa.mm"
include "nrexdv.mm"
include "wex.mm"
include "rabid.mm"
include "anbi12i.mm"
include "anandi.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "nfrab1.mm"
include "nfin.mm"
include "n0f.mm"
include "df-rex.mm"
include "necon1bbii.mm"
include "adantr.mm"
include "ineq1d.mm"
include "0in.mm"
include "syl6eq.mm"
include "cdif.mm"
include "simplr.mm"
include "vex.mm"
include "snss.mm"
include "eldif.mm"
include "bitr3i.mm"
include "ssconb.mm"
include "syl5bb.mm"
include "sylanb.mm"
include "anass1rs.mm"
include "mpbi2and.mm"
include "nfun.mm"
include "ianor.mm"
include "posrasymb.mm"
include "equcom.mm"
include "syl6bb.mm"
include "necon3bbid.mm"
include "syl5bbr.mm"
include "3expia.mm"
include "pm5.32d.mm"
include "orbi12i.mm"
include "elun.mm"
include "andi.mm"
include "3bitr4ri.mm"
include "eldifsn.mm"
include "bicomi.mm"
include "3bitr3g.mm"
include "eqrd.mm"
include "sseqtr4d.mm"
include "nconnsubb.mm"
include "anasss.mm"
include "adantllr.mm"
include "rexanali.mm"
include "rexbii.mm"
include "rexcom.mm"
include "rexnal.mm"
include "3bitr3i.mm"
include "r19.41v.mm"
include "reeanv.mm"
include "sselda.mm"
include "syl3anc.mm"
include "nelne2.mm"
include "mpbird.mm"
include "pm5.17.mm"
include "rexbidva.mm"
include "necomd.mm"
include "anbi12d.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "biimpa.mm"
include "r19.29af.mm"
include "con4d.mm"

theorem ordtconnlem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let vr: setvar r
  let vz: setvar z
  assume ordtconn.x: |- B = ( Base ` K )
  assume ordtconn.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )
  assume ordtconn.j: |- J = ( ordTop ` .<_ )

  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint J r
  disjoint K r
  disjoint K x
  disjoint K y
  disjoint .<_ x
  disjoint .<_ y
  disjoint r z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint K z
  disjoint .<_ z
  assert |- ( ( K e. Toset /\ A C_ B ) -> ( ( J |`t A ) e. Conn -> A. x e. A A. y e. A A. r e. B ( ( x .<_ r /\ r .<_ y ) -> r e. A ) ) )

  proof
    cK
    ctos
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    vx
    cv
    #
    vr
    cv
    #
    c.le
    wbr
    #
    @4
    vy
    cv
    #
    c.le
    wbr
    #
    wa
    #
    @4
    cA
    wcel
    #
    wi
    #
    vr
    cB
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    cJ
    cA
    crest
    co
    cconn
    wcel
    #
    @2
    @13
    wn
    #
    @14
    wn
    #
    @2
    @15
    wa
    @4
    @3
    c.le
    wbr
    #
    wn
    #
    vx
    cA
    wrex
    #
    @6
    @4
    c.le
    wbr
    #
    wn
    #
    vy
    cA
    wrex
    #
    wa
    #
    @9
    wn
    #
    wa
    #
    @16
    vr
    cB
    @2
    @15
    vr
    @2
    vr
    nfv
    @13
    vr
    @12
    vr
    vx
    cA
    vr
    cA
    nfcv
    @10
    vy
    vr
    cA
    cB
    nfra2
    nfral
    nfn
    nfan
    @2
    @4
    cB
    wcel
    #
    @25
    @16
    @15
    @2
    @26
    wa
    #
    @23
    @24
    @16
    @27
    @23
    wa
    #
    @24
    wa
    #
    cA
    @4
    vz
    cv
    #
    c.le
    wbr
    #
    wn
    #
    vz
    cB
    crab
    #
    cJ
    @30
    @4
    c.le
    wbr
    #
    wn
    #
    vz
    cB
    crab
    #
    cB
    @27
    @24
    cJ
    cB
    ctopon
    cfv
    #
    wcel
    #
    @23
    @0
    @38
    @1
    @26
    @24
    @0
    cK
    cpo
    wcel
    #
    cK
    cpreset
    wcel
    #
    @38
    cK
    tospos
    #
    cK
    posprs
    #
    @40
    cJ
    c.le
    cordt
    cfv
    #
    @37
    ordtconn.j
    @40
    @43
    c.le
    cdm
    #
    ctopon
    cfv
    #
    @37
    c.le
    cvv
    wcel
    @43
    @45
    wcel
    c.le
    cK
    cple
    cfv
    #
    cB
    cB
    cxp
    #
    cin
    cvv
    ordtconn.l
    @46
    @47
    cK
    cple
    fvex
    inex1
    eqeltri
    c.le
    cvv
    @44
    @44
    eqid
    ordttopon
    ax-mp
    @40
    @44
    cB
    ctopon
    cB
    cK
    c.le
    ordtconn.x
    ordtconn.l
    prsdm
    fveq2d
    syl5eleq
    syl5eqel
    3syl
    ad3antrrr
    adantlr
    @27
    @24
    @1
    @23
    @0
    @1
    @26
    @24
    simpllr
    #
    adantlr
    @27
    @33
    cJ
    wcel
    @23
    @24
    @27
    vx
    cB
    @3
    @6
    c.le
    wbr
    #
    wn
    #
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    cJ
    @33
    @27
    vx
    cB
    @6
    @3
    c.le
    wbr
    #
    wn
    #
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    @53
    cJ
    @27
    @40
    @58
    @53
    cun
    #
    cJ
    wss
    @27
    @0
    @39
    @40
    @0
    @1
    @26
    simpll
    #
    @41
    @42
    3syl
    @40
    cB
    csn
    #
    @59
    cJ
    @40
    @61
    @59
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @62
    cJ
    @62
    @63
    @64
    @62
    cvv
    wcel
    @62
    @63
    wss
    @61
    @59
    cB
    snex
    @58
    @53
    @57
    vx
    cB
    @56
    cB
    cK
    cbs
    cfv
    cvv
    ordtconn.x
    cK
    cbs
    fvex
    eqeltri
    #
    mptex
    rnex
    @52
    vx
    cB
    @51
    @65
    mptex
    rnex
    unex
    unex
    @62
    cvv
    ssfii
    ax-mp
    @63
    cvv
    wcel
    @63
    @64
    wss
    @62
    cfi
    fvex
    @63
    cvv
    bastg
    ax-mp
    sstri
    @40
    cJ
    @43
    @64
    ordtconn.j
    vx
    vy
    cB
    @58
    @53
    cK
    c.le
    ordtconn.x
    ordtconn.l
    @58
    eqid
    @53
    eqid
    ordtprsval
    syl5eq
    syl5sseqr
    unssbd
    syl
    #
    unssbd
    @26
    @33
    @53
    wcel
    #
    @2
    @26
    @33
    @51
    wceq
    #
    vx
    cB
    wrex
    #
    @67
    @26
    @33
    @7
    wn
    #
    vy
    cB
    crab
    #
    wceq
    #
    @69
    @32
    @70
    vz
    vy
    cB
    @30
    @6
    wceq
    #
    @31
    @7
    @30
    @6
    @4
    c.le
    breq2
    notbid
    cbvrabv
    @68
    @72
    vx
    @4
    cB
    @3
    @4
    wceq
    #
    @51
    @71
    @33
    @74
    @50
    @70
    vy
    cB
    @74
    @49
    @7
    @3
    @4
    @6
    c.le
    breq1
    notbid
    rabbidv
    eqeq2d
    rspcev
    mpan2
    @33
    cvv
    wcel
    @67
    @69
    wb
    @32
    vz
    cB
    @65
    rabex
    vx
    cB
    @51
    @33
    @52
    cvv
    @52
    eqid
    elrnmpt
    ax-mp
    sylibr
    adantl
    sseldd
    ad2antrr
    @27
    @36
    cJ
    wcel
    @23
    @24
    @27
    @58
    cJ
    @36
    @27
    @58
    @53
    cJ
    @66
    unssad
    @26
    @36
    @58
    wcel
    #
    @2
    @26
    @36
    @56
    wceq
    #
    vx
    cB
    wrex
    #
    @75
    @26
    @36
    @21
    vy
    cB
    crab
    #
    wceq
    #
    @77
    @35
    @21
    vz
    vy
    cB
    @73
    @34
    @20
    @30
    @6
    @4
    c.le
    breq1
    notbid
    #
    cbvrabv
    @76
    @79
    vx
    @4
    cB
    @74
    @56
    @78
    @36
    @74
    @55
    @21
    vy
    cB
    @74
    @54
    @20
    @3
    @4
    @6
    c.le
    breq2
    notbid
    rabbidv
    eqeq2d
    rspcev
    mpan2
    @36
    cvv
    wcel
    @75
    @77
    wb
    @35
    vz
    cB
    @65
    rabex
    vx
    cB
    @56
    @36
    @57
    cvv
    @57
    eqid
    elrnmpt
    ax-mp
    sylibr
    adantl
    sseldd
    ad2antrr
    @29
    @27
    @24
    wa
    #
    @19
    @33
    cA
    cin
    #
    c0
    wne
    #
    @29
    @27
    @24
    @27
    @23
    @24
    simpll
    @28
    @24
    simpr
    jca
    #
    @27
    @19
    @22
    @24
    simplrl
    @81
    @18
    @83
    vx
    cA
    @81
    @1
    @3
    cA
    wcel
    #
    @18
    @83
    @48
    @1
    @85
    wa
    @18
    wa
    #
    @3
    @82
    wcel
    #
    @83
    @86
    @3
    cB
    wcel
    #
    @85
    wa
    #
    @18
    wa
    #
    @87
    @1
    @85
    @18
    @90
    @1
    @85
    @89
    @18
    @1
    @85
    @88
    cA
    cB
    @3
    ssel
    ancrd
    anim1d
    impl
    @87
    @3
    @33
    wcel
    #
    @85
    wa
    @88
    @18
    wa
    #
    @85
    wa
    @90
    @3
    @33
    cA
    elin
    @91
    @92
    @85
    @32
    @18
    vz
    @3
    cB
    @30
    @3
    wceq
    @31
    @17
    @30
    @3
    @4
    c.le
    breq2
    notbid
    elrab
    anbi1i
    @88
    @18
    @85
    an32
    3bitri
    sylibr
    @82
    @3
    ne0i
    syl
    sylanl1
    r19.29an
    syl2anc
    @29
    @81
    @22
    @36
    cA
    cin
    #
    c0
    wne
    #
    @84
    @27
    @19
    @22
    @24
    simplrr
    @81
    @21
    @94
    vy
    cA
    @81
    @1
    @6
    cA
    wcel
    #
    @21
    @94
    @48
    @1
    @95
    wa
    @21
    wa
    #
    @6
    @93
    wcel
    #
    @94
    @96
    @6
    cB
    wcel
    #
    @95
    wa
    #
    @21
    wa
    #
    @97
    @1
    @95
    @21
    @100
    @1
    @95
    @99
    @21
    @1
    @95
    @98
    cA
    cB
    @6
    ssel
    ancrd
    anim1d
    impl
    @97
    @6
    @36
    wcel
    #
    @95
    wa
    @98
    @21
    wa
    #
    @95
    wa
    @100
    @6
    @36
    cA
    elin
    @101
    @102
    @95
    @35
    @21
    vz
    @6
    cB
    @80
    elrab
    anbi1i
    @98
    @21
    @95
    an32
    3bitri
    sylibr
    @93
    @6
    ne0i
    syl
    sylanl1
    r19.29an
    syl2anc
    @27
    @24
    @33
    @36
    cin
    #
    cA
    cin
    #
    c0
    wceq
    @23
    @81
    @104
    c0
    cA
    cin
    c0
    @81
    @103
    c0
    cA
    @27
    @103
    c0
    wceq
    #
    @24
    @0
    @26
    @105
    @1
    @0
    @26
    wa
    #
    @32
    @35
    wa
    #
    vz
    cB
    wrex
    #
    wn
    @105
    @106
    @107
    vz
    cB
    @0
    @26
    @30
    cB
    wcel
    #
    @107
    wn
    #
    @0
    @26
    @109
    w3a
    @31
    @34
    wo
    @110
    cB
    cK
    c.le
    @4
    @30
    ordtconn.x
    ordtconn.l
    trleile
    @31
    @34
    oran
    sylib
    3expa
    nrexdv
    @108
    @103
    c0
    @30
    @103
    wcel
    #
    vz
    wex
    @109
    @107
    wa
    #
    vz
    wex
    @103
    c0
    wne
    @108
    @111
    @112
    vz
    @30
    @33
    wcel
    #
    @30
    @36
    wcel
    #
    wa
    @109
    @32
    wa
    #
    @109
    @35
    wa
    #
    wa
    @111
    @112
    @113
    @115
    @114
    @116
    @32
    vz
    cB
    rabid
    #
    @35
    vz
    cB
    rabid
    #
    anbi12i
    @30
    @33
    @36
    elin
    @109
    @32
    @35
    anandi
    3bitr4i
    exbii
    vz
    @103
    vz
    @33
    @36
    @32
    vz
    cB
    nfrab1
    #
    @35
    vz
    cB
    nfrab1
    #
    nfin
    n0f
    @107
    vz
    cB
    df-rex
    3bitr4i
    necon1bbii
    sylib
    adantlr
    adantr
    ineq1d
    cA
    0in
    syl6eq
    adantlr
    @27
    @24
    cA
    @33
    @36
    cun
    #
    wss
    @23
    @81
    cA
    cB
    @4
    csn
    #
    cdif
    #
    @121
    @81
    @26
    @24
    cA
    @123
    wss
    #
    @2
    @26
    @24
    simplr
    #
    @27
    @24
    simpr
    @27
    @26
    @24
    wa
    #
    @124
    wb
    #
    @24
    @0
    @26
    @1
    @127
    @26
    @1
    wa
    @127
    @0
    @26
    @122
    cB
    wss
    #
    @1
    @127
    @4
    cB
    vr
    vex
    #
    snss
    @126
    @122
    cB
    cA
    cdif
    #
    wss
    #
    @128
    @1
    wa
    @124
    @126
    @4
    @130
    wcel
    @131
    @4
    cB
    cA
    eldif
    @4
    @130
    @129
    snss
    bitr3i
    @122
    cA
    cB
    ssconb
    syl5bb
    sylanb
    adantl
    anass1rs
    adantr
    mpbi2and
    @81
    @39
    @26
    @121
    @123
    wceq
    @0
    @39
    @1
    @26
    @24
    @41
    ad3antrrr
    #
    @125
    @39
    @26
    wa
    #
    vz
    @121
    @123
    @133
    vz
    nfv
    vz
    @33
    @36
    @119
    @120
    nfun
    vz
    @123
    nfcv
    @133
    @109
    @32
    @35
    wo
    #
    wa
    #
    @109
    @30
    @4
    wne
    #
    wa
    #
    @30
    @121
    wcel
    #
    @30
    @123
    wcel
    #
    @133
    @109
    @134
    @136
    @39
    @26
    @109
    @134
    @136
    wb
    @134
    @31
    @34
    wa
    #
    wn
    @39
    @26
    @109
    w3a
    #
    @136
    @31
    @34
    ianor
    @141
    @140
    @30
    @4
    @141
    @140
    @4
    @30
    wceq
    @30
    @4
    wceq
    cB
    cK
    c.le
    @4
    @30
    ordtconn.x
    ordtconn.l
    posrasymb
    vr
    vz
    equcom
    syl6bb
    necon3bbid
    syl5bbr
    3expia
    pm5.32d
    @113
    @114
    wo
    @115
    @116
    wo
    @138
    @135
    @113
    @115
    @114
    @116
    @117
    @118
    orbi12i
    @30
    @33
    @36
    elun
    @109
    @32
    @35
    andi
    3bitr4ri
    @139
    @137
    @30
    cB
    @4
    eldifsn
    bicomi
    3bitr3g
    eqrd
    syl2anc
    sseqtr4d
    adantlr
    nconnsubb
    anasss
    adantllr
    @2
    @15
    @25
    vr
    cB
    wrex
    #
    @15
    @5
    vx
    cA
    wrex
    #
    @7
    vy
    cA
    wrex
    #
    wa
    #
    @24
    wa
    #
    vr
    cB
    wrex
    #
    @2
    @142
    @15
    @8
    @24
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    vr
    cB
    wrex
    #
    @147
    @149
    vr
    cB
    wrex
    #
    vx
    cA
    wrex
    @12
    wn
    #
    vx
    cA
    wrex
    @151
    @15
    @152
    @153
    vx
    cA
    @148
    vr
    cB
    wrex
    #
    vy
    cA
    wrex
    @11
    wn
    #
    vy
    cA
    wrex
    @152
    @153
    @154
    @155
    vy
    cA
    @8
    @9
    vr
    cB
    rexanali
    rexbii
    @148
    vy
    vr
    cA
    cB
    rexcom
    @11
    vy
    cA
    rexnal
    3bitr3i
    rexbii
    @149
    vx
    vr
    cA
    cB
    rexcom
    @12
    vx
    cA
    rexnal
    3bitr3i
    @150
    @146
    vr
    cB
    @150
    @8
    vy
    cA
    wrex
    #
    @24
    wa
    #
    vx
    cA
    wrex
    @156
    vx
    cA
    wrex
    #
    @24
    wa
    @146
    @149
    @157
    vx
    cA
    @8
    @24
    vy
    cA
    r19.41v
    rexbii
    @156
    @24
    vx
    cA
    r19.41v
    @158
    @145
    @24
    @5
    @7
    vx
    vy
    cA
    cA
    reeanv
    anbi1i
    3bitri
    rexbii
    bitr3i
    @2
    @146
    @25
    vr
    cB
    @27
    @24
    @145
    @23
    @27
    @24
    @145
    @23
    wb
    @81
    @143
    @19
    @144
    @22
    @81
    @5
    @18
    vx
    cA
    @81
    @85
    wa
    #
    @5
    @17
    wo
    #
    @5
    @17
    wa
    #
    wn
    #
    wa
    @5
    @18
    wb
    @159
    @160
    @162
    @159
    @0
    @88
    @26
    @160
    @27
    @0
    @24
    @85
    @60
    ad2antrr
    @81
    cA
    cB
    @3
    @48
    sselda
    #
    @2
    @26
    @24
    @85
    simpllr
    #
    cB
    cK
    c.le
    @3
    @4
    ordtconn.x
    ordtconn.l
    trleile
    syl3anc
    @159
    @162
    @3
    @4
    wne
    #
    @159
    @85
    @24
    @165
    @81
    @85
    simpr
    @27
    @24
    @85
    simplr
    @3
    @4
    cA
    nelne2
    syl2anc
    @159
    @39
    @88
    @26
    @162
    @165
    wb
    @81
    @39
    @85
    @132
    adantr
    @163
    @164
    @39
    @88
    @26
    w3a
    @161
    @3
    @4
    cB
    cK
    c.le
    @3
    @4
    ordtconn.x
    ordtconn.l
    posrasymb
    necon3bbid
    syl3anc
    mpbird
    jca
    @5
    @17
    pm5.17
    sylib
    rexbidva
    @81
    @7
    @21
    vy
    cA
    @81
    @95
    wa
    #
    @7
    @20
    wo
    #
    @7
    @20
    wa
    #
    wn
    #
    wa
    @7
    @21
    wb
    @166
    @167
    @169
    @166
    @0
    @26
    @98
    @167
    @27
    @0
    @24
    @95
    @60
    ad2antrr
    @2
    @26
    @24
    @95
    simpllr
    #
    @81
    cA
    cB
    @6
    @48
    sselda
    #
    cB
    cK
    c.le
    @4
    @6
    ordtconn.x
    ordtconn.l
    trleile
    syl3anc
    @166
    @169
    @4
    @6
    wne
    #
    @166
    @6
    @4
    @166
    @95
    @24
    @6
    @4
    wne
    @81
    @95
    simpr
    @27
    @24
    @95
    simplr
    @6
    @4
    cA
    nelne2
    syl2anc
    necomd
    @166
    @39
    @26
    @98
    @169
    @172
    wb
    @81
    @39
    @95
    @132
    adantr
    @170
    @171
    @39
    @26
    @98
    w3a
    @168
    @4
    @6
    cB
    cK
    c.le
    @4
    @6
    ordtconn.x
    ordtconn.l
    posrasymb
    necon3bbid
    syl3anc
    mpbird
    jca
    @7
    @20
    pm5.17
    sylib
    rexbidva
    anbi12d
    ex
    pm5.32rd
    rexbidva
    syl5bb
    biimpa
    r19.29af
    ex
    con4d
end
