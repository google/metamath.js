include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "oacl.mm"
include "oa0.mm"
include "syl.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wi.mm"
include "suceq.mm"
include "oasuc.mm"
include "sylan.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "anassrs.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "cvv.mm"
include "vex.mm"
include "oalim.mm"
include "mpanr1.mm"
include "ancoms.mm"
include "adantr.mm"
include "oalimcl.mm"
include "ovex.mm"
include "wss.mm"
include "wrex.mm"
include "limelon.mm"
include "mpan.mm"
include "onelon.mm"
include "ex.mm"
include "adantld.mm"
include "0ellim.mm"
include "onelss.mm"
include "sseq2d.mm"
include "sylibrd.mm"
include "imp.mm"
include "rspcev.mm"
include "syl2an.mm"
include "expr.mm"
include "adantrl.mm"
include "adantrr.mm"
include "wb.mm"
include "oawordex.mm"
include "ad2ant2l.mm"
include "oaord.mm"
include "3expb.mm"
include "eleq1.mm"
include "sylan9bb.mm"
include "an32s.mm"
include "biimpar.mm"
include "eqimss2.mm"
include "ad3antlr.mm"
include "jca.mm"
include "anasss.mm"
include "reximdv2.mm"
include "sylbid.mm"
include "wo.mm"
include "word.mm"
include "eloni.mm"
include "ordtri2or.mm"
include "syl2anr.mm"
include "mpjaod.mm"
include "exp45.mm"
include "imp32.mm"
include "simplrr.mm"
include "exp32.mm"
include "com12.mm"
include "imp31.mm"
include "adantll.mm"
include "adantlr.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "oaword.mm"
include "syl3anc.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "mpdd.mm"
include "mpd.mm"
include "exp4a.mm"
include "ralrimiv.mm"
include "iunss2.mm"
include "oaordi.mm"
include "anim1d.mm"
include "eleq2d.mm"
include "syl6.mm"
include "expd.mm"
include "rexlimdv.mm"
include "eliun.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "an12s.mm"
include "iuneq2.mm"
include "exp31.mm"
include "tfinds3.mm"
include "3impia.mm"

theorem oaass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( ( A +o B ) +o C ) = ( A +o ( B +o C ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    cA
    cB
    coa
    co
    #
    cC
    coa
    co
    #
    cA
    cB
    cC
    coa
    co
    #
    coa
    co
    #
    wceq
    #
    @2
    @0
    @1
    wa
    #
    @7
    @3
    vx
    cv
    #
    coa
    co
    #
    cA
    cB
    @9
    coa
    co
    #
    coa
    co
    #
    wceq
    #
    @3
    c0
    coa
    co
    #
    cA
    cB
    c0
    coa
    co
    #
    coa
    co
    #
    wceq
    @3
    vy
    cv
    #
    coa
    co
    #
    cA
    cB
    @17
    coa
    co
    #
    coa
    co
    #
    wceq
    #
    @3
    @17
    csuc
    #
    coa
    co
    #
    cA
    cB
    @22
    coa
    co
    #
    coa
    co
    #
    wceq
    #
    @7
    @8
    vx
    vy
    cC
    @9
    c0
    wceq
    #
    @10
    @14
    @12
    @16
    @9
    c0
    @3
    coa
    oveq2
    @27
    @11
    @15
    cA
    coa
    @9
    c0
    cB
    coa
    oveq2
    oveq2d
    eqeq12d
    @9
    @17
    wceq
    #
    @10
    @18
    @12
    @20
    @9
    @17
    @3
    coa
    oveq2
    @28
    @11
    @19
    cA
    coa
    @9
    @17
    cB
    coa
    oveq2
    oveq2d
    eqeq12d
    @9
    @22
    wceq
    #
    @10
    @23
    @12
    @25
    @9
    @22
    @3
    coa
    oveq2
    @29
    @11
    @24
    cA
    coa
    @9
    @22
    cB
    coa
    oveq2
    oveq2d
    eqeq12d
    @9
    cC
    wceq
    #
    @10
    @4
    @12
    @6
    @9
    cC
    @3
    coa
    oveq2
    @30
    @11
    @5
    cA
    coa
    @9
    cC
    cB
    coa
    oveq2
    oveq2d
    eqeq12d
    @8
    @14
    @3
    @16
    @8
    @3
    con0
    wcel
    #
    @14
    @3
    wceq
    cA
    cB
    oacl
    #
    @3
    oa0
    syl
    @1
    @16
    @3
    wceq
    @0
    @1
    @15
    cB
    cA
    coa
    cB
    oa0
    #
    oveq2d
    adantl
    eqtr4d
    @8
    @17
    con0
    wcel
    #
    @21
    @26
    wi
    @21
    @26
    @8
    @34
    wa
    #
    @18
    csuc
    #
    @20
    csuc
    #
    wceq
    @18
    @20
    suceq
    @35
    @23
    @36
    @25
    @37
    @8
    @31
    @34
    @23
    @36
    wceq
    @32
    @3
    @17
    oasuc
    sylan
    @0
    @1
    @34
    @25
    @37
    wceq
    @0
    @1
    @34
    wa
    #
    wa
    @25
    cA
    @19
    csuc
    #
    coa
    co
    #
    @37
    @38
    @25
    @40
    wceq
    @0
    @38
    @24
    @39
    cA
    coa
    cB
    @17
    oasuc
    oveq2d
    adantl
    @38
    @0
    @19
    con0
    wcel
    #
    @40
    @37
    wceq
    cB
    @17
    oacl
    #
    cA
    @19
    oasuc
    sylan2
    eqtrd
    anassrs
    eqeq12d
    syl5ibr
    expcom
    @9
    wlim
    #
    @8
    @21
    vy
    @9
    wral
    #
    @13
    @43
    @8
    wa
    #
    @44
    wa
    #
    @10
    vy
    @9
    @18
    ciun
    #
    @12
    @45
    @10
    @47
    wceq
    #
    @44
    @8
    @43
    @48
    @8
    @31
    @43
    @48
    @32
    @31
    @9
    cvv
    wcel
    #
    @43
    @48
    vx
    vex
    #
    vy
    @3
    @9
    cvv
    oalim
    mpanr1
    sylan
    ancoms
    adantr
    @46
    @12
    vy
    @9
    @20
    ciun
    #
    @47
    @45
    @12
    @51
    wceq
    #
    @44
    @0
    @43
    @1
    @52
    @0
    @43
    @1
    wa
    #
    wa
    #
    @12
    vz
    @11
    cA
    vz
    cv
    #
    coa
    co
    #
    ciun
    #
    @51
    @53
    @0
    @11
    wlim
    #
    @12
    @57
    wceq
    #
    @1
    @43
    @58
    @1
    @49
    @43
    @58
    @50
    cB
    @9
    cvv
    oalimcl
    mpanr1
    ancoms
    @0
    @11
    cvv
    wcel
    @58
    @59
    cB
    @9
    coa
    ovex
    vz
    cA
    @11
    cvv
    oalim
    mpanr1
    sylan2
    @54
    @57
    @51
    @53
    @0
    @57
    @51
    wss
    #
    @53
    @0
    wa
    #
    @56
    @20
    wss
    #
    vy
    @9
    wrex
    #
    vz
    @11
    wral
    @60
    @61
    @63
    vz
    @11
    @43
    @1
    @0
    @55
    @11
    wcel
    #
    @63
    wi
    @43
    @1
    @0
    @64
    @63
    @43
    @9
    con0
    wcel
    #
    @1
    @0
    @64
    wa
    #
    @63
    wi
    #
    wi
    @49
    @43
    @65
    @50
    @9
    cvv
    limelon
    mpan
    #
    @43
    @65
    @1
    @67
    @43
    @65
    @1
    wa
    #
    wa
    #
    @66
    @55
    con0
    wcel
    #
    @63
    @69
    @66
    @71
    wi
    @43
    @69
    @64
    @71
    @0
    @69
    @11
    con0
    wcel
    #
    @64
    @71
    wi
    @1
    @65
    @72
    cB
    @9
    oacl
    ancoms
    @72
    @64
    @71
    @11
    @55
    onelon
    ex
    syl
    adantld
    adantl
    @70
    @66
    @71
    @63
    @70
    @66
    @71
    wa
    #
    wa
    #
    @55
    @19
    wss
    #
    vy
    @9
    wrex
    #
    @63
    @70
    @66
    @71
    @76
    @70
    @64
    @71
    @76
    wi
    #
    @0
    @43
    @69
    @64
    @77
    wi
    @43
    @69
    @64
    @71
    @76
    @43
    @69
    @64
    @71
    wa
    #
    wa
    #
    wa
    @55
    cB
    wcel
    #
    @76
    cB
    @55
    wss
    #
    @43
    @69
    @80
    @76
    wi
    #
    @78
    @43
    @1
    @82
    @65
    @43
    @1
    @80
    @76
    @43
    c0
    @9
    wcel
    @55
    @15
    wss
    #
    @76
    @1
    @80
    wa
    @9
    0ellim
    @1
    @80
    @83
    @1
    @80
    @55
    cB
    wss
    @83
    cB
    @55
    onelss
    @1
    @15
    cB
    @55
    @33
    sseq2d
    sylibrd
    imp
    @75
    @83
    vy
    c0
    @9
    @17
    c0
    wceq
    @19
    @15
    @55
    @17
    c0
    cB
    coa
    oveq2
    sseq2d
    rspcev
    syl2an
    expr
    adantrl
    adantrr
    @79
    @81
    @76
    wi
    @43
    @79
    @81
    @19
    @55
    wceq
    #
    vy
    con0
    wrex
    #
    @76
    @1
    @71
    @81
    @85
    wb
    @65
    @64
    vy
    cB
    @55
    oawordex
    ad2ant2l
    @69
    @64
    @85
    @76
    wi
    @71
    @69
    @64
    wa
    #
    @84
    @75
    vy
    con0
    @9
    @34
    @84
    wa
    #
    @86
    @17
    @9
    wcel
    #
    @75
    wa
    #
    @87
    @69
    @64
    @89
    @87
    @69
    wa
    #
    @64
    wa
    @88
    @75
    @90
    @88
    @64
    @34
    @69
    @84
    @88
    @64
    wb
    @34
    @69
    wa
    @88
    @19
    @11
    wcel
    #
    @84
    @64
    @34
    @65
    @1
    @88
    @91
    wb
    @17
    @9
    cB
    oaord
    3expb
    @19
    @55
    @11
    eleq1
    sylan9bb
    an32s
    biimpar
    @84
    @75
    @34
    @69
    @64
    @55
    @19
    eqimss2
    ad3antlr
    jca
    anasss
    expcom
    reximdv2
    adantrr
    sylbid
    adantl
    @79
    @80
    @81
    wo
    #
    @43
    @1
    @71
    @92
    @65
    @64
    @71
    @55
    word
    cB
    word
    @92
    @1
    @55
    eloni
    cB
    eloni
    @55
    cB
    ordtri2or
    syl2anr
    ad2ant2l
    adantl
    mpjaod
    exp45
    imp
    adantld
    imp32
    @74
    @75
    @62
    vy
    @9
    @74
    @88
    wa
    @71
    @41
    @0
    @75
    @62
    wb
    @70
    @66
    @71
    @88
    simplrr
    @70
    @88
    @41
    @73
    @69
    @88
    @41
    @43
    @65
    @1
    @88
    @41
    @1
    @65
    @88
    @41
    wi
    @1
    @65
    @88
    @41
    @65
    @88
    wa
    @1
    @34
    @41
    @9
    @17
    onelon
    @42
    sylan2
    exp32
    com12
    imp31
    adantll
    adantlr
    @73
    @0
    @70
    @88
    @0
    @64
    @71
    simpll
    ad2antlr
    @55
    @19
    cA
    oaword
    syl3anc
    rexbidva
    mpbid
    exp32
    mpdd
    exp32
    mpd
    exp4a
    imp31
    ralrimiv
    vz
    vy
    @11
    @9
    @56
    @20
    iunss2
    syl
    ancoms
    @53
    @51
    @57
    wss
    #
    @0
    @43
    @65
    @1
    @93
    @68
    @69
    vw
    @51
    @57
    @69
    vw
    cv
    #
    @20
    wcel
    #
    vy
    @9
    wrex
    @94
    @56
    wcel
    #
    vz
    @11
    wrex
    #
    @94
    @51
    wcel
    @94
    @57
    wcel
    @69
    @95
    @97
    vy
    @9
    @69
    @88
    @95
    @97
    @69
    @88
    @95
    wa
    @91
    @95
    wa
    @97
    @69
    @88
    @91
    @95
    @17
    @9
    cB
    oaordi
    anim1d
    @96
    @95
    vz
    @19
    @11
    @55
    @19
    wceq
    @56
    @20
    @94
    @55
    @19
    cA
    coa
    oveq2
    eleq2d
    rspcev
    syl6
    expd
    rexlimdv
    vy
    @94
    @9
    @20
    eliun
    vz
    @94
    @11
    @56
    eliun
    3imtr4g
    ssrdv
    sylan
    adantl
    eqssd
    eqtrd
    an12s
    adantr
    @44
    @47
    @51
    wceq
    @45
    vy
    @9
    @18
    @20
    iuneq2
    adantl
    eqtr4d
    eqtr4d
    exp31
    tfinds3
    com12
    3impia
end
