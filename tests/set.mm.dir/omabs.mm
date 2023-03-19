include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wa.mm"
include "con0.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "csuc.mm"
include "eleq2.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "simprl.mm"
include "simpll.mm"
include "simplr.mm"
include "omabslem.mm"
include "syl3anc.mm"
include "adantr.mm"
include "c1o.mm"
include "suceq.mm"
include "df-1o.mm"
include "syl6eqr.mm"
include "oe1.mm"
include "ad2antrl.mm"
include "sylan9eqr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "a1dd.mm"
include "oveq1.mm"
include "oesuc.mm"
include "adantl.mm"
include "nnon.mm"
include "ad2antrr.mm"
include "oecl.mm"
include "omass.mm"
include "eqtr4d.mm"
include "syl5ibr.mm"
include "imim2d.mm"
include "com23.mm"
include "wo.mm"
include "simprr.mm"
include "on0eqel.mm"
include "syl.mm"
include "mpjaod.mm"
include "anassrs.mm"
include "expcom.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "ad3antrrr.mm"
include "cvv.mm"
include "vex.mm"
include "jctil.mm"
include "limelon.mm"
include "syl2anc.mm"
include "c2o.mm"
include "cdif.mm"
include "1onn.mm"
include "ondif2.mm"
include "sylanbrc.mm"
include "oelimcl.mm"
include "omlim.mm"
include "syl12anc.mm"
include "wss.mm"
include "wrex.mm"
include "simplrl.mm"
include "oelim2.mm"
include "eleq2d.mm"
include "eliun.mm"
include "syl6bb.mm"
include "wb.mm"
include "anass.mm"
include "wne.mm"
include "onelon.mm"
include "on0eln0.mm"
include "pm5.32da.mm"
include "dif1o.mm"
include "syl6bbr.mm"
include "anbi1d.mm"
include "syl5bbr.mm"
include "rexbidv2.mm"
include "bitr4d.mm"
include "r19.29.mm"
include "id.mm"
include "imp.mm"
include "anim1i.mm"
include "anasss.mm"
include "word.mm"
include "eloni.mm"
include "omord2.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "eleqtrd.mm"
include "oeord.mm"
include "ontr1.mm"
include "mp2and.mm"
include "ordelss.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "expdimp.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "simpllr.mm"
include "omword2.mm"
include "syl21anc.mm"
include "eqssd.mm"
include "tfinds3.mm"
include "com12.mm"
include "adantrr.mm"
include "imp32.mm"
include "an32s.mm"
include "wn.mm"
include "nnm0.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "fnoe.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "pm2.61dan.mm"

theorem omabs
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( ( A e. _om /\ (/) e. A ) /\ ( B e. On /\ (/) e. B ) ) -> ( A .o ( _om ^o B ) ) = ( _om ^o B ) )

  proof
    cA
    com
    wcel
    #
    c0
    cA
    wcel
    #
    wa
    #
    cB
    con0
    wcel
    #
    c0
    cB
    wcel
    #
    wa
    #
    wa
    #
    com
    con0
    wcel
    #
    @3
    wa
    #
    cA
    com
    cB
    coe
    co
    #
    comu
    co
    #
    @9
    wceq
    #
    @2
    @8
    @5
    @11
    @2
    @8
    wa
    @3
    @4
    @11
    @2
    @7
    @3
    @4
    @11
    wi
    #
    wi
    @3
    @3
    @2
    @7
    wa
    #
    @12
    c0
    vx
    cv
    #
    wcel
    #
    cA
    com
    @14
    coe
    co
    #
    comu
    co
    #
    @16
    wceq
    #
    wi
    #
    c0
    c0
    wcel
    #
    cA
    com
    c0
    coe
    co
    #
    comu
    co
    #
    @21
    wceq
    #
    wi
    #
    c0
    vy
    cv
    #
    wcel
    #
    cA
    com
    @25
    coe
    co
    #
    comu
    co
    #
    @27
    wceq
    #
    wi
    #
    c0
    @25
    csuc
    #
    wcel
    #
    cA
    com
    @31
    coe
    co
    #
    comu
    co
    #
    @33
    wceq
    #
    wi
    #
    @12
    @13
    vx
    vy
    cB
    @14
    c0
    wceq
    #
    @15
    @20
    @18
    @23
    @14
    c0
    c0
    eleq2
    @37
    @17
    @22
    @16
    @21
    @37
    @16
    @21
    cA
    comu
    @14
    c0
    com
    coe
    oveq2
    #
    oveq2d
    @38
    eqeq12d
    imbi12d
    @14
    @25
    wceq
    #
    @15
    @26
    @18
    @29
    @14
    @25
    c0
    eleq2
    @39
    @17
    @28
    @16
    @27
    @39
    @16
    @27
    cA
    comu
    @14
    @25
    com
    coe
    oveq2
    #
    oveq2d
    @40
    eqeq12d
    imbi12d
    @14
    @31
    wceq
    #
    @15
    @32
    @18
    @35
    @14
    @31
    c0
    eleq2
    @41
    @17
    @34
    @16
    @33
    @41
    @16
    @33
    cA
    comu
    @14
    @31
    com
    coe
    oveq2
    #
    oveq2d
    @42
    eqeq12d
    imbi12d
    @14
    cB
    wceq
    #
    @15
    @4
    @18
    @11
    @14
    cB
    c0
    eleq2
    @43
    @17
    @10
    @16
    @9
    @43
    @16
    @9
    cA
    comu
    @14
    cB
    com
    coe
    oveq2
    #
    oveq2d
    @44
    eqeq12d
    imbi12d
    @24
    @13
    @20
    @23
    c0
    noel
    pm2.21i
    a1i
    @13
    @25
    con0
    wcel
    #
    @30
    @36
    wi
    #
    @2
    @7
    @45
    @46
    @2
    @7
    @45
    wa
    #
    wa
    #
    @30
    @35
    @32
    @48
    @25
    c0
    wceq
    #
    @30
    @35
    wi
    @26
    @48
    @49
    @35
    @30
    @48
    @49
    @35
    @48
    @49
    wa
    #
    cA
    com
    comu
    co
    #
    com
    @34
    @33
    @48
    @51
    com
    wceq
    #
    @49
    @48
    @7
    @0
    @1
    @52
    @2
    @7
    @45
    simprl
    #
    @0
    @1
    @47
    simpll
    @0
    @1
    @47
    simplr
    cA
    omabslem
    syl3anc
    adantr
    @50
    @33
    com
    cA
    comu
    @49
    @48
    @33
    com
    c1o
    coe
    co
    #
    com
    @49
    @31
    c1o
    com
    coe
    @49
    @31
    c0
    csuc
    c1o
    @25
    c0
    suceq
    df-1o
    syl6eqr
    oveq2d
    @7
    @54
    com
    wceq
    @2
    @45
    com
    oe1
    ad2antrl
    sylan9eqr
    #
    oveq2d
    @55
    3eqtr4d
    ex
    a1dd
    @48
    @30
    @26
    @35
    @48
    @29
    @35
    @26
    @29
    @35
    @48
    @28
    com
    comu
    co
    #
    @27
    com
    comu
    co
    #
    wceq
    @28
    @27
    com
    comu
    oveq1
    @48
    @34
    @56
    @33
    @57
    @48
    @34
    cA
    @57
    comu
    co
    #
    @56
    @48
    @33
    @57
    cA
    comu
    @47
    @33
    @57
    wceq
    @2
    com
    @25
    oesuc
    adantl
    #
    oveq2d
    @48
    cA
    con0
    wcel
    #
    @27
    con0
    wcel
    #
    @7
    @56
    @58
    wceq
    @0
    @60
    @1
    @47
    cA
    nnon
    #
    ad2antrr
    @47
    @61
    @2
    com
    @25
    oecl
    #
    adantl
    @53
    cA
    @27
    com
    omass
    syl3anc
    eqtr4d
    @59
    eqeq12d
    syl5ibr
    imim2d
    com23
    @48
    @45
    @49
    @26
    wo
    @2
    @7
    @45
    simprr
    @25
    on0eqel
    syl
    mpjaod
    a1dd
    anassrs
    expcom
    @13
    @14
    wlim
    #
    @30
    vy
    @14
    wral
    #
    @19
    wi
    @13
    @64
    wa
    @65
    @18
    @15
    @2
    @7
    @64
    @65
    @18
    wi
    @2
    @7
    @64
    wa
    #
    wa
    #
    @65
    @18
    @67
    @65
    wa
    #
    @17
    @16
    @68
    @17
    vz
    @16
    cA
    vz
    cv
    #
    comu
    co
    #
    ciun
    #
    @16
    @68
    @60
    @16
    con0
    wcel
    #
    @16
    wlim
    #
    @17
    @71
    wceq
    @0
    @60
    @1
    @66
    @65
    @62
    ad3antrrr
    #
    @67
    @72
    @65
    @67
    @7
    @14
    con0
    wcel
    #
    @72
    @2
    @7
    @64
    simprl
    #
    @67
    @14
    cvv
    wcel
    #
    @64
    wa
    #
    @75
    @67
    @64
    @77
    @2
    @7
    @64
    simprr
    vx
    vex
    jctil
    #
    @14
    cvv
    limelon
    syl
    #
    com
    @14
    oecl
    syl2anc
    #
    adantr
    #
    @68
    com
    con0
    c2o
    cdif
    wcel
    #
    @78
    @73
    @67
    @83
    @65
    @67
    @7
    c1o
    com
    wcel
    #
    @83
    @76
    @84
    @67
    1onn
    a1i
    com
    ondif2
    sylanbrc
    #
    adantr
    @67
    @78
    @65
    @79
    adantr
    #
    com
    @14
    cvv
    oelimcl
    syl2anc
    vz
    cA
    @16
    con0
    omlim
    syl12anc
    @68
    @70
    @16
    wss
    #
    vz
    @16
    wral
    @71
    @16
    wss
    @68
    @87
    vz
    @16
    @68
    @69
    @16
    wcel
    #
    @26
    @69
    @27
    wcel
    #
    wa
    #
    vy
    @14
    wrex
    #
    @87
    @68
    @88
    @89
    vy
    @14
    c1o
    cdif
    #
    wrex
    #
    @91
    @68
    @88
    @69
    vy
    @92
    @27
    ciun
    #
    wcel
    @93
    @68
    @16
    @94
    @69
    @68
    @7
    @78
    @16
    @94
    wceq
    @2
    @7
    @64
    @65
    simplrl
    @86
    vy
    com
    @14
    cvv
    oelim2
    syl2anc
    eleq2d
    vy
    @69
    @92
    @27
    eliun
    syl6bb
    @68
    @75
    @91
    @93
    wb
    @67
    @75
    @65
    @80
    adantr
    @75
    @90
    @89
    vy
    @14
    @92
    @25
    @14
    wcel
    #
    @90
    wa
    @95
    @26
    wa
    #
    @89
    wa
    @75
    @25
    @92
    wcel
    #
    @89
    wa
    @95
    @26
    @89
    anass
    @75
    @96
    @97
    @89
    @75
    @96
    @95
    @25
    c0
    wne
    #
    wa
    @97
    @75
    @95
    @26
    @98
    @75
    @95
    wa
    @45
    @26
    @98
    wb
    @14
    @25
    onelon
    #
    @25
    on0eln0
    syl
    pm5.32da
    @25
    @14
    dif1o
    syl6bbr
    anbi1d
    syl5bbr
    rexbidv2
    syl
    bitr4d
    @67
    @65
    @91
    @87
    @65
    @91
    wa
    @30
    @90
    wa
    #
    vy
    @14
    wrex
    @67
    @87
    @30
    @90
    vy
    @14
    r19.29
    @67
    @100
    @87
    vy
    @14
    @100
    @29
    @89
    wa
    #
    @67
    @95
    wa
    #
    @87
    @30
    @26
    @89
    @101
    @30
    @26
    wa
    @29
    @89
    @30
    @26
    @29
    @30
    id
    imp
    anim1i
    anasss
    @102
    @101
    @87
    @102
    @101
    wa
    #
    @16
    word
    #
    @70
    @16
    wcel
    #
    @87
    @103
    @72
    @104
    @67
    @72
    @95
    @101
    @81
    ad2antrr
    #
    @16
    eloni
    syl
    @103
    @70
    @27
    wcel
    #
    @27
    @16
    wcel
    #
    @105
    @103
    @70
    @28
    @27
    @103
    @89
    @70
    @28
    wcel
    #
    @102
    @29
    @89
    simprr
    #
    @103
    @69
    con0
    wcel
    #
    @61
    @60
    @1
    @89
    @109
    wb
    @103
    @61
    @89
    @111
    @103
    @7
    @45
    @61
    @67
    @7
    @95
    @101
    @76
    ad2antrr
    @103
    @75
    @95
    @45
    @67
    @75
    @95
    @101
    @80
    ad2antrr
    #
    @67
    @95
    @101
    simplr
    #
    @99
    syl2anc
    #
    @63
    syl2anc
    #
    @110
    @27
    @69
    onelon
    syl2anc
    @115
    @67
    @60
    @95
    @101
    @0
    @60
    @1
    @66
    @62
    ad2antrr
    ad2antrr
    @67
    @1
    @95
    @101
    @0
    @1
    @66
    simplr
    ad2antrr
    @69
    @27
    cA
    omord2
    syl31anc
    mpbid
    @102
    @29
    @89
    simprl
    eleqtrd
    @103
    @95
    @108
    @113
    @103
    @45
    @75
    @83
    @95
    @108
    wb
    @114
    @112
    @67
    @83
    @95
    @101
    @85
    ad2antrr
    @25
    @14
    com
    oeord
    syl3anc
    mpbid
    @103
    @72
    @107
    @108
    wa
    @105
    wi
    @106
    @70
    @27
    @16
    ontr1
    syl
    mp2and
    @16
    @70
    ordelss
    syl2anc
    ex
    syl5
    rexlimdva
    syl5
    expdimp
    sylbid
    ralrimiv
    vz
    @16
    @70
    @16
    iunss
    sylibr
    eqsstrd
    @68
    @72
    @60
    @1
    @16
    @17
    wss
    @82
    @74
    @0
    @1
    @66
    @65
    simpllr
    @16
    cA
    omword2
    syl21anc
    eqssd
    ex
    anassrs
    a1dd
    expcom
    tfinds3
    com12
    adantrr
    imp32
    an32s
    @6
    @8
    wn
    #
    wa
    #
    cA
    c0
    comu
    co
    #
    c0
    @10
    @9
    @0
    @118
    c0
    wceq
    @1
    @5
    @116
    cA
    nnm0
    ad3antrrr
    @117
    @9
    c0
    cA
    comu
    @116
    @9
    c0
    wceq
    @6
    com
    cB
    con0
    coe
    coe
    con0
    con0
    cxp
    #
    wfn
    coe
    cdm
    @119
    wceq
    fnoe
    @119
    coe
    fndm
    ax-mp
    ndmov
    adantl
    #
    oveq2d
    @120
    3eqtr4d
    pm2.61dan
end
