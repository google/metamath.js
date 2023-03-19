include "cres.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cdm.mm"
include "fssresd.mm"
include "wa.mm"
include "caddc.mm"
include "wceq.mm"
include "crab.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "w3a.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "sselda.mm"
include "recnd.mm"
include "adantr.mm"
include "pncand.mm"
include "adantlr.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "wss.mm"
include "wb.mm"
include "ssid.mm"
include "a1i.mm"
include "elcncf.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "rexralbidv.mm"
include "ralbidv.mm"
include "rspcva.mm"
include "adantrr.mm"
include "simprr.mm"
include "rspa.mm"
include "simpl1l.mm"
include "simp1rl.mm"
include "simplr.mm"
include "fvres.mm"
include "adantl.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "npcand.mm"
include "eqcomd.mm"
include "simpl.mm"
include "jca.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eqeq12d.mm"
include "chvarv.mm"
include "vtoclg.mm"
include "sylc.mm"
include "syl.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "syl3anc.mm"
include "jca31.mm"
include "simpld.mm"
include "nnncan2d.mm"
include "eqbrtrd.mm"
include "eleq1d.mm"
include "simpll3.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "3exp.mm"
include "reximdvai.mm"
include "ralrimivva.mm"
include "mpbir2and.mm"

theorem cncfperiod
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  let vk: setvar k
  assume cncfperiod.a: |- ( ph -> A C_ CC )
  assume cncfperiod.t: |- ( ph -> T e. RR )
  assume cncfperiod.b: |- B = { x e. CC | E. y e. A x = ( y + T ) }
  assume cncfperiod.f: |- ( ph -> F : dom F --> CC )
  assume cncfperiod.cssdmf: |- ( ph -> B C_ dom F )
  assume cncfperiod.fper: |- ( ( ph /\ x e. A ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume cncfperiod.fcn: |- ( ph -> ( F |` A ) e. ( A -cn-> CC ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint T x
  disjoint T y
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint A w
  disjoint A z
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A v
  disjoint b v
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint F a
  disjoint F b
  disjoint F w
  disjoint F z
  disjoint F v
  disjoint T a
  disjoint T b
  disjoint T w
  disjoint T z
  disjoint T v
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( F |` B ) e. ( B -cn-> CC ) )

  proof
    wph
    cF
    cB
    cres
    #
    cB
    cc
    ccncf
    co
    wcel
    #
    cB
    cc
    @0
    wf
    #
    vx
    cv
    #
    vv
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @3
    @0
    cfv
    #
    @4
    @0
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    cB
    wral
    #
    vz
    crp
    wrex
    #
    vw
    crp
    wral
    vx
    cB
    wral
    #
    wph
    cF
    cdm
    cc
    cB
    cF
    cncfperiod.f
    cncfperiod.cssdmf
    fssresd
    wph
    @17
    vx
    vw
    cB
    crp
    wph
    @3
    cB
    wcel
    #
    @13
    crp
    wcel
    #
    wa
    #
    wa
    #
    @3
    cT
    cmin
    co
    #
    vb
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @23
    cF
    cA
    cres
    #
    cfv
    #
    @24
    @28
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vb
    cA
    wral
    #
    vz
    crp
    wrex
    #
    @17
    @22
    @36
    vw
    crp
    wral
    #
    @20
    @36
    wph
    @19
    @37
    @20
    wph
    @19
    wa
    #
    @23
    cA
    wcel
    #
    va
    cv
    #
    @24
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @40
    @28
    cfv
    #
    @30
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    wi
    #
    vb
    cA
    wral
    vz
    crp
    wrex
    #
    vw
    crp
    wral
    #
    va
    cA
    wral
    #
    @37
    @38
    @3
    vy
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vy
    cA
    wrex
    #
    @39
    @38
    @3
    cc
    wcel
    #
    @55
    @38
    @3
    @55
    vx
    cc
    crab
    #
    wcel
    @56
    @55
    wa
    @38
    @3
    cB
    @57
    wph
    @19
    simpr
    cncfperiod.b
    syl6eleq
    @55
    vx
    cc
    rabid
    sylib
    #
    simprd
    @38
    @54
    @39
    vy
    cA
    @38
    @52
    cA
    wcel
    #
    @54
    w3a
    #
    @23
    @52
    cA
    @60
    @23
    @53
    cT
    cmin
    co
    #
    @52
    @54
    @38
    @23
    @61
    wceq
    @59
    @3
    @53
    cT
    cmin
    oveq1
    3ad2ant3
    @38
    @59
    @61
    @52
    wceq
    #
    @54
    wph
    @59
    @62
    @19
    wph
    @59
    wa
    #
    @52
    cT
    wph
    cA
    cc
    @52
    cncfperiod.a
    sselda
    wph
    cT
    cc
    wcel
    #
    @59
    wph
    cT
    cncfperiod.t
    recnd
    #
    adantr
    pncand
    adantlr
    3adant3
    eqtrd
    @38
    @59
    @54
    simp2
    eqeltrd
    rexlimdv3a
    mpd
    #
    @38
    cA
    cc
    @28
    wf
    #
    @51
    @38
    @28
    cA
    cc
    ccncf
    co
    wcel
    #
    @67
    @51
    wa
    #
    wph
    @68
    @19
    cncfperiod.fcn
    adantr
    @38
    cA
    cc
    wss
    #
    cc
    cc
    wss
    #
    @68
    @69
    wb
    wph
    @70
    @19
    cncfperiod.a
    adantr
    @71
    @38
    cc
    ssid
    #
    a1i
    va
    vw
    vz
    vb
    cA
    cc
    @28
    elcncf
    syl2anc
    mpbid
    simprd
    @50
    @37
    va
    @23
    cA
    @40
    @23
    wceq
    #
    @49
    @36
    vw
    crp
    @73
    @48
    @34
    vz
    vb
    crp
    cA
    @73
    @43
    @27
    @47
    @33
    @73
    @42
    @26
    @7
    clt
    @73
    @41
    @25
    cabs
    @40
    @23
    @24
    cmin
    oveq1
    fveq2d
    breq1d
    @73
    @46
    @32
    @13
    clt
    @73
    @45
    @31
    cabs
    @73
    @44
    @29
    @30
    cmin
    @40
    @23
    @28
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rexralbidv
    ralbidv
    rspcva
    syl2anc
    adantrr
    wph
    @19
    @20
    simprr
    @36
    vw
    crp
    rspa
    syl2anc
    @22
    @35
    @16
    vz
    crp
    @22
    @7
    crp
    wcel
    #
    @35
    @16
    @22
    @74
    @35
    w3a
    #
    @15
    vv
    cB
    @75
    @4
    cB
    wcel
    #
    wa
    #
    @8
    @14
    @77
    @8
    wa
    #
    @12
    @29
    @4
    cT
    cmin
    co
    #
    @28
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    clt
    @78
    wph
    @19
    @76
    @12
    @82
    wceq
    @77
    wph
    @8
    wph
    @21
    @74
    @35
    @76
    simpl1l
    adantr
    #
    @77
    @19
    @8
    @75
    @19
    @76
    @19
    @20
    wph
    @74
    @35
    simp1rl
    adantr
    adantr
    #
    @75
    @76
    @8
    simplr
    #
    wph
    @19
    @76
    w3a
    #
    @11
    @81
    cabs
    @86
    @9
    @29
    @10
    @80
    cmin
    wph
    @19
    @9
    @29
    wceq
    #
    @76
    @38
    @9
    @3
    cF
    cfv
    #
    @23
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @29
    @19
    @9
    @88
    wceq
    wph
    @3
    cB
    cF
    fvres
    adantl
    @38
    @3
    @89
    cF
    @38
    @89
    @3
    @38
    @3
    cT
    @19
    @56
    wph
    cB
    cc
    @3
    cB
    @57
    cc
    cncfperiod.b
    @55
    vx
    cc
    ssrab2
    eqsstri
    #
    sseli
    adantl
    wph
    @64
    @19
    @65
    adantr
    #
    npcand
    eqcomd
    fveq2d
    @38
    @90
    @23
    cF
    cfv
    #
    @29
    @38
    @39
    wph
    @39
    wa
    #
    @90
    @93
    wceq
    #
    @66
    @38
    wph
    @39
    wph
    @19
    simpl
    @66
    jca
    @63
    @53
    cF
    cfv
    #
    @52
    cF
    cfv
    #
    wceq
    #
    wi
    #
    @94
    @95
    wi
    vy
    @23
    cA
    @52
    @23
    wceq
    #
    @63
    @94
    @98
    @95
    @100
    @59
    @39
    wph
    @52
    @23
    cA
    eleq1
    anbi2d
    @100
    @96
    @90
    @97
    @93
    @100
    @53
    @89
    cF
    @52
    @23
    cT
    caddc
    oveq1
    fveq2d
    @52
    @23
    cF
    fveq2
    eqeq12d
    imbi12d
    wph
    @3
    cA
    wcel
    #
    wa
    #
    @3
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @88
    wceq
    #
    wi
    @99
    vx
    vy
    @3
    @52
    wceq
    #
    @102
    @63
    @105
    @98
    @106
    @101
    @59
    wph
    @3
    @52
    cA
    eleq1
    anbi2d
    @106
    @104
    @96
    @88
    @97
    @106
    @103
    @53
    cF
    @3
    @52
    cT
    caddc
    oveq1
    fveq2d
    @3
    @52
    cF
    fveq2
    eqeq12d
    imbi12d
    cncfperiod.fper
    chvarv
    vtoclg
    sylc
    @38
    @39
    @29
    @93
    wceq
    @66
    @23
    cA
    cF
    fvres
    syl
    eqtr4d
    3eqtrd
    #
    3adant3
    wph
    @76
    @10
    @80
    wceq
    #
    @19
    @38
    @87
    wi
    wph
    @76
    wa
    #
    @108
    wi
    vx
    vv
    @3
    @4
    wceq
    #
    @38
    @109
    @87
    @108
    @110
    @19
    @76
    wph
    @3
    @4
    cB
    eleq1
    anbi2d
    #
    @110
    @9
    @10
    @29
    @80
    @3
    @4
    @0
    fveq2
    @110
    @23
    @79
    @28
    @3
    @4
    cT
    cmin
    oveq1
    #
    fveq2d
    eqeq12d
    imbi12d
    @107
    chvarv
    3adant2
    oveq12d
    fveq2d
    syl3anc
    @78
    @23
    @79
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @82
    @13
    clt
    wbr
    #
    @78
    @38
    @76
    wa
    #
    @8
    @115
    @78
    wph
    @19
    @76
    @83
    @84
    @85
    jca31
    @77
    @8
    simpr
    @117
    @8
    wa
    @114
    @6
    @7
    clt
    @117
    @114
    @6
    wceq
    @8
    @117
    @113
    @5
    cabs
    @117
    @3
    @4
    cT
    @38
    @56
    @76
    @38
    @56
    @55
    @58
    simpld
    adantr
    @76
    @4
    cc
    wcel
    @38
    cB
    cc
    @4
    @91
    sseli
    adantl
    @38
    @64
    @76
    @92
    adantr
    nnncan2d
    fveq2d
    adantr
    @117
    @8
    simpr
    eqbrtrd
    syl2anc
    @78
    @79
    cA
    wcel
    #
    @35
    @115
    @116
    wi
    #
    @78
    wph
    @76
    @118
    @83
    @85
    @38
    @39
    wi
    @109
    @118
    wi
    vx
    vv
    @110
    @38
    @109
    @39
    @118
    @111
    @110
    @23
    @79
    cA
    @112
    eleq1d
    imbi12d
    @66
    chvarv
    syl2anc
    @22
    @74
    @35
    @76
    @8
    simpll3
    @34
    @119
    vb
    @79
    cA
    @24
    @79
    wceq
    #
    @27
    @115
    @33
    @116
    @120
    @26
    @114
    @7
    clt
    @120
    @25
    @113
    cabs
    @24
    @79
    @23
    cmin
    oveq2
    fveq2d
    breq1d
    @120
    @32
    @82
    @13
    clt
    @120
    @31
    @81
    cabs
    @120
    @30
    @80
    @29
    cmin
    @24
    @79
    @28
    fveq2
    oveq2d
    fveq2d
    breq1d
    imbi12d
    rspcva
    syl2anc
    mpd
    eqbrtrd
    ex
    ralrimiva
    3exp
    reximdvai
    mpd
    ralrimivva
    wph
    cB
    cc
    wss
    #
    @71
    @1
    @2
    @18
    wa
    wb
    @121
    wph
    @91
    a1i
    @71
    wph
    @72
    a1i
    vx
    vw
    vz
    vv
    cB
    cc
    @0
    elcncf
    syl2anc
    mpbir2and
end
