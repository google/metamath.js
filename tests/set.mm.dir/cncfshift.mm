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
include "wa.mm"
include "cncff.mm"
include "syl.mm"
include "adantr.mm"
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
include "pncand.mm"
include "adantlr.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "wss.mm"
include "wb.mm"
include "ssid.mm"
include "elcncf.mm"
include "sylancl.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "rexralbidv.mm"
include "ralbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "simprr.mm"
include "rspa.mm"
include "simpl1l.mm"
include "simp1rl.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "fvmpt2.mm"
include "cmpt.mm"
include "a1i.mm"
include "adantl.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "chvarv.mm"
include "fvmptd.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "syl3anc.mm"
include "jca31.mm"
include "simpld.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "nnncan2d.mm"
include "eqbrtrd.mm"
include "simpll3.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "3exp.mm"
include "reximdvai.mm"
include "ralrimivva.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfim.mm"
include "nfral.mm"
include "nfrex.mm"
include "cbvral.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "syl6bbr.mm"
include "mpbir2and.mm"

theorem cncfshift
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume cncfshift.a: |- ( ph -> A C_ CC )
  assume cncfshift.t: |- ( ph -> T e. CC )
  assume cncfshift.b: |- B = { x e. CC | E. y e. A x = ( y + T ) }
  assume cncfshift.f: |- ( ph -> F e. ( A -cn-> CC ) )
  assume cncfshift.g: |- G = ( x e. B |-> ( F ` ( x - T ) ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint T x
  disjoint T y
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint a b
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint B a
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint F a
  disjoint F b
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint G a
  disjoint G v
  disjoint G w
  disjoint G z
  disjoint T a
  disjoint T b
  disjoint T v
  disjoint T w
  disjoint T z
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> G e. ( B -cn-> CC ) )

  proof
    wph
    cG
    cB
    cc
    ccncf
    co
    wcel
    #
    cB
    cc
    cG
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
    @2
    cG
    cfv
    #
    @3
    cG
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
    #
    vx
    cB
    wral
    #
    wph
    vx
    cB
    @2
    cT
    cmin
    co
    #
    cF
    cfv
    #
    cc
    cG
    wph
    @2
    cB
    wcel
    #
    wa
    #
    cA
    cc
    @19
    cF
    wph
    cA
    cc
    cF
    wf
    #
    @21
    wph
    cF
    cA
    cc
    ccncf
    co
    wcel
    #
    @23
    cncfshift.f
    cA
    cc
    cF
    cncff
    syl
    #
    adantr
    @22
    @2
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
    @19
    cA
    wcel
    #
    @22
    @2
    cc
    wcel
    #
    @29
    @22
    @2
    @29
    vx
    cc
    crab
    #
    wcel
    @31
    @29
    wa
    @22
    @2
    cB
    @32
    wph
    @21
    simpr
    #
    cncfshift.b
    syl6eleq
    @29
    vx
    cc
    rabid
    sylib
    #
    simprd
    @22
    @28
    @30
    vy
    cA
    @22
    @26
    cA
    wcel
    #
    @28
    w3a
    #
    @19
    @26
    cA
    @36
    @19
    @27
    cT
    cmin
    co
    #
    @26
    @28
    @22
    @19
    @37
    wceq
    @35
    @2
    @27
    cT
    cmin
    oveq1
    3ad2ant3
    @22
    @35
    @37
    @26
    wceq
    #
    @28
    wph
    @35
    @38
    @21
    wph
    @35
    wa
    @26
    cT
    wph
    cA
    cc
    @26
    cncfshift.a
    sselda
    wph
    cT
    cc
    wcel
    #
    @35
    cncfshift.t
    adantr
    pncand
    adantlr
    3adant3
    eqtrd
    @22
    @35
    @28
    simp2
    eqeltrd
    rexlimdv3a
    mpd
    #
    ffvelrnd
    #
    cncfshift.g
    fmptd
    wph
    @16
    vx
    vw
    cB
    crp
    wph
    @21
    @12
    crp
    wcel
    #
    wa
    #
    wa
    #
    @19
    vb
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    @20
    @45
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @12
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
    @16
    @44
    @55
    vw
    crp
    wral
    #
    @42
    @55
    wph
    @21
    @56
    @42
    @22
    @30
    va
    cv
    #
    @45
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    @57
    cF
    cfv
    #
    @49
    cmin
    co
    #
    cabs
    cfv
    #
    @12
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
    @56
    @40
    @22
    @23
    @68
    @22
    @24
    @23
    @68
    wa
    #
    wph
    @24
    @21
    cncfshift.f
    adantr
    @22
    cA
    cc
    wss
    #
    cc
    cc
    wss
    #
    @24
    @69
    wb
    wph
    @70
    @21
    cncfshift.a
    adantr
    cc
    ssid
    #
    va
    vw
    vz
    vb
    cA
    cc
    cF
    elcncf
    sylancl
    mpbid
    simprd
    @67
    @56
    va
    @19
    cA
    @57
    @19
    wceq
    #
    @66
    @55
    vw
    crp
    @73
    @65
    @53
    vz
    vb
    crp
    cA
    @73
    @60
    @48
    @64
    @52
    @73
    @59
    @47
    @6
    clt
    @73
    @58
    @46
    cabs
    @57
    @19
    @45
    cmin
    oveq1
    fveq2d
    breq1d
    @73
    @63
    @51
    @12
    clt
    @73
    @62
    @50
    cabs
    @73
    @61
    @20
    @49
    cmin
    @57
    @19
    cF
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
    @21
    @42
    simprr
    @55
    vw
    crp
    rspa
    syl2anc
    @44
    @54
    @15
    vz
    crp
    @44
    @6
    crp
    wcel
    #
    @54
    @15
    @44
    @74
    @54
    w3a
    #
    @14
    vv
    cB
    @75
    @3
    cB
    wcel
    #
    wa
    #
    @7
    @13
    @77
    @7
    wa
    #
    @11
    @20
    @3
    cT
    cmin
    co
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    clt
    @78
    wph
    @21
    @76
    @11
    @82
    wceq
    @77
    wph
    @7
    wph
    @43
    @74
    @54
    @76
    simpl1l
    adantr
    #
    @75
    @21
    @76
    @7
    @21
    @42
    wph
    @74
    @54
    simp1rl
    ad2antrr
    #
    @75
    @76
    @7
    simplr
    #
    wph
    @21
    @76
    w3a
    #
    @10
    @81
    cabs
    @86
    @8
    @20
    @9
    @80
    cmin
    wph
    @21
    @8
    @20
    wceq
    #
    @76
    @22
    @21
    @20
    cc
    wcel
    @87
    @33
    @41
    vx
    cB
    @20
    cc
    cG
    cncfshift.g
    fvmpt2
    syl2anc
    3adant3
    wph
    @76
    @9
    @80
    wceq
    @21
    wph
    @76
    wa
    #
    vx
    @3
    @20
    @80
    cB
    cG
    cc
    cG
    vx
    cB
    @20
    cmpt
    #
    wceq
    @88
    cncfshift.g
    a1i
    @2
    @3
    wceq
    #
    @20
    @80
    wceq
    @88
    @90
    @19
    @79
    cF
    @2
    @3
    cT
    cmin
    oveq1
    #
    fveq2d
    adantl
    wph
    @76
    simpr
    @88
    cA
    cc
    @79
    cF
    wph
    @23
    @76
    @25
    adantr
    @22
    @30
    wi
    @88
    @79
    cA
    wcel
    #
    wi
    vx
    vv
    @90
    @22
    @88
    @30
    @92
    @90
    @21
    @76
    wph
    @2
    @3
    cB
    eleq1
    anbi2d
    @90
    @19
    @79
    cA
    @91
    eleq1d
    imbi12d
    @40
    chvarv
    #
    ffvelrnd
    fvmptd
    3adant2
    oveq12d
    fveq2d
    syl3anc
    @78
    @19
    @79
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    @82
    @12
    clt
    wbr
    #
    @78
    @22
    @76
    wa
    #
    @7
    @96
    @78
    wph
    @21
    @76
    @83
    @84
    @85
    jca31
    @77
    @7
    simpr
    @98
    @7
    wa
    @95
    @5
    @6
    clt
    @98
    @95
    @5
    wceq
    @7
    @98
    @94
    @4
    cabs
    @98
    @2
    @3
    cT
    @22
    @31
    @76
    @22
    @31
    @29
    @34
    simpld
    adantr
    @76
    @3
    cc
    wcel
    @22
    cB
    cc
    @3
    cB
    @32
    cc
    cncfshift.b
    @29
    vx
    cc
    ssrab2
    eqsstri
    #
    sseli
    adantl
    wph
    @39
    @21
    @76
    cncfshift.t
    ad2antrr
    nnncan2d
    fveq2d
    adantr
    @98
    @7
    simpr
    eqbrtrd
    syl2anc
    @78
    @92
    @54
    @96
    @97
    wi
    #
    @78
    wph
    @76
    @92
    @83
    @85
    @93
    syl2anc
    @44
    @74
    @54
    @76
    @7
    simpll3
    @53
    @100
    vb
    @79
    cA
    @45
    @79
    wceq
    #
    @48
    @96
    @52
    @97
    @101
    @47
    @95
    @6
    clt
    @101
    @46
    @94
    cabs
    @45
    @79
    @19
    cmin
    oveq2
    fveq2d
    breq1d
    @101
    @51
    @82
    @12
    clt
    @101
    @50
    @81
    cabs
    @101
    @49
    @80
    @20
    cmin
    @45
    @79
    cF
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
    @0
    @1
    @57
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    @57
    cG
    cfv
    #
    @9
    cmin
    co
    #
    cabs
    cfv
    #
    @12
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
    #
    va
    cB
    wral
    #
    wa
    #
    @1
    @18
    wa
    wph
    cB
    cc
    wss
    #
    @71
    @0
    @114
    wb
    @115
    wph
    @99
    a1i
    @72
    va
    vw
    vz
    vv
    cB
    cc
    cG
    elcncf
    sylancl
    @18
    @113
    @1
    @113
    @18
    @112
    @17
    va
    vx
    cB
    @111
    vx
    vw
    crp
    vx
    crp
    nfcv
    #
    @110
    vx
    vz
    crp
    @116
    @109
    vx
    vv
    cB
    vx
    cB
    nfcv
    @104
    @108
    vx
    @104
    vx
    nfv
    vx
    @107
    @12
    clt
    vx
    @106
    cabs
    vx
    cabs
    nfcv
    vx
    @105
    @9
    cmin
    vx
    @57
    cG
    vx
    cG
    @89
    cncfshift.g
    vx
    cB
    @20
    nfmpt1
    nfcxfr
    #
    vx
    @57
    nfcv
    nffv
    vx
    cmin
    nfcv
    vx
    @3
    cG
    @117
    vx
    @3
    nfcv
    nffv
    nfov
    nffv
    vx
    clt
    nfcv
    vx
    @12
    nfcv
    nfbr
    nfim
    nfral
    nfrex
    nfral
    @17
    va
    nfv
    @57
    @2
    wceq
    #
    @111
    @16
    vw
    crp
    @118
    @109
    @14
    vz
    vv
    crp
    cB
    @118
    @104
    @7
    @108
    @13
    @118
    @103
    @5
    @6
    clt
    @118
    @102
    @4
    cabs
    @57
    @2
    @3
    cmin
    oveq1
    fveq2d
    breq1d
    @118
    @107
    @11
    @12
    clt
    @118
    @106
    @10
    cabs
    @118
    @105
    @8
    @9
    cmin
    @57
    @2
    cG
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rexralbidv
    ralbidv
    cbvral
    bicomi
    anbi2i
    syl6bbr
    mpbir2and
end
