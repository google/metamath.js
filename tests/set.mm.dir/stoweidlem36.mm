include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "cle.mm"
include "c1.mm"
include "wral.mm"
include "crab.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cmul.mm"
include "cr.mm"
include "ccn.mm"
include "eqid.mm"
include "nfeq2.mm"
include "stoweidlem6.mm"
include "mpd3an23.mm"
include "syl5eqel.mm"
include "sseldd.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "cc.mm"
include "crn.mm"
include "csup.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"
include "cncmpmax.mm"
include "simp2d.mm"
include "adantr.mm"
include "0red.mm"
include "ffvelrnd.mm"
include "neeqtrd.mm"
include "msqgt0d.mm"
include "remulcld.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "simp3d.mm"
include "breq1d.mm"
include "rspccva.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "divrecd.mm"
include "simpr.mm"
include "rereccld.mm"
include "fvmpt2.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "mpteq2da.mm"
include "syl5eq.mm"
include "stoweidlem4.mm"
include "mpdan.mm"
include "nfmpt1.mm"
include "eqeltrd.mm"
include "redivcld.mm"
include "oveq1d.mm"
include "0re.mm"
include "syl6eqel.mm"
include "0cn.mm"
include "mul02i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "div0d.mm"
include "3eqtrd.mm"
include "msqge0d.mm"
include "syl6breqr.mm"
include "divge0.mm"
include "syl22anc.mm"
include "div1d.mm"
include "sylan.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "lediv23.mm"
include "syl122anc.mm"
include "mpbird.mm"
include "jca.mm"
include "ex.mm"
include "ralrimi.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "divgt0d.mm"
include "nfel2.mm"
include "nfv.mm"
include "nfan.mm"
include "eleq1.mm"
include "spcegf.mm"
include "anabsi5.mm"

theorem stoweidlem36
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cN: class N
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem36.1: |- F/_ h Q
  assume stoweidlem36.2: |- F/_ t H
  assume stoweidlem36.3: |- F/_ t F
  assume stoweidlem36.4: |- F/_ t G
  assume stoweidlem36.5: |- F/ t ph
  assume stoweidlem36.6: |- K = ( topGen ` ran (,) )
  assume stoweidlem36.7: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem36.8: |- T = U. J
  assume stoweidlem36.9: |- G = ( t e. T |-> ( ( F ` t ) x. ( F ` t ) ) )
  assume stoweidlem36.10: |- N = sup ( ran G , RR , < )
  assume stoweidlem36.11: |- H = ( t e. T |-> ( ( G ` t ) / N ) )
  assume stoweidlem36.12: |- ( ph -> J e. Comp )
  assume stoweidlem36.13: |- ( ph -> A C_ ( J Cn K ) )
  assume stoweidlem36.14: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem36.15: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem36.16: |- ( ph -> S e. T )
  assume stoweidlem36.17: |- ( ph -> Z e. T )
  assume stoweidlem36.18: |- ( ph -> F e. A )
  assume stoweidlem36.19: |- ( ph -> ( F ` S ) =/= ( F ` Z ) )
  assume stoweidlem36.20: |- ( ph -> ( F ` Z ) = 0 )

  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint A f
  disjoint A g
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint f ph
  disjoint g ph
  disjoint N g
  disjoint N t
  disjoint h t
  disjoint S h
  disjoint S t
  disjoint A h
  disjoint H h
  disjoint T h
  disjoint Z h
  disjoint Z t
  disjoint t x
  disjoint N x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint s t
  disjoint S s
  disjoint G s
  disjoint J s
  disjoint K s
  disjoint T s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> E. h ( h e. Q /\ 0 < ( h ` S ) ) )

  proof
    wph
    cH
    cQ
    wcel
    #
    cc0
    cS
    cH
    cfv
    #
    clt
    wbr
    #
    vh
    cv
    #
    cQ
    wcel
    #
    cc0
    cS
    @3
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vh
    wex
    #
    wph
    cH
    cZ
    @3
    cfv
    #
    cc0
    wceq
    #
    cc0
    vt
    cv
    #
    @3
    cfv
    #
    cle
    wbr
    #
    @12
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    wa
    #
    vh
    cA
    crab
    #
    cQ
    wph
    cH
    cA
    wcel
    cZ
    cH
    cfv
    #
    cc0
    wceq
    #
    cc0
    @11
    cH
    cfv
    #
    cle
    wbr
    #
    @21
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    wa
    #
    cH
    @18
    wcel
    wph
    cH
    vt
    cT
    @11
    cG
    cfv
    #
    @11
    vt
    cT
    c1
    cN
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cA
    wph
    cH
    vt
    cT
    @27
    cN
    cdiv
    co
    #
    cmpt
    @32
    stoweidlem36.11
    wph
    vt
    cT
    @33
    @31
    stoweidlem36.5
    wph
    @11
    cT
    wcel
    #
    wa
    #
    @33
    @27
    @28
    cmul
    co
    @31
    @35
    @27
    cN
    @35
    @27
    wph
    cT
    cr
    @11
    cG
    wph
    cJ
    cK
    ccn
    co
    #
    cT
    cG
    cJ
    cK
    stoweidlem36.6
    stoweidlem36.8
    @36
    eqid
    #
    wph
    cA
    @36
    cG
    stoweidlem36.13
    wph
    cG
    vt
    cT
    @11
    cF
    cfv
    #
    @38
    cmul
    co
    #
    cmpt
    #
    cA
    stoweidlem36.9
    wph
    cF
    cA
    wcel
    #
    @41
    @40
    cA
    wcel
    stoweidlem36.18
    stoweidlem36.18
    wph
    vt
    cA
    cT
    vf
    vg
    cF
    cF
    vt
    vf
    cv
    #
    cF
    stoweidlem36.3
    nfeq2
    vt
    vg
    cv
    #
    cF
    stoweidlem36.3
    nfeq2
    stoweidlem36.14
    stoweidlem6
    mpd3an23
    syl5eqel
    #
    sseldd
    #
    fcnre
    #
    ffvelrnda
    #
    recnd
    #
    wph
    cN
    cc
    wcel
    @34
    wph
    cN
    wph
    cN
    cG
    crn
    #
    cr
    clt
    csup
    #
    cr
    stoweidlem36.10
    wph
    @50
    @49
    wcel
    #
    @50
    cr
    wcel
    #
    vs
    cv
    #
    cG
    cfv
    #
    @50
    cle
    wbr
    #
    vs
    cT
    wral
    #
    wph
    vs
    cT
    cG
    cJ
    cK
    stoweidlem36.8
    stoweidlem36.6
    stoweidlem36.12
    @45
    wph
    cS
    cT
    wcel
    #
    cT
    c0
    wne
    stoweidlem36.16
    cT
    cS
    ne0i
    syl
    cncmpmax
    #
    simp2d
    #
    syl5eqel
    #
    recnd
    #
    adantr
    wph
    cN
    cc0
    wne
    #
    @34
    wph
    @50
    cc0
    wne
    @62
    wph
    @50
    wph
    cc0
    cS
    cG
    cfv
    #
    @50
    wph
    0red
    wph
    cT
    cr
    cS
    cG
    @46
    stoweidlem36.16
    ffvelrnd
    #
    @59
    wph
    cc0
    cS
    cF
    cfv
    #
    @65
    cmul
    co
    #
    @63
    clt
    wph
    @65
    wph
    cT
    cr
    cS
    cF
    wph
    @36
    cT
    cF
    cJ
    cK
    stoweidlem36.6
    stoweidlem36.8
    @37
    wph
    cA
    @36
    cF
    stoweidlem36.13
    stoweidlem36.18
    sseldd
    fcnre
    #
    stoweidlem36.16
    ffvelrnd
    #
    wph
    @65
    cZ
    cF
    cfv
    #
    cc0
    stoweidlem36.19
    stoweidlem36.20
    neeqtrd
    msqgt0d
    wph
    @57
    @66
    cr
    wcel
    @63
    @66
    wceq
    stoweidlem36.16
    wph
    @65
    @65
    @68
    @68
    remulcld
    vt
    cS
    @39
    @66
    cT
    cG
    cr
    vt
    cS
    nfcv
    #
    vt
    @65
    @65
    cmul
    vt
    cS
    cF
    stoweidlem36.3
    @70
    nffv
    #
    vt
    cmul
    nfcv
    #
    @71
    nfov
    @11
    cS
    wceq
    #
    @38
    @65
    @38
    @65
    cmul
    @11
    cS
    cF
    fveq2
    #
    @74
    oveq12d
    stoweidlem36.9
    fvmptf
    syl2anc
    breqtrrd
    #
    wph
    @56
    @57
    @63
    @50
    cle
    wbr
    #
    wph
    @51
    @52
    @56
    @58
    simp3d
    #
    stoweidlem36.16
    @55
    @76
    vs
    cS
    cT
    @53
    cS
    wceq
    @54
    @63
    @50
    cle
    @53
    cS
    cG
    fveq2
    breq1d
    rspccva
    syl2anc
    ltletrd
    #
    gt0ne0d
    cN
    @50
    cc0
    stoweidlem36.10
    neeq1i
    sylibr
    #
    adantr
    #
    divrecd
    @35
    @30
    @28
    @27
    cmul
    @35
    @34
    @28
    cr
    wcel
    #
    @30
    @28
    wceq
    wph
    @34
    simpr
    #
    wph
    @81
    @34
    wph
    cN
    @60
    @79
    rereccld
    #
    adantr
    vt
    cT
    @28
    cr
    @29
    @29
    eqid
    fvmpt2
    syl2anc
    oveq2d
    eqtr4d
    mpteq2da
    syl5eq
    wph
    cG
    cA
    wcel
    @29
    cA
    wcel
    #
    @32
    cA
    wcel
    @44
    wph
    @81
    @84
    @83
    wph
    vx
    vt
    cA
    @28
    cT
    stoweidlem36.15
    stoweidlem4
    mpdan
    wph
    vt
    cA
    cT
    vf
    vg
    cG
    @29
    vt
    @42
    cG
    stoweidlem36.4
    nfeq2
    vt
    @43
    @29
    vt
    cT
    @28
    nfmpt1
    nfeq2
    stoweidlem36.14
    stoweidlem6
    mpd3an23
    eqeltrd
    wph
    @20
    @25
    wph
    @19
    cZ
    cG
    cfv
    #
    cN
    cdiv
    co
    #
    cc0
    cN
    cdiv
    co
    cc0
    wph
    cZ
    cT
    wcel
    #
    @86
    cr
    wcel
    @19
    @86
    wceq
    stoweidlem36.17
    wph
    @85
    cN
    wph
    cT
    cr
    cZ
    cG
    @46
    stoweidlem36.17
    ffvelrnd
    @60
    @79
    redivcld
    vt
    cZ
    @33
    @86
    cT
    cH
    cr
    vt
    cZ
    nfcv
    #
    vt
    @85
    cN
    cdiv
    vt
    cZ
    cG
    stoweidlem36.4
    @88
    nffv
    vt
    cdiv
    nfcv
    #
    vt
    cN
    nfcv
    #
    nfov
    @11
    cZ
    wceq
    #
    @27
    @85
    cN
    cdiv
    @11
    cZ
    cG
    fveq2
    oveq1d
    stoweidlem36.11
    fvmptf
    syl2anc
    wph
    @85
    cc0
    cN
    cdiv
    wph
    @85
    @69
    @69
    cmul
    co
    #
    cc0
    wph
    @87
    @92
    cr
    wcel
    @85
    @92
    wceq
    stoweidlem36.17
    wph
    @69
    @69
    wph
    @69
    cc0
    cr
    stoweidlem36.20
    0re
    syl6eqel
    #
    @93
    remulcld
    vt
    cZ
    @39
    @92
    cT
    cG
    cr
    @88
    vt
    @69
    @69
    cmul
    vt
    cZ
    cF
    stoweidlem36.3
    @88
    nffv
    #
    @72
    @94
    nfov
    @91
    @38
    @69
    @38
    @69
    cmul
    @11
    cZ
    cF
    fveq2
    #
    @95
    oveq12d
    stoweidlem36.9
    fvmptf
    syl2anc
    wph
    @92
    cc0
    cc0
    cmul
    co
    cc0
    wph
    @69
    cc0
    @69
    cc0
    cmul
    stoweidlem36.20
    stoweidlem36.20
    oveq12d
    cc0
    0cn
    mul02i
    syl6eq
    eqtrd
    oveq1d
    wph
    cN
    @61
    @79
    div0d
    3eqtrd
    wph
    @24
    vt
    cT
    stoweidlem36.5
    wph
    @34
    @24
    @35
    @22
    @23
    @35
    cc0
    @33
    @21
    cle
    @35
    @27
    cr
    wcel
    #
    cc0
    @27
    cle
    wbr
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    cc0
    @33
    cle
    wbr
    @47
    @35
    cc0
    @39
    @27
    cle
    @35
    @38
    wph
    cT
    cr
    @11
    cF
    @67
    ffvelrnda
    #
    msqge0d
    @35
    @34
    @39
    cr
    wcel
    @27
    @39
    wceq
    @82
    @35
    @38
    @38
    @99
    @99
    remulcld
    vt
    cT
    @39
    cr
    cG
    stoweidlem36.9
    fvmpt2
    syl2anc
    breqtrrd
    wph
    @97
    @34
    @60
    adantr
    #
    wph
    @98
    @34
    wph
    cc0
    @50
    cN
    clt
    @78
    stoweidlem36.10
    syl6breqr
    #
    adantr
    #
    @27
    cN
    divge0
    syl22anc
    @35
    @34
    @33
    cr
    wcel
    @21
    @33
    wceq
    @82
    @35
    @27
    cN
    @47
    @100
    @80
    redivcld
    vt
    cT
    @33
    cr
    cH
    stoweidlem36.11
    fvmpt2
    syl2anc
    #
    breqtrrd
    @35
    @21
    @33
    c1
    cle
    @103
    @35
    @33
    c1
    cle
    wbr
    #
    @27
    c1
    cdiv
    co
    #
    cN
    cle
    wbr
    #
    @35
    @105
    @27
    cN
    cle
    @35
    @27
    @48
    div1d
    @35
    @27
    @50
    cN
    cle
    wph
    @56
    @34
    @27
    @50
    cle
    wbr
    #
    @77
    @55
    @107
    vs
    @11
    cT
    @53
    @11
    wceq
    @54
    @27
    @50
    cle
    @53
    @11
    cG
    fveq2
    breq1d
    rspccva
    sylan
    stoweidlem36.10
    syl6breqr
    eqbrtrd
    @35
    @96
    @97
    @98
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @104
    @106
    wb
    @47
    @100
    @102
    @35
    1red
    @108
    @35
    0lt1
    a1i
    @27
    cN
    c1
    lediv23
    syl122anc
    mpbird
    eqbrtrd
    jca
    ex
    ralrimi
    jca
    @17
    @26
    vh
    cH
    cA
    @3
    cH
    wceq
    #
    @10
    @20
    @16
    @25
    @109
    @9
    @19
    cc0
    cZ
    @3
    cH
    fveq1
    eqeq1d
    @109
    @15
    @24
    vt
    cT
    vt
    @3
    cH
    stoweidlem36.2
    nfeq2
    @109
    @13
    @22
    @14
    @23
    @109
    @12
    @21
    cc0
    cle
    @11
    @3
    cH
    fveq1
    #
    breq2d
    @109
    @12
    @21
    c1
    cle
    @110
    breq1d
    anbi12d
    ralbid
    anbi12d
    elrab
    sylanbrc
    stoweidlem36.7
    syl6eleqr
    wph
    cc0
    @63
    cN
    cdiv
    co
    #
    @1
    clt
    wph
    @63
    cN
    @64
    @60
    @75
    @101
    divgt0d
    wph
    @57
    @111
    cr
    wcel
    @1
    @111
    wceq
    stoweidlem36.16
    wph
    @63
    cN
    @64
    @60
    @79
    redivcld
    vt
    cS
    @33
    @111
    cT
    cH
    cr
    @70
    vt
    @63
    cN
    cdiv
    vt
    cS
    cG
    stoweidlem36.4
    @70
    nffv
    @89
    @90
    nfov
    @73
    @27
    @63
    cN
    cdiv
    @11
    cS
    cG
    fveq2
    oveq1d
    stoweidlem36.11
    fvmptf
    syl2anc
    breqtrrd
    @0
    @2
    @8
    @7
    @0
    @2
    wa
    vh
    cH
    cQ
    vh
    cH
    nfcv
    @0
    @2
    vh
    vh
    cH
    cQ
    stoweidlem36.1
    nfel2
    @2
    vh
    nfv
    nfan
    @109
    @4
    @0
    @6
    @2
    @3
    cH
    cQ
    eleq1
    @109
    @5
    @1
    cc0
    clt
    cS
    @3
    cH
    fveq1
    breq2d
    anbi12d
    spcegf
    anabsi5
    syl2anc
end
