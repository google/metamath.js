include "cuz.mm"
include "cfv.mm"
include "eqid.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cdv.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "crab.mm"
include "ssrab2.mm"
include "cinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "rpre.mm"
include "adantl.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "cle.mm"
include "c2.mm"
include "ioomidp.mm"
include "syl3anc.mm"
include "ne0i.mm"
include "cc.mm"
include "cdm.mm"
include "ioossre.mm"
include "a1i.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "abscld.mm"
include "suprnmpt.mm"
include "simpld.mm"
include "syl5eqel.mm"
include "peano2re.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "readdcld.mm"
include "ltp1d.mm"
include "absge0d.mm"
include "simprd.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "breq1d.mm"
include "rspcva.mm"
include "letrd.mm"
include "leadd1dd.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "rpgt0.mm"
include "divgt0d.mm"
include "elrpd.mm"
include "cz.mm"
include "cli.mm"
include "climcau.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "rabn0.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "sseldi.mm"
include "uzss.mm"
include "sselda.mm"
include "ad2antrr.mm"
include "fvmptd.mm"
include "oveq12d.mm"
include "cmul.mm"
include "recnd.mm"
include "subcld.mm"
include "resubcld.mm"
include "remulcld.mm"
include "ad3antlr.mm"
include "abssubd.mm"
include "ad3antrrr.mm"
include "cxr.mm"
include "rexrd.mm"
include "simpr.mm"
include "iooltub.mm"
include "eliood.mm"
include "dvbdfbdioolem1.mm"
include "eqbrtrd.mm"
include "posdifd.mm"
include "ltmul1dd.mm"
include "leabsd.mm"
include "breqtrd.mm"
include "oveq2d.mm"
include "raleqbidv.mm"
include "elrab.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "lelttrd.mm"
include "ltmuldiv2d.mm"
include "mpbird.mm"
include "lttrd.mm"
include "wn.mm"
include "oveq1d.mm"
include "subidd.mm"
include "sylan9eqr.mm"
include "abs00bd.mm"
include "adantlr.mm"
include "simpll.mm"
include "id.mm"
include "eqcomd.mm"
include "necon3bi.mm"
include "simplr.mm"
include "lttri5d.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "rspcev.mm"
include "caurcvg.mm"

theorem ioodvbdlimc1lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cM: class M
  let vw: setvar w
  assume ioodvbdlimc1lem1.a: |- ( ph -> A e. RR )
  assume ioodvbdlimc1lem1.b: |- ( ph -> B e. RR )
  assume ioodvbdlimc1lem1.altb: |- ( ph -> A < B )
  assume ioodvbdlimc1lem1.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> RR ) )
  assume ioodvbdlimc1lem1.dmdv: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume ioodvbdlimc1lem1.dvbd: |- ( ph -> E. y e. RR A. x e. ( A (,) B ) ( abs ` ( ( RR _D F ) ` x ) ) <_ y )
  assume ioodvbdlimc1lem1.m: |- ( ph -> M e. ZZ )
  assume ioodvbdlimc1lem1.r: |- ( ph -> R : ( ZZ>= ` M ) --> ( A (,) B ) )
  assume ioodvbdlimc1lem1.s: |- S = ( j e. ( ZZ>= ` M ) |-> ( F ` ( R ` j ) ) )
  assume ioodvbdlimc1lem1.rcnv: |- ( ph -> R e. dom ~~> )
  assume ioodvbdlimc1lem1.k: |- K = inf ( { k e. ( ZZ>= ` M ) | A. i e. ( ZZ>= ` k ) ( abs ` ( ( R ` i ) - ( R ` k ) ) ) < ( x / ( sup ( ran ( z e. ( A (,) B ) |-> ( abs ` ( ( RR _D F ) ` z ) ) ) , RR , < ) + 1 ) ) } , RR , < )

  disjoint A i
  disjoint A k
  disjoint A x
  disjoint A z
  disjoint i k
  disjoint i x
  disjoint i z
  disjoint k x
  disjoint k z
  disjoint x z
  disjoint A y
  disjoint i y
  disjoint x y
  disjoint y z
  disjoint B i
  disjoint B k
  disjoint B x
  disjoint B z
  disjoint B y
  disjoint F i
  disjoint F j
  disjoint F x
  disjoint i j
  disjoint j x
  disjoint F k
  disjoint F z
  disjoint F y
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K y
  disjoint M i
  disjoint M j
  disjoint M x
  disjoint M k
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R y
  disjoint S i
  disjoint S k
  disjoint S x
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint k ph
  disjoint ph y
  disjoint k x
  disjoint A w
  disjoint i w
  disjoint k w
  disjoint w x
  disjoint w z
  disjoint B w
  disjoint F w
  disjoint M w
  disjoint R w
  assert |- ( ph -> S ~~> ( limsup ` S ) )

  proof
    wph
    vx
    vi
    vk
    cS
    cM
    cM
    cuz
    cfv
    #
    @0
    eqid
    #
    wph
    vj
    @0
    vj
    cv
    #
    cR
    cfv
    #
    cF
    cfv
    #
    cr
    cS
    wph
    @2
    @0
    wcel
    #
    wa
    cA
    cB
    cioo
    co
    #
    cr
    @3
    cF
    wph
    @6
    cr
    cF
    wf
    #
    @5
    wph
    cF
    @6
    cr
    ccncf
    co
    wcel
    @7
    ioodvbdlimc1lem1.f
    @6
    cr
    cF
    cncff
    syl
    #
    adantr
    wph
    @0
    @6
    @2
    cR
    ioodvbdlimc1lem1.r
    ffvelrnda
    ffvelrnd
    ioodvbdlimc1lem1.s
    fmptd
    wph
    vi
    cv
    #
    cS
    cfv
    #
    vk
    cv
    #
    cS
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vi
    @11
    cuz
    cfv
    #
    wral
    #
    vk
    @0
    wrex
    #
    vx
    crp
    wph
    @15
    crp
    wcel
    #
    wa
    #
    cK
    @0
    wcel
    #
    @10
    cK
    cS
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    vi
    cK
    cuz
    cfv
    #
    wral
    #
    @19
    @21
    @9
    cR
    cfv
    #
    @11
    cR
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    vz
    @6
    vz
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vi
    @17
    wral
    #
    vk
    @0
    crab
    #
    @0
    cK
    @43
    vk
    @0
    ssrab2
    #
    @21
    cK
    @44
    cr
    clt
    cinf
    #
    @44
    ioodvbdlimc1lem1.k
    @21
    @44
    @0
    wss
    @44
    c0
    wne
    #
    @46
    @44
    wcel
    @45
    @21
    @43
    vk
    @0
    wrex
    #
    @47
    @21
    @41
    crp
    wcel
    @32
    vw
    cv
    #
    clt
    wbr
    #
    vi
    @17
    wral
    vk
    @0
    wrex
    #
    vw
    crp
    wral
    #
    @48
    @21
    @41
    @21
    @15
    @40
    @20
    @15
    cr
    wcel
    #
    wph
    @15
    rpre
    #
    adantl
    #
    @21
    @39
    cr
    wcel
    #
    @40
    cr
    wcel
    #
    wph
    @56
    @20
    wph
    @39
    vx
    @6
    @15
    @34
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cr
    cr
    @38
    @61
    clt
    @37
    @60
    vz
    vx
    @6
    @36
    @59
    @33
    @15
    wceq
    @35
    @58
    cabs
    @33
    @15
    @34
    fveq2
    fveq2d
    cbvmptv
    rneqi
    supeq1i
    #
    wph
    @62
    cr
    wcel
    #
    @59
    @62
    cle
    wbr
    #
    vx
    @6
    wral
    #
    wph
    vx
    vy
    @6
    @59
    @62
    @60
    wph
    cA
    cB
    caddc
    co
    c2
    cdiv
    co
    #
    @6
    wcel
    #
    @6
    c0
    wne
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    @68
    ioodvbdlimc1lem1.a
    ioodvbdlimc1lem1.b
    ioodvbdlimc1lem1.altb
    cA
    cB
    ioomidp
    syl3anc
    #
    @6
    @67
    ne0i
    syl
    wph
    @15
    @6
    wcel
    wa
    @58
    wph
    @6
    cc
    @15
    @34
    wph
    @6
    cr
    cc
    @34
    wph
    @34
    cdm
    #
    cr
    @34
    wf
    #
    @6
    cr
    @34
    wf
    wph
    @7
    @6
    cr
    wss
    #
    @73
    @8
    @74
    wph
    cA
    cB
    ioossre
    #
    a1i
    @6
    cF
    dvfre
    syl2anc
    wph
    @72
    @6
    cr
    @34
    ioodvbdlimc1lem1.dmdv
    feq2d
    mpbid
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    #
    ffvelrnda
    abscld
    ioodvbdlimc1lem1.dvbd
    @60
    eqid
    @62
    eqid
    suprnmpt
    #
    simpld
    syl5eqel
    #
    adantr
    @39
    peano2re
    #
    syl
    #
    wph
    @40
    cc0
    wne
    @20
    wph
    @40
    wph
    cc0
    cc0
    c1
    caddc
    co
    @40
    wph
    0red
    #
    wph
    cc0
    c1
    @81
    wph
    1red
    #
    readdcld
    wph
    @56
    @57
    @78
    @79
    syl
    #
    wph
    cc0
    @81
    ltp1d
    wph
    cc0
    @39
    c1
    @81
    @78
    @82
    wph
    cc0
    @67
    @34
    cfv
    #
    cabs
    cfv
    #
    @39
    @81
    wph
    @84
    wph
    @6
    cc
    @67
    @34
    @76
    @71
    ffvelrnd
    #
    abscld
    @78
    wph
    @84
    @86
    absge0d
    wph
    @68
    vy
    cv
    #
    @34
    cfv
    #
    cabs
    cfv
    #
    @39
    cle
    wbr
    #
    vy
    @6
    wral
    #
    @85
    @39
    cle
    wbr
    #
    @71
    wph
    @66
    @91
    wph
    @64
    @66
    @77
    simprd
    @90
    @65
    vy
    vx
    @6
    @87
    @15
    wceq
    #
    @89
    @59
    @39
    @62
    cle
    @93
    @88
    @58
    cabs
    @87
    @15
    @34
    fveq2
    fveq2d
    @39
    @62
    wceq
    @93
    @63
    a1i
    breq12d
    cbvralv
    sylibr
    #
    @90
    @92
    vy
    @67
    @6
    @87
    @67
    wceq
    #
    @89
    @85
    @39
    cle
    @95
    @88
    @84
    cabs
    @87
    @67
    @34
    fveq2
    fveq2d
    breq1d
    rspcva
    syl2anc
    letrd
    leadd1dd
    ltletrd
    #
    gt0ne0d
    adantr
    redivcld
    #
    @21
    @15
    @40
    @55
    @80
    @20
    cc0
    @15
    clt
    wbr
    #
    wph
    @15
    rpgt0
    #
    adantl
    wph
    cc0
    @40
    clt
    wbr
    @20
    @96
    adantr
    divgt0d
    elrpd
    @21
    cM
    cz
    wcel
    #
    cR
    cli
    cdm
    wcel
    #
    @52
    wph
    @100
    @20
    ioodvbdlimc1lem1.m
    adantr
    wph
    @101
    @20
    ioodvbdlimc1lem1.rcnv
    adantr
    vw
    vk
    vi
    cR
    cM
    @0
    @1
    climcau
    syl2anc
    @51
    @48
    vw
    @41
    crp
    @49
    @41
    wceq
    @50
    @42
    vk
    vi
    @0
    @17
    @49
    @41
    @32
    clt
    breq2
    rexralbidv
    rspcva
    syl2anc
    @43
    vk
    @0
    rabn0
    sylibr
    @44
    cM
    infssuzcl
    sylancr
    syl5eqel
    #
    sseldi
    #
    @21
    @26
    vi
    @27
    @21
    @9
    @27
    wcel
    #
    wa
    #
    @25
    @29
    cF
    cfv
    #
    cK
    cR
    cfv
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
    @15
    clt
    @105
    @24
    @109
    cabs
    @105
    @10
    @106
    @23
    @108
    cmin
    @105
    vj
    @9
    @4
    @106
    @0
    cS
    cr
    cS
    vj
    @0
    @4
    cmpt
    wceq
    @105
    ioodvbdlimc1lem1.s
    a1i
    #
    @2
    @9
    wceq
    #
    @4
    @106
    wceq
    @105
    @112
    @3
    @29
    cF
    @2
    @9
    cR
    fveq2
    fveq2d
    adantl
    @21
    @27
    @0
    @9
    @21
    @22
    @27
    @0
    wss
    @103
    cM
    cK
    uzss
    syl
    sselda
    #
    @105
    @6
    cr
    @29
    cF
    wph
    @7
    @20
    @104
    @8
    ad2antrr
    #
    @105
    @0
    @6
    @9
    cR
    wph
    @0
    @6
    cR
    wf
    #
    @20
    @104
    ioodvbdlimc1lem1.r
    ad2antrr
    #
    @113
    ffvelrnd
    #
    ffvelrnd
    #
    fvmptd
    @105
    vj
    cK
    @4
    @108
    @0
    cS
    cr
    @111
    @2
    cK
    wceq
    #
    @4
    @108
    wceq
    @105
    @119
    @3
    @107
    cF
    @2
    cK
    cR
    fveq2
    fveq2d
    adantl
    @21
    @22
    @104
    @103
    adantr
    #
    @105
    @6
    cr
    @107
    cF
    @114
    @105
    @0
    @6
    cK
    cR
    @116
    @120
    ffvelrnd
    #
    ffvelrnd
    #
    fvmptd
    oveq12d
    fveq2d
    @105
    @29
    @107
    clt
    wbr
    #
    @110
    @15
    clt
    wbr
    #
    @105
    @123
    wa
    #
    @110
    @39
    @107
    @29
    cmin
    co
    #
    cmul
    co
    #
    @15
    @105
    @110
    cr
    wcel
    #
    @123
    @105
    @109
    @105
    @106
    @108
    @105
    @106
    @118
    recnd
    #
    @105
    @108
    @122
    recnd
    #
    subcld
    abscld
    #
    adantr
    @125
    @39
    @126
    @105
    @56
    @123
    wph
    @56
    @20
    @104
    @78
    ad2antrr
    #
    adantr
    #
    @125
    @107
    @29
    @21
    @107
    cr
    wcel
    #
    @104
    @123
    @21
    @6
    cr
    @107
    @75
    @21
    @0
    @6
    cK
    cR
    wph
    @115
    @20
    ioodvbdlimc1lem1.r
    adantr
    @103
    ffvelrnd
    #
    sseldi
    #
    ad2antrr
    #
    @105
    @29
    cr
    wcel
    #
    @123
    @105
    @6
    cr
    @29
    @75
    @117
    sseldi
    #
    adantr
    #
    resubcld
    #
    remulcld
    #
    @20
    @53
    wph
    @104
    @123
    @54
    ad3antlr
    #
    @125
    @110
    @108
    @106
    cmin
    co
    cabs
    cfv
    #
    @127
    cle
    @125
    @106
    @108
    @105
    @106
    cc
    wcel
    @123
    @129
    adantr
    @105
    @108
    cc
    wcel
    @123
    @130
    adantr
    abssubd
    @125
    @144
    @127
    cle
    wbr
    @144
    @39
    cB
    cA
    cmin
    co
    cmul
    co
    #
    cle
    wbr
    @125
    vy
    cA
    cB
    @29
    @107
    cF
    @39
    wph
    @69
    @20
    @104
    @123
    ioodvbdlimc1lem1.a
    ad3antrrr
    wph
    @70
    @20
    @104
    @123
    ioodvbdlimc1lem1.b
    ad3antrrr
    @105
    @7
    @123
    @114
    adantr
    wph
    @72
    @6
    wceq
    #
    @20
    @104
    @123
    ioodvbdlimc1lem1.dmdv
    ad3antrrr
    @133
    wph
    @91
    @20
    @104
    @123
    @94
    ad3antrrr
    @105
    @29
    @6
    wcel
    #
    @123
    @117
    adantr
    @125
    @29
    cB
    @107
    @105
    @29
    cxr
    wcel
    @123
    @105
    @29
    @139
    rexrd
    adantr
    @105
    cB
    cxr
    wcel
    #
    @123
    wph
    @148
    @20
    @104
    wph
    cB
    ioodvbdlimc1lem1.b
    rexrd
    #
    ad2antrr
    #
    adantr
    @137
    @105
    @123
    simpr
    #
    @21
    @107
    cB
    clt
    wbr
    #
    @104
    @123
    @21
    cA
    cxr
    wcel
    #
    @148
    @107
    @6
    wcel
    #
    @152
    wph
    @153
    @20
    wph
    cA
    ioodvbdlimc1lem1.a
    rexrd
    #
    adantr
    wph
    @148
    @20
    @149
    adantr
    @135
    cA
    cB
    @107
    iooltub
    syl3anc
    ad2antrr
    eliood
    dvbdfbdioolem1
    simpld
    eqbrtrd
    @125
    @127
    @40
    @126
    cmul
    co
    #
    @15
    @142
    @125
    @40
    @126
    @125
    @56
    @57
    @133
    @79
    syl
    #
    @141
    remulcld
    @143
    @125
    @39
    @40
    @126
    @133
    @157
    @125
    @126
    @141
    @125
    @123
    cc0
    @126
    clt
    wbr
    @151
    @125
    @29
    @107
    @140
    @137
    posdifd
    mpbid
    elrpd
    @125
    @39
    @133
    ltp1d
    ltmul1dd
    @125
    @156
    @15
    clt
    wbr
    @126
    @41
    clt
    wbr
    @125
    @126
    @29
    @107
    cmin
    co
    #
    cabs
    cfv
    #
    @41
    @141
    @105
    @159
    cr
    wcel
    #
    @123
    @105
    @158
    @105
    @158
    @105
    @29
    @107
    @139
    @105
    @6
    cr
    @107
    @75
    @121
    sseldi
    #
    resubcld
    #
    recnd
    abscld
    #
    adantr
    @21
    @41
    cr
    wcel
    #
    @104
    @123
    @97
    ad2antrr
    @125
    @126
    @126
    cabs
    cfv
    @159
    cle
    @125
    @126
    @141
    leabsd
    @125
    @107
    @29
    @125
    @107
    @137
    recnd
    @105
    @29
    cc
    wcel
    @123
    @105
    @29
    @139
    recnd
    adantr
    abssubd
    breqtrd
    @105
    @159
    @41
    clt
    wbr
    #
    @123
    @21
    @165
    vi
    @27
    @21
    @22
    @165
    vi
    @27
    wral
    #
    @21
    cK
    @44
    wcel
    @22
    @166
    wa
    @102
    @43
    @166
    vk
    cK
    @0
    @11
    cK
    wceq
    #
    @42
    @165
    vi
    @17
    @27
    @11
    cK
    cuz
    fveq2
    #
    @167
    @32
    @159
    @41
    clt
    @167
    @31
    @158
    cabs
    @167
    @30
    @107
    @29
    cmin
    @11
    cK
    cR
    fveq2
    oveq2d
    fveq2d
    breq1d
    raleqbidv
    elrab
    sylib
    simprd
    r19.21bi
    #
    adantr
    lelttrd
    @125
    @126
    @15
    @40
    @141
    @143
    wph
    @40
    crp
    wcel
    #
    @20
    @104
    @123
    wph
    @40
    @83
    @96
    elrpd
    #
    ad3antrrr
    ltmuldiv2d
    mpbird
    lttrd
    lelttrd
    @105
    @123
    wn
    #
    wa
    #
    @29
    @107
    wceq
    #
    @124
    @105
    @174
    @124
    @172
    @105
    @174
    wa
    #
    @110
    cc0
    @15
    clt
    @175
    @109
    @174
    @105
    @109
    @108
    @108
    cmin
    co
    cc0
    @174
    @106
    @108
    @108
    cmin
    @29
    @107
    cF
    fveq2
    oveq1d
    @105
    @108
    @130
    subidd
    sylan9eqr
    abs00bd
    @20
    @98
    wph
    @104
    @174
    @99
    ad3antlr
    eqbrtrd
    adantlr
    @173
    @174
    wn
    #
    wa
    #
    @105
    @107
    @29
    clt
    wbr
    #
    @124
    @105
    @172
    @176
    simpll
    @177
    @107
    @29
    @105
    @134
    @172
    @176
    @161
    ad2antrr
    @105
    @138
    @172
    @176
    @139
    ad2antrr
    @176
    @107
    @29
    wne
    @173
    @174
    @107
    @29
    @107
    @29
    wceq
    #
    @107
    @29
    @179
    id
    eqcomd
    necon3bi
    adantl
    @105
    @172
    @176
    simplr
    lttri5d
    @105
    @178
    wa
    #
    @110
    @39
    @158
    cmul
    co
    #
    @15
    @105
    @128
    @178
    @131
    adantr
    @105
    @181
    cr
    wcel
    @178
    @105
    @39
    @158
    @132
    @162
    remulcld
    adantr
    #
    @20
    @53
    wph
    @104
    @178
    @54
    ad3antlr
    #
    @180
    @110
    @181
    cle
    wbr
    @110
    @145
    cle
    wbr
    @180
    vy
    cA
    cB
    @107
    @29
    cF
    @39
    wph
    @69
    @20
    @104
    @178
    ioodvbdlimc1lem1.a
    ad3antrrr
    wph
    @70
    @20
    @104
    @178
    ioodvbdlimc1lem1.b
    ad3antrrr
    #
    @105
    @7
    @178
    @114
    adantr
    wph
    @146
    @20
    @104
    @178
    ioodvbdlimc1lem1.dmdv
    ad3antrrr
    wph
    @56
    @20
    @104
    @178
    @78
    ad3antrrr
    #
    wph
    @91
    @20
    @104
    @178
    @94
    ad3antrrr
    @105
    @154
    @178
    @121
    adantr
    @180
    @107
    cB
    @29
    @21
    @107
    cxr
    wcel
    @104
    @178
    @21
    @107
    @136
    rexrd
    ad2antrr
    @180
    cB
    @184
    rexrd
    @105
    @138
    @178
    @139
    adantr
    #
    @105
    @178
    simpr
    #
    @105
    @29
    cB
    clt
    wbr
    #
    @178
    @105
    @153
    @148
    @147
    @188
    wph
    @153
    @20
    @104
    @155
    ad2antrr
    @150
    @117
    cA
    cB
    @29
    iooltub
    syl3anc
    adantr
    eliood
    dvbdfbdioolem1
    simpld
    @180
    @181
    @40
    @158
    cmul
    co
    #
    @15
    @182
    @180
    @40
    @158
    @180
    @39
    c1
    @185
    @180
    1red
    readdcld
    @180
    @29
    @107
    @186
    @105
    @134
    @178
    @161
    adantr
    #
    resubcld
    #
    remulcld
    @183
    @180
    @39
    @40
    @158
    @185
    @180
    @56
    @57
    @185
    @79
    syl
    @180
    @158
    @191
    @180
    @178
    cc0
    @158
    clt
    wbr
    @187
    @180
    @107
    @29
    @190
    @186
    posdifd
    mpbid
    elrpd
    @180
    @39
    @185
    ltp1d
    ltmul1dd
    @180
    @189
    @15
    clt
    wbr
    @158
    @41
    clt
    wbr
    @180
    @158
    @159
    @41
    @191
    @105
    @160
    @178
    @163
    adantr
    @21
    @164
    @104
    @178
    @97
    ad2antrr
    @180
    @158
    @191
    leabsd
    @105
    @165
    @178
    @169
    adantr
    lelttrd
    @180
    @158
    @15
    @40
    @191
    @183
    wph
    @170
    @20
    @104
    @178
    @171
    ad3antrrr
    ltmuldiv2d
    mpbird
    lttrd
    lelttrd
    syl2anc
    pm2.61dan
    pm2.61dan
    eqbrtrd
    ralrimiva
    @18
    @28
    vk
    cK
    @0
    @167
    @16
    @26
    vi
    @17
    @27
    @168
    @167
    @14
    @25
    @15
    clt
    @167
    @13
    @24
    cabs
    @167
    @12
    @23
    @10
    cmin
    @11
    cK
    cS
    fveq2
    oveq2d
    fveq2d
    breq1d
    raleqbidv
    rspcev
    syl2anc
    ralrimiva
    caurcvg
end
