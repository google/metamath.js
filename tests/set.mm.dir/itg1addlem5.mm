include "crn.mm"
include "cv.mm"
include "co.mm"
include "cmul.mm"
include "csu.mm"
include "caddc.mm"
include "cof.mm"
include "citg1.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cfn.mm"
include "i1frn.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "i1ff.mm"
include "frn.mm"
include "sselda.mm"
include "recnd.mm"
include "cxp.mm"
include "itg1addlem2.mm"
include "ad2antrr.mm"
include "adantlr.mm"
include "fovrnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "fsumadd.mm"
include "itg1addlem4.mm"
include "adddird.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "wceq.mm"
include "itg1val.mm"
include "cin.mm"
include "ciun.mm"
include "inss2.mm"
include "a1i.mm"
include "i1fima.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "wn.mm"
include "ssdifssd.mm"
include "wne.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "simpl.mm"
include "necon3ai.mm"
include "itg1addlem3.mm"
include "syl21anc.mm"
include "eqeltrrd.mm"
include "itg1addlem1.mm"
include "iunin2.mm"
include "mblss.mm"
include "iunid.mm"
include "imaeq2i.mm"
include "imaiun.mm"
include "cnvimarndm.mm"
include "3eqtr3i.mm"
include "fdm.mm"
include "syl5eq.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5req.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "fsummulc2.mm"
include "difssd.mm"
include "dfin4.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "elsni.mm"
include "oveq1d.mm"
include "0re.mm"
include "syl6eqel.mm"
include "mul02d.mm"
include "cuz.mm"
include "wo.mm"
include "olcd.mm"
include "sumz.mm"
include "sylan2.mm"
include "fsumss.mm"
include "3eqtrd.mm"
include "inss1.mm"
include "simpr.mm"
include "incom.mm"
include "iuneq2i.mm"
include "eqtri.mm"
include "cnvimass.mm"
include "syl5sseq.mm"
include "cc.mm"
include "anasss.mm"
include "fsumcom.mm"
include "oveq12d.mm"

theorem itg1addlem5
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cI: class I
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vv: setvar v
  let vx: setvar x
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )
  assume itg1add.3: |- I = ( i e. RR , j e. RR |-> if ( ( i = 0 /\ j = 0 ) , 0 , ( vol ` ( ( `' F " { i } ) i^i ( `' G " { j } ) ) ) ) )
  assume itg1add.4: |- P = ( + |` ( ran F X. ran G ) )

  disjoint i j
  disjoint F i
  disjoint F j
  disjoint G i
  disjoint G j
  disjoint i ph
  disjoint j ph
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B i
  disjoint B j
  disjoint w y
  disjoint I w
  disjoint I y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint x y
  disjoint x z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( S.1 ` ( F oF + G ) ) = ( ( S.1 ` F ) + ( S.1 ` G ) ) )

  proof
    wph
    cF
    crn
    #
    cG
    crn
    #
    vy
    cv
    #
    @2
    vz
    cv
    #
    cI
    co
    #
    cmul
    co
    #
    vz
    csu
    #
    @1
    @3
    @4
    cmul
    co
    #
    vz
    csu
    #
    caddc
    co
    #
    vy
    csu
    #
    @0
    @6
    vy
    csu
    #
    @0
    @8
    vy
    csu
    #
    caddc
    co
    cF
    cG
    caddc
    cof
    co
    citg1
    cfv
    #
    cF
    citg1
    cfv
    #
    cG
    citg1
    cfv
    #
    caddc
    co
    wph
    @0
    @6
    @8
    vy
    wph
    cF
    citg1
    cdm
    #
    wcel
    #
    @0
    cfn
    wcel
    #
    i1fadd.1
    cF
    i1frn
    syl
    #
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @1
    @5
    vz
    wph
    @1
    cfn
    wcel
    #
    @20
    wph
    cG
    @16
    wcel
    #
    @22
    i1fadd.2
    cG
    i1frn
    syl
    #
    adantr
    #
    @21
    @3
    @1
    wcel
    #
    wa
    #
    @2
    @4
    @27
    @2
    @21
    @2
    cr
    wcel
    #
    @26
    wph
    @0
    cr
    @2
    wph
    cr
    cr
    cF
    wf
    #
    @0
    cr
    wss
    #
    wph
    @17
    @29
    i1fadd.1
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    frn
    syl
    #
    sselda
    #
    adantr
    #
    recnd
    #
    @27
    @4
    @27
    @2
    @3
    cr
    cr
    cr
    cI
    wph
    cr
    cr
    cxp
    cr
    cI
    wf
    #
    @20
    @26
    wph
    vi
    vj
    cF
    cG
    cI
    i1fadd.1
    i1fadd.2
    itg1add.3
    itg1addlem2
    #
    ad2antrr
    @34
    wph
    @26
    @3
    cr
    wcel
    #
    @20
    wph
    @1
    cr
    @3
    wph
    cr
    cr
    cG
    wf
    #
    @1
    cr
    wss
    #
    wph
    @23
    @39
    i1fadd.2
    cG
    i1ff
    syl
    #
    cr
    cr
    cG
    frn
    syl
    #
    sselda
    #
    adantlr
    #
    fovrnd
    recnd
    #
    mulcld
    #
    fsumcl
    @21
    @1
    @7
    vz
    @25
    @27
    @3
    @4
    @27
    @3
    @44
    recnd
    #
    @45
    mulcld
    #
    fsumcl
    fsumadd
    wph
    @13
    @0
    @1
    @2
    @3
    caddc
    co
    @4
    cmul
    co
    #
    vz
    csu
    #
    vy
    csu
    @10
    wph
    vy
    vz
    cP
    vi
    vj
    cF
    cG
    cI
    i1fadd.1
    i1fadd.2
    itg1add.3
    itg1add.4
    itg1addlem4
    wph
    @0
    @50
    @9
    vy
    @21
    @50
    @1
    @5
    @7
    caddc
    co
    #
    vz
    csu
    @9
    @21
    @1
    @49
    @51
    vz
    @27
    @2
    @3
    @4
    @35
    @47
    @45
    adddird
    sumeq2dv
    @21
    @1
    @5
    @7
    vz
    @25
    @46
    @48
    fsumadd
    eqtrd
    sumeq2dv
    eqtrd
    wph
    @14
    @11
    @15
    @12
    caddc
    wph
    @14
    @0
    cc0
    csn
    #
    cdif
    #
    @2
    cF
    ccnv
    #
    @2
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vy
    csu
    #
    @53
    @6
    vy
    csu
    @11
    wph
    @17
    @14
    @59
    wceq
    i1fadd.1
    vy
    cF
    itg1val
    syl
    wph
    @53
    @58
    @6
    vy
    wph
    @2
    @53
    wcel
    #
    wa
    #
    @58
    @2
    @1
    @4
    vz
    csu
    #
    cmul
    co
    @6
    @61
    @57
    @62
    @2
    cmul
    @61
    vz
    @1
    @56
    cG
    ccnv
    #
    @3
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    cvol
    cfv
    @1
    @66
    cvol
    cfv
    #
    vz
    csu
    @57
    @62
    @61
    @1
    @66
    vz
    cG
    cr
    cr
    wph
    @39
    @60
    @41
    adantr
    #
    wph
    @22
    @60
    @24
    adantr
    #
    @66
    @65
    wss
    @61
    @26
    wa
    #
    @56
    @65
    inss2
    a1i
    @71
    @56
    cvol
    cdm
    #
    wcel
    #
    @65
    @72
    wcel
    #
    @66
    @72
    wcel
    #
    wph
    @73
    @60
    @26
    wph
    @17
    @73
    i1fadd.1
    @55
    cF
    i1fima
    #
    syl
    #
    ad2antrr
    wph
    @74
    @60
    @26
    wph
    @23
    @74
    i1fadd.2
    @64
    cG
    i1fima
    syl
    #
    ad2antrr
    @56
    @65
    inmbl
    #
    syl2anc
    @71
    @4
    @68
    cr
    @71
    @28
    @38
    @2
    cc0
    wceq
    #
    @3
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @4
    @68
    wceq
    #
    @61
    @28
    @26
    wph
    @53
    cr
    @2
    wph
    @0
    cr
    @52
    @32
    ssdifssd
    sselda
    #
    adantr
    #
    @61
    @1
    cr
    @3
    wph
    @40
    @60
    @42
    adantr
    sselda
    #
    @71
    @2
    cc0
    wne
    #
    @83
    @60
    @88
    wph
    @26
    @2
    @0
    cc0
    eldifsni
    ad2antlr
    @82
    @2
    cc0
    @80
    @81
    simpl
    necon3ai
    syl
    wph
    @2
    @3
    vi
    vj
    cF
    cG
    cI
    i1fadd.1
    i1fadd.2
    itg1add.3
    itg1addlem3
    #
    syl21anc
    #
    @71
    @2
    @3
    cr
    cr
    cr
    cI
    wph
    @36
    @60
    @26
    @37
    ad2antrr
    @86
    @87
    fovrnd
    #
    eqeltrrd
    itg1addlem1
    @61
    @56
    @67
    cvol
    @61
    @67
    @56
    vz
    @1
    @65
    ciun
    #
    cin
    #
    @56
    vz
    @1
    @56
    @65
    iunin2
    @61
    @56
    @92
    wss
    @93
    @56
    wceq
    @61
    @56
    cr
    @92
    @61
    @73
    @56
    cr
    wss
    @61
    @17
    @73
    wph
    @17
    @60
    i1fadd.1
    adantr
    @76
    syl
    @56
    mblss
    syl
    @61
    @92
    cG
    cdm
    #
    cr
    @63
    vz
    @1
    @64
    ciun
    #
    cima
    @63
    @1
    cima
    @92
    @94
    @95
    @1
    @63
    vz
    @1
    iunid
    imaeq2i
    vz
    @63
    @1
    @64
    imaiun
    cG
    cnvimarndm
    3eqtr3i
    @61
    @39
    @94
    cr
    wceq
    #
    @69
    cr
    cr
    cG
    fdm
    #
    syl
    syl5eq
    sseqtr4d
    @56
    @92
    df-ss
    sylib
    syl5req
    fveq2d
    @61
    @1
    @4
    @68
    vz
    @90
    sumeq2dv
    3eqtr4d
    oveq2d
    @61
    @1
    @4
    @2
    vz
    @70
    @61
    @2
    @85
    recnd
    @71
    @4
    @91
    recnd
    #
    fsummulc2
    eqtrd
    sumeq2dv
    wph
    @53
    @0
    @6
    vy
    wph
    @0
    @52
    difssd
    @61
    @1
    @5
    vz
    @70
    @71
    @2
    @4
    @71
    @2
    @86
    recnd
    @98
    mulcld
    fsumcl
    @2
    @0
    @53
    cdif
    #
    wcel
    wph
    @2
    @52
    wcel
    #
    @6
    cc0
    wceq
    @99
    @52
    @2
    @99
    @0
    @52
    cin
    @52
    @0
    @52
    dfin4
    @0
    @52
    inss2
    eqsstr3i
    sseli
    wph
    @100
    wa
    #
    @6
    @1
    cc0
    vz
    csu
    #
    cc0
    @101
    @1
    @5
    cc0
    vz
    @101
    @26
    wa
    #
    @5
    cc0
    @4
    cmul
    co
    #
    cc0
    @103
    @2
    cc0
    @4
    cmul
    @100
    @80
    wph
    @26
    @2
    cc0
    elsni
    ad2antlr
    #
    oveq1d
    @103
    @4
    @103
    @4
    @103
    @2
    @3
    cr
    cr
    cr
    cI
    wph
    @36
    @100
    @26
    @37
    ad2antrr
    @103
    @2
    cc0
    cr
    @105
    0re
    syl6eqel
    wph
    @26
    @38
    @100
    @43
    adantlr
    fovrnd
    recnd
    mul02d
    eqtrd
    sumeq2dv
    @101
    @1
    cc0
    cuz
    cfv
    #
    wss
    #
    @22
    wo
    @102
    cc0
    wceq
    @101
    @22
    @107
    wph
    @22
    @100
    @24
    adantr
    olcd
    @1
    vz
    cc0
    sumz
    syl
    eqtrd
    sylan2
    @19
    fsumss
    3eqtrd
    wph
    @15
    @1
    @52
    cdif
    #
    @3
    @65
    cvol
    cfv
    #
    cmul
    co
    #
    vz
    csu
    #
    @108
    @0
    @7
    vy
    csu
    #
    vz
    csu
    #
    @12
    wph
    @23
    @15
    @111
    wceq
    i1fadd.2
    vz
    cG
    itg1val
    syl
    wph
    @108
    @110
    @112
    vz
    wph
    @3
    @108
    wcel
    #
    wa
    #
    @110
    @3
    @0
    @4
    vy
    csu
    #
    cmul
    co
    @112
    @115
    @109
    @116
    @3
    cmul
    @115
    vy
    @0
    @66
    ciun
    #
    cvol
    cfv
    @0
    @68
    vy
    csu
    @109
    @116
    @115
    @0
    @66
    vy
    cF
    cr
    cr
    wph
    @29
    @114
    @31
    adantr
    wph
    @18
    @114
    @19
    adantr
    #
    @66
    @56
    wss
    @115
    @20
    wa
    #
    @56
    @65
    inss1
    a1i
    @119
    @73
    @74
    @75
    wph
    @73
    @114
    @20
    @77
    ad2antrr
    wph
    @74
    @114
    @20
    @78
    ad2antrr
    @79
    syl2anc
    @119
    @4
    @68
    cr
    @119
    @28
    @38
    @83
    @84
    @115
    @0
    cr
    @2
    wph
    @30
    @114
    @32
    adantr
    sselda
    #
    @115
    @38
    @20
    wph
    @108
    cr
    @3
    wph
    @1
    cr
    @52
    @42
    ssdifssd
    sselda
    #
    adantr
    #
    @119
    @3
    cc0
    wne
    #
    @83
    @114
    @123
    wph
    @20
    @3
    @1
    cc0
    eldifsni
    ad2antlr
    @82
    @3
    cc0
    @80
    @81
    simpr
    necon3ai
    syl
    @89
    syl21anc
    #
    @119
    @2
    @3
    cr
    cr
    cr
    cI
    wph
    @36
    @114
    @20
    @37
    ad2antrr
    @120
    @122
    fovrnd
    #
    eqeltrrd
    itg1addlem1
    @115
    @65
    @117
    cvol
    @115
    @117
    @65
    vy
    @0
    @56
    ciun
    #
    cin
    #
    @65
    @117
    vy
    @0
    @65
    @56
    cin
    #
    ciun
    @127
    vy
    @0
    @66
    @128
    @66
    @128
    wceq
    @20
    @56
    @65
    incom
    a1i
    iuneq2i
    vy
    @0
    @65
    @56
    iunin2
    eqtri
    @115
    @65
    @126
    wss
    @127
    @65
    wceq
    @115
    @65
    cr
    @126
    @115
    @94
    @65
    cr
    cG
    @64
    cnvimass
    wph
    @96
    @114
    wph
    @39
    @96
    @41
    @97
    syl
    adantr
    syl5sseq
    @115
    @126
    cF
    cdm
    #
    cr
    @54
    vy
    @0
    @55
    ciun
    #
    cima
    @54
    @0
    cima
    @126
    @129
    @130
    @0
    @54
    vy
    @0
    iunid
    imaeq2i
    vy
    @54
    @0
    @55
    imaiun
    cF
    cnvimarndm
    3eqtr3i
    wph
    @129
    cr
    wceq
    #
    @114
    wph
    @29
    @131
    @31
    cr
    cr
    cF
    fdm
    syl
    adantr
    syl5eq
    sseqtr4d
    @65
    @126
    df-ss
    sylib
    syl5req
    fveq2d
    @115
    @0
    @4
    @68
    vy
    @124
    sumeq2dv
    3eqtr4d
    oveq2d
    @115
    @0
    @4
    @3
    vy
    @118
    @115
    @3
    @121
    recnd
    #
    @119
    @4
    @125
    recnd
    #
    fsummulc2
    eqtrd
    sumeq2dv
    wph
    @113
    @1
    @112
    vz
    csu
    @12
    wph
    @108
    @1
    @112
    vz
    wph
    @1
    @52
    difssd
    @115
    @0
    @7
    vy
    @118
    @119
    @3
    @4
    @115
    @3
    cc
    wcel
    @20
    @132
    adantr
    @133
    mulcld
    fsumcl
    @3
    @1
    @108
    cdif
    #
    wcel
    wph
    @3
    @52
    wcel
    #
    @112
    cc0
    wceq
    @134
    @52
    @3
    @134
    @1
    @52
    cin
    @52
    @1
    @52
    dfin4
    @1
    @52
    inss2
    eqsstr3i
    sseli
    wph
    @135
    wa
    #
    @112
    @0
    cc0
    vy
    csu
    #
    cc0
    @136
    @0
    @7
    cc0
    vy
    @136
    @20
    wa
    #
    @7
    @104
    cc0
    @138
    @3
    cc0
    @4
    cmul
    @135
    @81
    wph
    @20
    @3
    cc0
    elsni
    ad2antlr
    #
    oveq1d
    @138
    @4
    @138
    @4
    @138
    @2
    @3
    cr
    cr
    cr
    cI
    wph
    @36
    @135
    @20
    @37
    ad2antrr
    wph
    @20
    @28
    @135
    @33
    adantlr
    @138
    @3
    cc0
    cr
    @139
    0re
    syl6eqel
    fovrnd
    recnd
    mul02d
    eqtrd
    sumeq2dv
    @136
    @0
    @106
    wss
    #
    @18
    wo
    @137
    cc0
    wceq
    @136
    @18
    @140
    wph
    @18
    @135
    @19
    adantr
    olcd
    @0
    vy
    cc0
    sumz
    syl
    eqtrd
    sylan2
    @24
    fsumss
    wph
    @1
    @0
    @7
    vz
    vy
    @24
    @19
    wph
    @26
    @20
    @7
    cc
    wcel
    wph
    @26
    wa
    #
    @20
    wa
    #
    @3
    @4
    @142
    @3
    @141
    @38
    @20
    @43
    adantr
    #
    recnd
    @142
    @4
    @142
    @2
    @3
    cr
    cr
    cr
    cI
    wph
    @36
    @26
    @20
    @37
    ad2antrr
    @141
    @0
    cr
    @2
    wph
    @30
    @26
    @32
    adantr
    sselda
    @143
    fovrnd
    recnd
    mulcld
    anasss
    fsumcom
    eqtrd
    3eqtrd
    oveq12d
    3eqtr4d
end
