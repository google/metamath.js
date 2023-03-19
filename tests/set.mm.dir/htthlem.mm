include "wcel.mm"
include "cnmoo.mm"
include "co.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cv.mm"
include "c1.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cabs.mm"
include "wa.mm"
include "cnv.mm"
include "hlnvi.mm"
include "wf.mm"
include "lnof.mm"
include "mp3an12.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "nvcl.mm"
include "sylancr.mm"
include "wceq.mm"
include "crab.mm"
include "wfun.mm"
include "cima.mm"
include "cblo.mm"
include "cmpt.mm"
include "chlo.mm"
include "ccphlo.mm"
include "hlph.mm"
include "ax-mp.mm"
include "eqid.mm"
include "ipblnfi.mm"
include "fmptd.mm"
include "ffun.mm"
include "adantr.mm"
include "id.mm"
include "syl6eleq.mm"
include "fvelima.mm"
include "syl2an.mm"
include "ex.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "hlex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "fveq1d.mm"
include "oveq1.mm"
include "ovex.mm"
include "sylan9eqr.mm"
include "ad2ant2lr.mm"
include "rsp2.mm"
include "impl.mm"
include "adantrr.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "cmul.mm"
include "cc.mm"
include "simpl.mm"
include "dipcl.mm"
include "mp3an1.mm"
include "abscld.mm"
include "mpan.mm"
include "ad2antrl.mm"
include "remulcld.mm"
include "sii.mm"
include "cc0.mm"
include "1red.mm"
include "nvge0.mm"
include "jca.mm"
include "simprr.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "sylan2b.mm"
include "fveq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syld.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wss.mm"
include "wb.mm"
include "crn.mm"
include "imassrn.mm"
include "eqsstri.mm"
include "frn.mm"
include "syl5ss.mm"
include "ccbn.mm"
include "hlobn.mm"
include "cnnv.mm"
include "cnnvnm.mm"
include "ubth.mm"
include "mpbid.mm"
include "simpr.mm"
include "sylibr.mm"
include "cdm.mm"
include "dmmptd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "funfvima.mm"
include "sylan.mm"
include "syldan.mm"
include "ad2ant2r.mm"
include "mpd.mm"
include "syl6eleqr.mm"
include "rspcv.mm"
include "cnnvba.mm"
include "nmblore.mm"
include "simplr.mm"
include "c2.mm"
include "cexp.mm"
include "adantl.mm"
include "ipidsq.mm"
include "resqcl.mm"
include "sqge0.mm"
include "absidd.mm"
include "sqvald.mm"
include "3eqtrd.mm"
include "nmblolbi.mm"
include "eqbrtrrd.mm"
include "lemul1ad.mm"
include "w3a.mm"
include "lemul1.mm"
include "biimprd.mm"
include "3expia.mm"
include "expdimp.mm"
include "syl21anc.mm"
include "mpid.mm"
include "0red.mm"
include "blof.mm"
include "nmooge0.mm"
include "breq1.mm"
include "wo.mm"
include "0re.mm"
include "leloe.mm"
include "mpjaod.mm"
include "expr.mm"
include "com23.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "nmobndi.mm"
include "mpbird.mm"
include "ltpnf.mm"
include "isblo.mm"
include "mp2an.mm"
include "sylanbrc.mm"

theorem htthlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cP: class P
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let cL: class L
  let cN: class N
  let cW: class W
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  assume htth.1: |- X = ( BaseSet ` U )
  assume htth.2: |- P = ( .iOLD ` U )
  assume htth.3: |- L = ( U LnOp U )
  assume htth.4: |- B = ( U BLnOp U )
  assume htthlem.5: |- N = ( normCV ` U )
  assume htthlem.6: |- U e. CHilOLD
  assume htthlem.7: |- W = <. <. + , x. >. , abs >.
  assume htthlem.8: |- ( ph -> T e. L )
  assume htthlem.9: |- ( ph -> A. x e. X A. y e. X ( x P ( T ` y ) ) = ( ( T ` x ) P y ) )
  assume htthlem.10: |- F = ( z e. X |-> ( w e. X |-> ( w P ( T ` z ) ) ) )
  assume htthlem.11: |- K = ( F " { z e. X | ( N ` z ) <_ 1 } )

  disjoint w y
  disjoint F w
  disjoint F y
  disjoint w x
  disjoint w z
  disjoint K w
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P w
  disjoint P z
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint U u
  disjoint U v
  assert |- ( ph -> T e. B )

  proof
    wph
    cT
    cL
    wcel
    #
    cT
    cU
    cU
    cnmoo
    co
    #
    cfv
    #
    cpnf
    clt
    wbr
    #
    cT
    cB
    wcel
    #
    htthlem.8
    wph
    @2
    cr
    wcel
    #
    @3
    wph
    @5
    vx
    cv
    #
    cN
    cfv
    #
    c1
    cle
    wbr
    #
    @6
    cT
    cfv
    #
    cN
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    vy
    cr
    wrex
    #
    wph
    vw
    cv
    #
    cU
    cW
    cnmoo
    co
    #
    cfv
    #
    @11
    cle
    wbr
    #
    vw
    cK
    wral
    #
    vy
    cr
    wrex
    #
    @15
    wph
    @6
    @16
    cfv
    #
    cabs
    cfv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vw
    cK
    wral
    #
    vz
    cr
    wrex
    #
    vx
    cX
    wral
    #
    @21
    wph
    @27
    vx
    cX
    wph
    @6
    cX
    wcel
    #
    wa
    #
    @10
    cr
    wcel
    #
    @23
    @10
    cle
    wbr
    #
    vw
    cK
    wral
    #
    @27
    @30
    cU
    cnv
    wcel
    #
    @9
    cX
    wcel
    #
    @31
    cU
    htthlem.6
    hlnvi
    #
    wph
    cX
    cX
    @6
    cT
    wph
    @0
    cX
    cX
    cT
    wf
    #
    htthlem.8
    @34
    @34
    @0
    @37
    @36
    @36
    cT
    cU
    cL
    cU
    cX
    cX
    htth.1
    htth.1
    htth.3
    lnof
    mp3an12
    syl
    #
    ffvelrnda
    #
    @9
    cU
    cN
    cX
    htth.1
    htthlem.5
    nvcl
    sylancr
    #
    @30
    @32
    vw
    cK
    @30
    @16
    cK
    wcel
    #
    @11
    cF
    cfv
    #
    @16
    wceq
    #
    vy
    @24
    cN
    cfv
    #
    c1
    cle
    wbr
    #
    vz
    cX
    crab
    #
    wrex
    #
    @32
    @30
    @41
    @47
    @30
    cF
    wfun
    #
    @16
    cF
    @46
    cima
    #
    wcel
    @47
    @41
    wph
    @48
    @29
    wph
    cX
    cU
    cW
    cblo
    co
    #
    cF
    wf
    #
    @48
    wph
    vz
    cX
    vw
    cX
    @16
    @24
    cT
    cfv
    #
    cP
    co
    #
    cmpt
    #
    @50
    cF
    wph
    @24
    cX
    wcel
    wa
    @52
    cX
    wcel
    @54
    @50
    wcel
    wph
    cX
    cX
    @24
    cT
    @38
    ffvelrnda
    vw
    @52
    @50
    cW
    cP
    cU
    @54
    cX
    htth.1
    htth.2
    cU
    chlo
    wcel
    #
    cU
    ccphlo
    wcel
    htthlem.6
    cU
    hlph
    ax-mp
    #
    htthlem.7
    @50
    eqid
    #
    @54
    eqid
    ipblnfi
    syl
    #
    htthlem.10
    fmptd
    #
    cX
    @50
    cF
    ffun
    syl
    #
    adantr
    @41
    @16
    cK
    @49
    @41
    id
    htthlem.11
    syl6eleq
    vy
    @16
    @46
    cF
    fvelima
    syl2an
    ex
    @30
    @43
    @32
    vy
    @46
    @30
    @11
    @46
    wcel
    #
    wa
    @6
    @42
    cfv
    #
    cabs
    cfv
    #
    @10
    cle
    wbr
    #
    @43
    @32
    @61
    @30
    @11
    cX
    wcel
    #
    @11
    cN
    cfv
    #
    c1
    cle
    wbr
    #
    wa
    #
    @64
    @45
    @67
    vz
    @11
    cX
    vz
    vy
    weq
    #
    @44
    @66
    c1
    cle
    @24
    @11
    cN
    fveq2
    breq1d
    elrab
    @30
    @68
    wa
    #
    @63
    @9
    @11
    cP
    co
    #
    cabs
    cfv
    #
    @10
    cle
    @70
    @62
    @71
    cabs
    @70
    @62
    @6
    @11
    cT
    cfv
    #
    cP
    co
    #
    @71
    @29
    @65
    @62
    @74
    wceq
    wph
    @67
    @65
    @29
    @62
    @6
    vw
    cX
    @16
    @73
    cP
    co
    #
    cmpt
    #
    cfv
    @74
    @65
    @6
    @42
    @76
    vz
    @11
    @54
    @76
    cX
    cF
    @69
    vw
    cX
    @53
    @75
    @69
    @52
    @73
    @16
    cP
    @24
    @11
    cT
    fveq2
    oveq2d
    mpteq2dv
    htthlem.10
    vw
    cX
    @75
    cU
    cX
    htth.1
    hlex
    #
    mptex
    fvmpt
    fveq1d
    vw
    @6
    @75
    @74
    cX
    @76
    @16
    @6
    @73
    cP
    oveq1
    @76
    eqid
    @6
    @73
    cP
    ovex
    fvmpt
    sylan9eqr
    ad2ant2lr
    @30
    @65
    @74
    @71
    wceq
    #
    @67
    wph
    @29
    @65
    @78
    wph
    @78
    vy
    cX
    wral
    vx
    cX
    wral
    @29
    @65
    wa
    @78
    wi
    htthlem.9
    @78
    vx
    vy
    cX
    cX
    rsp2
    syl
    impl
    adantrr
    eqtrd
    fveq2d
    @70
    @72
    @10
    @66
    cmul
    co
    #
    @10
    @70
    @71
    @30
    @35
    @65
    @71
    cc
    wcel
    #
    @68
    @39
    @65
    @67
    simpl
    #
    @34
    @35
    @65
    @80
    @36
    @9
    @11
    cP
    cU
    cX
    htth.1
    htth.2
    dipcl
    mp3an1
    syl2an
    abscld
    @70
    @10
    @66
    @30
    @31
    @68
    @40
    adantr
    #
    @65
    @66
    cr
    wcel
    #
    @30
    @67
    @34
    @65
    @83
    @36
    @11
    cU
    cN
    cX
    htth.1
    htthlem.5
    nvcl
    mpan
    ad2antrl
    #
    remulcld
    @82
    @30
    @35
    @65
    @72
    @79
    cle
    wbr
    @68
    @39
    @81
    @9
    @11
    cP
    cU
    cN
    cX
    htth.1
    htthlem.5
    htth.2
    @56
    sii
    syl2an
    @70
    @79
    @10
    c1
    cmul
    co
    #
    @10
    cle
    @70
    @83
    c1
    cr
    wcel
    @31
    cc0
    @10
    cle
    wbr
    #
    wa
    #
    @67
    @79
    @85
    cle
    wbr
    @84
    @70
    1red
    @30
    @87
    @68
    @30
    @31
    @86
    @40
    @30
    @34
    @35
    @86
    @36
    @39
    @9
    cU
    cN
    cX
    htth.1
    htthlem.5
    nvge0
    #
    sylancr
    jca
    adantr
    @30
    @65
    @67
    simprr
    @66
    c1
    @10
    lemul2a
    syl31anc
    @70
    @10
    @70
    @10
    @82
    recnd
    mulid1d
    breqtrd
    letrd
    eqbrtrd
    sylan2b
    @43
    @63
    @23
    @10
    cle
    @43
    @62
    @22
    cabs
    @6
    @42
    @16
    fveq1
    fveq2d
    breq1d
    syl5ibcom
    rexlimdva
    syld
    ralrimiv
    @26
    @33
    vz
    @10
    cr
    @24
    @10
    wceq
    @25
    @32
    vw
    cK
    @24
    @10
    @23
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    wph
    cK
    @50
    wss
    #
    @28
    @21
    wb
    #
    wph
    cK
    cF
    crn
    #
    @50
    cK
    @49
    @91
    htthlem.11
    cF
    @46
    imassrn
    eqsstri
    wph
    @51
    @91
    @50
    wss
    @59
    cX
    @50
    cF
    frn
    syl
    syl5ss
    cU
    ccbn
    wcel
    #
    cW
    cnv
    wcel
    #
    @89
    @90
    @55
    @92
    htthlem.6
    cU
    hlobn
    ax-mp
    cW
    htthlem.7
    cnnv
    #
    vx
    vw
    cK
    cU
    @17
    cabs
    cW
    cX
    vz
    vy
    htth.1
    cW
    htthlem.7
    cnnvnm
    #
    @17
    eqid
    #
    ubth
    mp3an12
    syl
    mpbid
    wph
    @20
    @14
    vy
    cr
    wph
    @11
    cr
    wcel
    #
    wa
    #
    @20
    @13
    vx
    cX
    @98
    @29
    wa
    @8
    @20
    @12
    @98
    @29
    @8
    @20
    @12
    wi
    @98
    @29
    @8
    wa
    #
    wa
    #
    @20
    @6
    cF
    cfv
    #
    @17
    cfv
    #
    @11
    cle
    wbr
    #
    @12
    @100
    @101
    cK
    wcel
    @20
    @103
    wi
    @100
    @101
    @49
    cK
    @100
    @6
    @46
    wcel
    #
    @101
    @49
    wcel
    #
    @100
    @99
    @104
    @98
    @99
    simpr
    @45
    @8
    vz
    @6
    cX
    vz
    vx
    weq
    #
    @44
    @7
    c1
    cle
    @24
    @6
    cN
    fveq2
    breq1d
    elrab
    sylibr
    wph
    @29
    @104
    @105
    wi
    #
    @97
    @8
    wph
    @29
    @6
    cF
    cdm
    #
    wcel
    #
    @107
    wph
    @109
    @29
    wph
    @108
    cX
    @6
    wph
    vz
    cF
    cX
    @54
    @50
    htthlem.10
    @58
    dmmptd
    eleq2d
    biimpar
    wph
    @48
    @109
    @107
    @60
    @46
    @6
    cF
    funfvima
    sylan
    syldan
    ad2ant2r
    mpd
    htthlem.11
    syl6eleqr
    @19
    @103
    vw
    @101
    cK
    @16
    @101
    wceq
    @18
    @102
    @11
    cle
    @16
    @101
    @17
    fveq2
    breq1d
    rspcv
    syl
    @98
    @29
    @103
    @12
    wi
    @8
    @98
    @29
    @103
    @12
    @98
    @29
    @103
    wa
    #
    wa
    #
    cc0
    @10
    clt
    wbr
    #
    @12
    cc0
    @10
    wceq
    #
    @111
    @112
    @10
    @10
    cmul
    co
    #
    @11
    @10
    cmul
    co
    #
    cle
    wbr
    #
    @12
    @111
    @114
    @102
    @10
    cmul
    co
    #
    @115
    @111
    @10
    @10
    wph
    @29
    @31
    @97
    @103
    @40
    ad2ant2r
    #
    @118
    remulcld
    @111
    @102
    @10
    wph
    @29
    @102
    cr
    wcel
    #
    @97
    @103
    @30
    @101
    @50
    wcel
    #
    @119
    wph
    cX
    @50
    @6
    cF
    @59
    ffvelrnda
    #
    @34
    @93
    @120
    @119
    @36
    @94
    @50
    @101
    cU
    @17
    cW
    cX
    cc
    htth.1
    cW
    htthlem.7
    cnnvba
    #
    @96
    @57
    nmblore
    mp3an12
    syl
    ad2ant2r
    #
    @118
    remulcld
    @111
    @11
    @10
    wph
    @97
    @110
    simplr
    #
    @118
    remulcld
    @111
    @9
    @101
    cfv
    #
    cabs
    cfv
    #
    @114
    @117
    cle
    @111
    @126
    @10
    c2
    cexp
    co
    #
    cabs
    cfv
    #
    @127
    @114
    @111
    @125
    @127
    cabs
    @111
    @125
    @9
    @9
    cP
    co
    #
    @127
    wph
    @29
    @125
    @129
    wceq
    @97
    @103
    @30
    @125
    @9
    vw
    cX
    @16
    @9
    cP
    co
    #
    cmpt
    #
    cfv
    #
    @129
    @30
    @9
    @101
    @131
    @29
    @101
    @131
    wceq
    wph
    vz
    @6
    @54
    @131
    cX
    cF
    @106
    vw
    cX
    @53
    @130
    @106
    @52
    @9
    @16
    cP
    @24
    @6
    cT
    fveq2
    oveq2d
    mpteq2dv
    htthlem.10
    vw
    cX
    @130
    @77
    mptex
    fvmpt
    adantl
    fveq1d
    @30
    @35
    @132
    @129
    wceq
    @39
    vw
    @9
    @130
    @129
    cX
    @131
    @16
    @9
    @9
    cP
    oveq1
    @131
    eqid
    @9
    @9
    cP
    ovex
    fvmpt
    syl
    eqtrd
    ad2ant2r
    @111
    @34
    @35
    @129
    @127
    wceq
    @36
    wph
    @29
    @35
    @97
    @103
    @39
    ad2ant2r
    #
    @9
    cP
    cU
    cN
    cX
    htth.1
    htthlem.5
    htth.2
    ipidsq
    sylancr
    eqtrd
    fveq2d
    @111
    @31
    @128
    @127
    wceq
    @118
    @31
    @127
    @10
    resqcl
    @10
    sqge0
    absidd
    syl
    @111
    @10
    @111
    @10
    @118
    recnd
    sqvald
    3eqtrd
    @111
    @120
    @35
    @126
    @117
    cle
    wbr
    wph
    @29
    @120
    @97
    @103
    @121
    ad2ant2r
    @133
    @9
    @50
    @101
    cU
    cN
    cabs
    @17
    cW
    cX
    htth.1
    htthlem.5
    @95
    @96
    @57
    @36
    @94
    nmblolbi
    syl2anc
    eqbrtrrd
    @111
    @102
    @11
    @10
    @123
    @124
    @118
    @111
    @34
    @35
    @86
    @36
    @133
    @88
    sylancr
    #
    @98
    @29
    @103
    simprr
    #
    lemul1ad
    letrd
    @111
    @31
    @97
    @31
    @112
    @116
    @12
    wi
    #
    wi
    @118
    @124
    @118
    @31
    @97
    wa
    @31
    @112
    @136
    @31
    @97
    @31
    @112
    wa
    #
    @136
    @31
    @97
    @137
    w3a
    @12
    @116
    @10
    @11
    @10
    lemul1
    biimprd
    3expia
    expdimp
    syl21anc
    mpid
    @111
    cc0
    @11
    cle
    wbr
    @113
    @12
    @111
    cc0
    @102
    @11
    @111
    0red
    @123
    @124
    @111
    cX
    cc
    @101
    wf
    #
    cc0
    @102
    cle
    wbr
    #
    wph
    @29
    @138
    @97
    @103
    @30
    @120
    @138
    @121
    @34
    @93
    @120
    @138
    @36
    @94
    @50
    @101
    cU
    cW
    cX
    cc
    htth.1
    @122
    @57
    blof
    mp3an12
    syl
    ad2ant2r
    @34
    @93
    @138
    @139
    @36
    @94
    @101
    cU
    @17
    cW
    cX
    cc
    htth.1
    @122
    @96
    nmooge0
    mp3an12
    syl
    @135
    letrd
    cc0
    @10
    @11
    cle
    breq1
    syl5ibcom
    @111
    @86
    @112
    @113
    wo
    #
    @134
    @111
    cc0
    cr
    wcel
    @31
    @86
    @140
    wb
    0re
    @118
    cc0
    @10
    leloe
    sylancr
    mpbid
    mpjaod
    expr
    adantrr
    syld
    expr
    com23
    ralrimdva
    reximdva
    mpd
    wph
    @37
    @5
    @15
    wb
    @38
    vx
    cT
    cU
    cN
    cN
    @1
    cU
    cX
    cX
    vy
    htth.1
    htth.1
    htthlem.5
    htthlem.5
    @1
    eqid
    #
    @36
    @36
    nmobndi
    syl
    mpbird
    @2
    ltpnf
    syl
    @34
    @34
    @4
    @0
    @3
    wa
    wb
    @36
    @36
    cB
    cT
    cU
    cL
    @1
    cU
    @141
    htth.3
    htth.4
    isblo
    mp2an
    sylanbrc
end
