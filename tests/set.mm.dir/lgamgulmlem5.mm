include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cabs.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "cpi.mm"
include "cif.mm"
include "breq2.mm"
include "adantr.mm"
include "cn0.mm"
include "wral.mm"
include "cc.mm"
include "crab.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "simplrl.mm"
include "simprr.mm"
include "simpr.mm"
include "lgamgulmlem3.mm"
include "wn.mm"
include "cz.mm"
include "cdif.mm"
include "wss.mm"
include "lgamgulmlem1.mm"
include "sseldd.mm"
include "eldifad.mm"
include "simprl.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "dmgmdivn0.mm"
include "logcld.mm"
include "subcld.mm"
include "abscld.mm"
include "readdcld.mm"
include "nnred.mm"
include "remulcld.mm"
include "rpmulcld.mm"
include "cr.mm"
include "pire.mm"
include "a1i.mm"
include "abs2dif2d.mm"
include "absmuld.mm"
include "rpred.mm"
include "mulid2d.mm"
include "lep1d.mm"
include "eqbrtrd.mm"
include "1red.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "logge0d.mm"
include "absidd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "elrab2.mm"
include "simprbi.mm"
include "ad2antll.mm"
include "simpld.mm"
include "lemul1ad.mm"
include "absrpcld.mm"
include "cc0.mm"
include "wne.mm"
include "abslogle.mm"
include "syl2anc.mm"
include "cneg.mm"
include "crp.mm"
include "wceq.mm"
include "1rp.mm"
include "relogdiv.mm"
include "sylancr.mm"
include "log1.mm"
include "oveq1i.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "syl6req.mm"
include "nnrecred.mm"
include "0le1.mm"
include "lediv2ad.mm"
include "nnnn0d.mm"
include "simprd.mm"
include "oveq2.mm"
include "rspcv.mm"
include "sylc.mm"
include "letrd.mm"
include "lediv1dd.mm"
include "recdiv2d.mm"
include "divdird.mm"
include "dividd.mm"
include "eqtr2d.mm"
include "absdivd.mm"
include "rpge0d.mm"
include "3eqtrrd.mm"
include "3brtr3d.mm"
include "rpreccld.mm"
include "logled.mm"
include "abstrid.mm"
include "abs1.mm"
include "oveq2i.mm"
include "syl6breq.mm"
include "absge0d.mm"
include "nnge1d.mm"
include "lediv12ad.mm"
include "div1d.mm"
include "leadd1dd.mm"
include "lemulge11d.mm"
include "absled.mm"
include "mpbir2and.mm"
include "le2addd.mm"
include "ifbothda.mm"
include "cmpt.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "cnex.mm"
include "rabex2.mm"
include "mptex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "fveq1d.mm"
include "eqid.mm"
include "ovex.mm"
include "ifbieq12d.mm"
include "ifex.mm"
include "3brtr4d.mm"

theorem lgamgulmlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vr: setvar r
  let vt: setvar t
  let cN: class N
  let cA: class A
  let cO: class O
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.g: |- G = ( m e. NN |-> ( z e. U |-> ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) ) )
  assume lgamgulm.t: |- T = ( m e. NN |-> if ( ( 2 x. R ) <_ m , ( R x. ( ( 2 x. ( R + 1 ) ) / ( m ^ 2 ) ) ) , ( ( R x. ( log ` ( ( m + 1 ) / m ) ) ) + ( ( log ` ( ( R + 1 ) x. m ) ) + _pi ) ) ) )

  disjoint n y
  disjoint G n
  disjoint G y
  disjoint x y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint R k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint R m
  disjoint n x
  disjoint n z
  disjoint R n
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint U m
  disjoint U n
  disjoint U y
  disjoint U z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T n
  disjoint T y
  disjoint n r
  disjoint r y
  disjoint G r
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint k r
  disjoint k t
  disjoint m r
  disjoint m t
  disjoint n t
  disjoint r t
  disjoint r x
  disjoint r z
  disjoint R r
  disjoint t z
  disjoint R t
  disjoint U r
  disjoint U t
  disjoint A k
  disjoint A m
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint O n
  disjoint O r
  disjoint O y
  disjoint ph r
  disjoint ph t
  disjoint T r
  assert |- ( ( ph /\ ( n e. NN /\ y e. U ) ) -> ( abs ` ( ( G ` n ) ` y ) ) <_ ( T ` n ) )

  proof
    wph
    vn
    cv
    #
    cn
    wcel
    #
    vy
    cv
    #
    cU
    wcel
    #
    wa
    #
    wa
    #
    @2
    @0
    c1
    caddc
    co
    #
    @0
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @2
    @0
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cR
    cmul
    co
    #
    @0
    cle
    wbr
    #
    cR
    c2
    cR
    c1
    caddc
    co
    #
    cmul
    co
    #
    @0
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cR
    @8
    cmul
    co
    #
    @17
    @0
    cmul
    co
    #
    clog
    cfv
    #
    cpi
    caddc
    co
    #
    caddc
    co
    #
    cif
    #
    @2
    @0
    cG
    cfv
    #
    cfv
    #
    cabs
    cfv
    @0
    cT
    cfv
    #
    cle
    @16
    @14
    @21
    cle
    wbr
    @14
    @26
    cle
    wbr
    #
    @14
    @27
    cle
    wbr
    @5
    @21
    @26
    @21
    @27
    @14
    cle
    breq2
    @26
    @27
    @14
    cle
    breq2
    @5
    @16
    wa
    vt
    @2
    cR
    cU
    vk
    @0
    @5
    cR
    cn
    wcel
    #
    @16
    wph
    @32
    @4
    lgamgulm.r
    adantr
    #
    adantr
    cU
    vx
    cv
    #
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    c1
    cR
    cdiv
    co
    #
    @34
    vk
    cv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    #
    vx
    cc
    crab
    vt
    cv
    #
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    @37
    @44
    @38
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    #
    vt
    cc
    crab
    lgamgulm.u
    @43
    @51
    vx
    vt
    cc
    vx
    vt
    weq
    #
    @36
    @46
    @42
    @50
    @52
    @35
    @45
    cR
    cle
    @34
    @44
    cabs
    fveq2
    breq1d
    @52
    @41
    @49
    vk
    cn0
    @52
    @40
    @48
    @37
    cle
    @52
    @39
    @47
    cabs
    @34
    @44
    @38
    caddc
    oveq1
    fveq2d
    breq2d
    ralbidv
    anbi12d
    cbvrabv
    eqtri
    wph
    @1
    @3
    @16
    simplrl
    @5
    @3
    @16
    wph
    @1
    @3
    simprr
    #
    adantr
    @5
    @16
    simpr
    lgamgulmlem3
    @5
    @31
    @16
    wn
    @5
    @14
    @9
    cabs
    cfv
    #
    @12
    cabs
    cfv
    #
    caddc
    co
    @26
    @5
    @13
    @5
    @9
    @12
    @5
    @2
    @8
    @5
    @2
    cc
    cz
    cn
    cdif
    #
    @5
    cU
    cc
    @56
    cdif
    #
    @2
    wph
    cU
    @57
    wss
    @4
    wph
    vx
    cR
    cU
    vk
    lgamgulm.r
    lgamgulm.u
    lgamgulmlem1
    adantr
    @53
    sseldd
    #
    eldifad
    #
    @5
    @8
    @5
    @7
    @5
    @6
    @0
    @5
    @6
    @5
    @0
    wph
    @1
    @3
    simprl
    #
    peano2nnd
    nnrpd
    @5
    @0
    @60
    nnrpd
    #
    rpdivcld
    #
    relogcld
    #
    recnd
    #
    mulcld
    #
    @5
    @11
    @5
    @10
    c1
    @5
    @2
    @0
    @59
    @5
    @0
    @60
    nncnd
    #
    @5
    @0
    @60
    nnne0d
    #
    divcld
    #
    @5
    1cnd
    #
    addcld
    #
    @5
    @2
    @0
    @58
    @60
    dmgmdivn0
    #
    logcld
    #
    subcld
    abscld
    @5
    @54
    @55
    @5
    @9
    @65
    abscld
    #
    @5
    @12
    @72
    abscld
    #
    readdcld
    @5
    @22
    @25
    @5
    cR
    @8
    @5
    cR
    @33
    nnred
    #
    @63
    remulcld
    #
    @5
    @24
    cpi
    @5
    @23
    @5
    @17
    @0
    @5
    @17
    @5
    cR
    @33
    peano2nnd
    #
    nnrpd
    #
    @61
    rpmulcld
    #
    relogcld
    #
    cpi
    cr
    wcel
    @5
    pire
    a1i
    #
    readdcld
    #
    readdcld
    @5
    @9
    @12
    @65
    @72
    abs2dif2d
    @5
    @54
    @55
    @22
    @25
    @73
    @74
    @76
    @82
    @5
    @54
    @2
    cabs
    cfv
    #
    @8
    cmul
    co
    #
    @22
    cle
    @5
    @54
    @83
    @8
    cabs
    cfv
    #
    cmul
    co
    @84
    @5
    @2
    @8
    @59
    @64
    absmuld
    @5
    @85
    @8
    @83
    cmul
    @5
    @8
    @63
    @5
    @7
    @5
    @7
    @62
    rpred
    @5
    c1
    @0
    cmul
    co
    #
    @6
    cle
    wbr
    c1
    @7
    cle
    wbr
    @5
    @86
    @0
    @6
    cle
    @5
    @0
    @66
    mulid2d
    @5
    @0
    @5
    @0
    @60
    nnred
    #
    lep1d
    eqbrtrd
    @5
    c1
    @6
    @0
    @5
    1red
    #
    @5
    @0
    c1
    @87
    @88
    readdcld
    @61
    lemuldivd
    mpbid
    logge0d
    #
    absidd
    oveq2d
    eqtrd
    @5
    @83
    cR
    @8
    @5
    @2
    @59
    abscld
    #
    @75
    @63
    @89
    @5
    @83
    cR
    cle
    wbr
    #
    @37
    @2
    @38
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    @3
    @91
    @95
    wa
    #
    wph
    @1
    @3
    @2
    cc
    wcel
    @96
    @43
    @96
    vx
    @2
    cc
    cU
    vx
    vy
    weq
    #
    @36
    @91
    @42
    @95
    @97
    @35
    @83
    cR
    cle
    @34
    @2
    cabs
    fveq2
    breq1d
    @97
    @41
    @94
    vk
    cn0
    @97
    @40
    @93
    @37
    cle
    @97
    @39
    @92
    cabs
    @34
    @2
    @38
    caddc
    oveq1
    fveq2d
    breq2d
    ralbidv
    anbi12d
    lgamgulm.u
    elrab2
    simprbi
    ad2antll
    #
    simpld
    #
    lemul1ad
    eqbrtrd
    @5
    @55
    @11
    cabs
    cfv
    #
    clog
    cfv
    #
    cabs
    cfv
    #
    cpi
    caddc
    co
    #
    @25
    @74
    @5
    @102
    cpi
    @5
    @101
    @5
    @101
    @5
    @100
    @5
    @11
    @70
    @71
    absrpcld
    #
    relogcld
    #
    recnd
    abscld
    #
    @81
    readdcld
    @82
    @5
    @11
    cc
    wcel
    @11
    cc0
    wne
    @55
    @103
    cle
    wbr
    @70
    @71
    @11
    abslogle
    syl2anc
    @5
    @102
    @24
    cpi
    @106
    @80
    @81
    @5
    @102
    @24
    cle
    wbr
    @24
    cneg
    #
    @101
    cle
    wbr
    @101
    @24
    cle
    wbr
    #
    @5
    @107
    c1
    @23
    cdiv
    co
    #
    clog
    cfv
    #
    @101
    cle
    @5
    @110
    c1
    clog
    cfv
    #
    @24
    cmin
    co
    #
    @107
    @5
    c1
    crp
    wcel
    #
    @23
    crp
    wcel
    @110
    @112
    wceq
    1rp
    @79
    c1
    @23
    relogdiv
    sylancr
    @112
    cc0
    @24
    cmin
    co
    @107
    @111
    cc0
    @24
    cmin
    log1
    oveq1i
    @24
    df-neg
    eqtr4i
    syl6req
    @5
    @109
    @100
    cle
    wbr
    @110
    @101
    cle
    wbr
    @5
    c1
    @17
    cdiv
    co
    #
    @0
    cdiv
    co
    @2
    @0
    caddc
    co
    #
    cabs
    cfv
    #
    @0
    cdiv
    co
    #
    @109
    @100
    cle
    @5
    @114
    @116
    @0
    @5
    @17
    @77
    nnrecred
    #
    @5
    @115
    @5
    @2
    @0
    @59
    @66
    addcld
    #
    abscld
    #
    @61
    @5
    @114
    @37
    @116
    @118
    @5
    cR
    @33
    nnrecred
    @120
    @5
    cR
    @17
    c1
    @5
    cR
    @33
    nnrpd
    @78
    @88
    cc0
    c1
    cle
    wbr
    @5
    0le1
    a1i
    @5
    cR
    @75
    lep1d
    lediv2ad
    @5
    @0
    cn0
    wcel
    @95
    @37
    @116
    cle
    wbr
    #
    @5
    @0
    @60
    nnnn0d
    @5
    @91
    @95
    @98
    simprd
    @94
    @121
    vk
    @0
    cn0
    vk
    vn
    weq
    #
    @93
    @116
    @37
    cle
    @122
    @92
    @115
    cabs
    @38
    @0
    @2
    caddc
    oveq2
    fveq2d
    breq2d
    rspcv
    sylc
    letrd
    lediv1dd
    @5
    @17
    @0
    @5
    @17
    @77
    nncnd
    @66
    @5
    @17
    @77
    nnne0d
    @67
    recdiv2d
    @5
    @100
    @115
    @0
    cdiv
    co
    #
    cabs
    cfv
    @116
    @0
    cabs
    cfv
    #
    cdiv
    co
    @117
    @5
    @11
    @123
    cabs
    @5
    @123
    @10
    @0
    @0
    cdiv
    co
    #
    caddc
    co
    @11
    @5
    @2
    @0
    @0
    @59
    @66
    @66
    @67
    divdird
    @5
    @125
    c1
    @10
    caddc
    @5
    @0
    @66
    @67
    dividd
    oveq2d
    eqtr2d
    fveq2d
    @5
    @115
    @0
    @119
    @66
    @67
    absdivd
    @5
    @124
    @0
    @116
    cdiv
    @5
    @0
    @87
    @5
    @0
    @61
    rpge0d
    absidd
    #
    oveq2d
    3eqtrrd
    3brtr3d
    @5
    @109
    @100
    @5
    @23
    @79
    rpreccld
    @104
    logled
    mpbid
    eqbrtrd
    @5
    @100
    @23
    cle
    wbr
    @108
    @5
    @100
    @17
    @23
    @5
    @11
    @70
    abscld
    #
    @5
    cR
    c1
    @75
    @88
    readdcld
    #
    @5
    @23
    @79
    rpred
    @5
    @100
    @10
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    @17
    @127
    @5
    @129
    c1
    @5
    @10
    @68
    abscld
    #
    @88
    readdcld
    @128
    @5
    @100
    @129
    c1
    cabs
    cfv
    #
    caddc
    co
    @130
    cle
    @5
    @10
    c1
    @68
    @69
    abstrid
    @132
    c1
    @129
    caddc
    abs1
    oveq2i
    syl6breq
    @5
    @129
    cR
    c1
    @131
    @75
    @88
    @5
    @83
    @0
    cdiv
    co
    #
    cR
    c1
    cdiv
    co
    @129
    cR
    cle
    @5
    @83
    cR
    c1
    @0
    @90
    @75
    @113
    @5
    1rp
    a1i
    @87
    @5
    @2
    @59
    absge0d
    @99
    @5
    @0
    @60
    nnge1d
    #
    lediv12ad
    @5
    @129
    @83
    @124
    cdiv
    co
    @133
    @5
    @2
    @0
    @59
    @66
    @67
    absdivd
    @5
    @124
    @0
    @83
    cdiv
    @126
    oveq2d
    eqtr2d
    @5
    cR
    @5
    cR
    @33
    nncnd
    div1d
    3brtr3d
    leadd1dd
    letrd
    @5
    @17
    @0
    @128
    @87
    @5
    @17
    @78
    rpge0d
    @134
    lemulge11d
    letrd
    @5
    @100
    @23
    @104
    @79
    logled
    mpbid
    @5
    @101
    @24
    @105
    @80
    absled
    mpbir2and
    leadd1dd
    letrd
    le2addd
    letrd
    adantr
    ifbothda
    @5
    @29
    @13
    cabs
    @5
    @29
    @2
    vz
    cU
    vz
    cv
    #
    @8
    cmul
    co
    #
    @135
    @0
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    @13
    @5
    @2
    @28
    @141
    @1
    @28
    @141
    wceq
    wph
    @3
    vm
    @0
    vz
    cU
    @135
    vm
    cv
    #
    c1
    caddc
    co
    #
    @143
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    @135
    @143
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    @141
    cn
    cG
    vm
    vn
    weq
    #
    vz
    cU
    @151
    @140
    @152
    @147
    @136
    @150
    @139
    cmin
    @152
    @146
    @8
    @135
    cmul
    @152
    @145
    @7
    clog
    @152
    @144
    @6
    @143
    @0
    cdiv
    @143
    @0
    c1
    caddc
    oveq1
    @152
    id
    oveq12d
    fveq2d
    #
    oveq2d
    @152
    @149
    @138
    clog
    @152
    @148
    @137
    c1
    caddc
    @143
    @0
    @135
    cdiv
    oveq2
    oveq1d
    fveq2d
    oveq12d
    mpteq2dv
    lgamgulm.g
    vz
    cU
    @140
    @43
    vx
    cc
    cU
    lgamgulm.u
    cnex
    rabex2
    mptex
    fvmpt
    ad2antrl
    fveq1d
    @3
    @142
    @13
    wceq
    wph
    @1
    vz
    @2
    @140
    @13
    cU
    @141
    vz
    vy
    weq
    #
    @136
    @9
    @139
    @12
    cmin
    @135
    @2
    @8
    cmul
    oveq1
    @154
    @138
    @11
    clog
    @154
    @137
    @10
    c1
    caddc
    @135
    @2
    @0
    cdiv
    oveq1
    oveq1d
    fveq2d
    oveq12d
    @141
    eqid
    @9
    @12
    cmin
    ovex
    fvmpt
    ad2antll
    eqtrd
    fveq2d
    @1
    @30
    @27
    wceq
    wph
    @3
    vm
    @0
    @15
    @143
    cle
    wbr
    #
    cR
    @18
    @143
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cR
    @146
    cmul
    co
    #
    @17
    @143
    cmul
    co
    #
    clog
    cfv
    #
    cpi
    caddc
    co
    #
    caddc
    co
    #
    cif
    @27
    cn
    cT
    @152
    @155
    @16
    @158
    @163
    @21
    @26
    @143
    @0
    @15
    cle
    breq2
    @152
    @157
    @20
    cR
    cmul
    @152
    @156
    @19
    @18
    cdiv
    @143
    @0
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    @152
    @159
    @22
    @162
    @25
    caddc
    @152
    @146
    @8
    cR
    cmul
    @153
    oveq2d
    @152
    @161
    @24
    cpi
    caddc
    @152
    @160
    @23
    clog
    @143
    @0
    @17
    cmul
    oveq2
    fveq2d
    oveq1d
    oveq12d
    ifbieq12d
    lgamgulm.t
    @16
    @21
    @26
    cR
    @20
    cmul
    ovex
    @22
    @25
    caddc
    ovex
    ifex
    fvmpt
    ad2antrl
    3brtr4d
end
