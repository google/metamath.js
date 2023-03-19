include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "clog.mm"
include "csu.mm"
include "c2.mm"
include "cexp.mm"
include "cem.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cabs.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "relogcld.mm"
include "cn.mm"
include "adantl.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "cr.mm"
include "emre.mm"
include "remulcl.mm"
include "sylancr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "rpsup.mm"
include "a1i.mm"
include "cmpt.mm"
include "crli.mm"
include "wf.mm"
include "cdm.mm"
include "wbr.mm"
include "ceu.mm"
include "cle.mm"
include "w3a.mm"
include "wi.mm"
include "logdivsum.mm"
include "simp1i.mm"
include "feqmptd.mm"
include "eqbrtrrd.mm"
include "ffvelrni.mm"
include "rlimrecl.mm"
include "resubcld.mm"
include "readdcld.mm"
include "recnd.mm"
include "abscld.mm"
include "rerpdivcl.mm"
include "fsumcl.mm"
include "readdcl.mm"
include "sylancl.mm"
include "mulcld.mm"
include "subcld.mm"
include "addcld.mm"
include "2re.mm"
include "rerpdivcld.mm"
include "relogdiv.mm"
include "oveq1d.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "adantr.mm"
include "rpcnne0d.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "fsumsub.mm"
include "pncand.mm"
include "recni.mm"
include "adddid.mm"
include "2halvesd.mm"
include "sqvald.mm"
include "add32d.mm"
include "3eqtr2d.mm"
include "mulcom.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "eqeltrd.mm"
include "addsubassd.mm"
include "subsub4d.mm"
include "3eqtr3d.mm"
include "oveq12d.mm"
include "sub4d.mm"
include "fveq2d.mm"
include "abs2dif2d.mm"
include "eqbrtrd.mm"
include "harmonicbnd4.mm"
include "syl.mm"
include "wb.mm"
include "nnrecred.mm"
include "rprecred.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "loge.mm"
include "epr.mm"
include "logleb.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "subdid.mm"
include "absmuld.mm"
include "ltled.mm"
include "absidd.mm"
include "3eqtrd.mm"
include "3brtr4d.mm"
include "fveq2.mm"
include "id.mm"
include "cbvsumv.mm"
include "sumeq1d.mm"
include "syl5eq.mm"
include "ovex.mm"
include "fvmpt.mm"
include "simp3i.mm"
include "le2addd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "letrd.mm"

theorem mulog2sumlem1
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cL: class L
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cR: class R
  assume logdivsum.1: |- F = ( y e. RR+ |-> ( sum_ i e. ( 1 ... ( |_ ` y ) ) ( ( log ` i ) / i ) - ( ( ( log ` y ) ^ 2 ) / 2 ) ) )
  assume mulog2sumlem.1: |- ( ph -> F ~~>r L )
  assume mulog2sumlem1.2: |- ( ph -> A e. RR+ )
  assume mulog2sumlem1.3: |- ( ph -> _e <_ A )

  disjoint i m
  disjoint i y
  disjoint A i
  disjoint m y
  disjoint A m
  disjoint A y
  disjoint m ph
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint F x
  disjoint L n
  disjoint L x
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint R n
  disjoint R x
  assert |- ( ph -> ( abs ` ( sum_ m e. ( 1 ... ( |_ ` A ) ) ( ( log ` ( A / m ) ) / m ) - ( ( ( ( log ` A ) ^ 2 ) / 2 ) + ( ( gamma x. ( log ` A ) ) - L ) ) ) ) <_ ( 2 x. ( ( log ` A ) / A ) ) )

  proof
    wph
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cA
    vm
    cv
    #
    cdiv
    co
    #
    clog
    cfv
    #
    @2
    cdiv
    co
    #
    vm
    csu
    #
    cA
    clog
    cfv
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cem
    @7
    cmul
    co
    #
    cL
    cmin
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    @7
    @2
    cdiv
    co
    #
    vm
    csu
    #
    @7
    @7
    cem
    caddc
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    @2
    clog
    cfv
    #
    @2
    cdiv
    co
    #
    vm
    csu
    #
    @9
    cL
    caddc
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    c2
    @7
    cA
    cdiv
    co
    #
    cmul
    co
    #
    wph
    @13
    wph
    @13
    wph
    @6
    @12
    wph
    @1
    @5
    vm
    wph
    c1
    @0
    fzfid
    #
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @4
    @2
    @32
    @3
    wph
    cA
    crp
    wcel
    #
    @2
    crp
    wcel
    #
    @3
    crp
    wcel
    @31
    mulog2sumlem1.2
    @31
    @2
    @2
    @0
    elfznn
    #
    nnrpd
    #
    cA
    @2
    rpdivcl
    syl2an
    relogcld
    @31
    @2
    cn
    wcel
    wph
    @35
    adantl
    #
    nndivred
    fsumrecl
    wph
    @9
    @11
    wph
    @8
    wph
    @7
    wph
    cA
    mulog2sumlem1.2
    relogcld
    #
    resqcld
    #
    rehalfcld
    #
    wph
    @10
    cL
    wph
    cem
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @10
    cr
    wcel
    emre
    @38
    cem
    @7
    remulcl
    sylancr
    wph
    vx
    crp
    vx
    cv
    #
    cF
    cfv
    #
    cL
    crp
    cxr
    clt
    csup
    cpnf
    wceq
    wph
    rpsup
    a1i
    wph
    cF
    vx
    crp
    @44
    cmpt
    cL
    crli
    wph
    vx
    crp
    cr
    cF
    crp
    cr
    cF
    wf
    #
    wph
    @45
    cF
    crli
    cdm
    wcel
    #
    cF
    cL
    crli
    wbr
    #
    @33
    ceu
    cA
    cle
    wbr
    #
    w3a
    cA
    cF
    cfv
    #
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    @28
    cle
    wbr
    #
    wi
    #
    vy
    cA
    vi
    cF
    cL
    logdivsum.1
    logdivsum
    #
    simp1i
    #
    a1i
    feqmptd
    mulog2sumlem.1
    eqbrtrrd
    @43
    crp
    wcel
    @44
    cr
    wcel
    wph
    crp
    cr
    @43
    cF
    @55
    ffvelrni
    adantl
    rlimrecl
    #
    resubcld
    readdcld
    resubcld
    recnd
    abscld
    wph
    @20
    @26
    wph
    @19
    wph
    @16
    @18
    wph
    @1
    @15
    vm
    @30
    @32
    @15
    wph
    @42
    @34
    @15
    cr
    wcel
    @31
    @38
    @36
    @7
    @2
    rerpdivcl
    syl2an
    recnd
    #
    fsumcl
    #
    wph
    @7
    @17
    wph
    @7
    @38
    recnd
    #
    wph
    @17
    wph
    @42
    @41
    @17
    cr
    wcel
    @38
    emre
    @7
    cem
    readdcl
    sylancl
    #
    recnd
    #
    mulcld
    #
    subcld
    #
    abscld
    #
    wph
    @25
    wph
    @23
    @24
    wph
    @1
    @22
    vm
    @30
    @32
    @22
    @32
    @21
    @2
    @32
    @2
    @32
    @2
    @37
    nnrpd
    #
    relogcld
    #
    @37
    nndivred
    recnd
    #
    fsumcl
    #
    wph
    @9
    cL
    wph
    @9
    @40
    recnd
    #
    wph
    cL
    @56
    recnd
    #
    addcld
    #
    subcld
    #
    abscld
    #
    readdcld
    wph
    c2
    cr
    wcel
    @28
    cr
    wcel
    @29
    cr
    wcel
    2re
    wph
    @7
    cA
    @38
    mulog2sumlem1.2
    rerpdivcld
    #
    c2
    @28
    remulcl
    sylancr
    wph
    @14
    @19
    @25
    cmin
    co
    #
    cabs
    cfv
    @27
    cle
    wph
    @13
    @75
    cabs
    wph
    @13
    @16
    @23
    cmin
    co
    #
    @18
    @24
    cmin
    co
    #
    cmin
    co
    @75
    wph
    @6
    @76
    @12
    @77
    cmin
    wph
    @6
    @1
    @15
    @22
    cmin
    co
    #
    vm
    csu
    @76
    wph
    @1
    @5
    @78
    vm
    @32
    @5
    @7
    @21
    cmin
    co
    #
    @2
    cdiv
    co
    #
    @78
    @32
    @4
    @79
    @2
    cdiv
    wph
    @33
    @34
    @4
    @79
    wceq
    @31
    mulog2sumlem1.2
    @36
    cA
    @2
    relogdiv
    syl2an
    oveq1d
    @32
    @7
    cc
    wcel
    #
    @21
    cc
    wcel
    @2
    cc
    wcel
    @2
    cc0
    wne
    wa
    @80
    @78
    wceq
    wph
    @81
    @31
    @59
    adantr
    #
    @32
    @21
    @66
    recnd
    @32
    @2
    @65
    rpcnne0d
    @7
    @21
    @2
    divsubdir
    syl3anc
    eqtrd
    sumeq2dv
    wph
    @1
    @15
    @22
    vm
    @30
    @57
    @67
    fsumsub
    eqtrd
    wph
    @9
    @10
    caddc
    co
    #
    cL
    cmin
    co
    @18
    @9
    cmin
    co
    #
    cL
    cmin
    co
    @12
    @77
    wph
    @83
    @84
    cL
    cmin
    wph
    @9
    @7
    cem
    cmul
    co
    #
    caddc
    co
    #
    @9
    caddc
    co
    #
    @9
    cmin
    co
    @86
    @84
    @83
    wph
    @86
    @9
    wph
    @86
    wph
    @9
    @85
    @40
    wph
    @42
    @41
    @85
    cr
    wcel
    @38
    emre
    @7
    cem
    remulcl
    sylancl
    #
    readdcld
    recnd
    @69
    pncand
    wph
    @18
    @87
    @9
    cmin
    wph
    @18
    @7
    @7
    cmul
    co
    #
    @85
    caddc
    co
    @9
    @9
    caddc
    co
    #
    @85
    caddc
    co
    @87
    wph
    @7
    @7
    cem
    @59
    @59
    cem
    cc
    wcel
    #
    wph
    cem
    emre
    recni
    #
    a1i
    adddid
    wph
    @90
    @89
    @85
    caddc
    wph
    @90
    @8
    @89
    wph
    @8
    wph
    @8
    @39
    recnd
    2halvesd
    wph
    @7
    @59
    sqvald
    eqtrd
    oveq1d
    wph
    @9
    @9
    @85
    @69
    @69
    wph
    @85
    @88
    recnd
    #
    add32d
    3eqtr2d
    oveq1d
    wph
    @10
    @85
    @9
    caddc
    wph
    @91
    @81
    @10
    @85
    wceq
    @92
    @59
    cem
    @7
    mulcom
    sylancr
    #
    oveq2d
    3eqtr4rd
    oveq1d
    wph
    @9
    @10
    cL
    @69
    wph
    @10
    @85
    cc
    @94
    @93
    eqeltrd
    @70
    addsubassd
    wph
    @18
    @9
    cL
    @62
    @69
    @70
    subsub4d
    3eqtr3d
    oveq12d
    wph
    @16
    @23
    @18
    @24
    @58
    @68
    @62
    @71
    sub4d
    eqtrd
    fveq2d
    wph
    @19
    @25
    @63
    @72
    abs2dif2d
    eqbrtrd
    wph
    @27
    @28
    @28
    caddc
    co
    @29
    cle
    wph
    @20
    @26
    @28
    @28
    @64
    @73
    @74
    @74
    wph
    @7
    @1
    c1
    @2
    cdiv
    co
    #
    vm
    csu
    #
    @17
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @7
    c1
    cA
    cdiv
    co
    #
    cmul
    co
    #
    @20
    @28
    cle
    wph
    @98
    @100
    cle
    wbr
    #
    @99
    @101
    cle
    wbr
    #
    wph
    @33
    @102
    mulog2sumlem1.2
    cA
    vm
    harmonicbnd4
    syl
    wph
    @98
    cr
    wcel
    @100
    cr
    wcel
    @42
    cc0
    @7
    clt
    wbr
    @102
    @103
    wb
    wph
    @97
    wph
    @97
    wph
    @96
    @17
    wph
    @1
    @95
    vm
    @30
    @32
    @2
    @37
    nnrecred
    #
    fsumrecl
    @60
    resubcld
    recnd
    abscld
    wph
    cA
    mulog2sumlem1.2
    rprecred
    @38
    wph
    cc0
    c1
    @7
    wph
    0red
    #
    wph
    1red
    @38
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    c1
    ceu
    clog
    cfv
    #
    @7
    cle
    loge
    wph
    @48
    @106
    @7
    cle
    wbr
    #
    mulog2sumlem1.3
    wph
    ceu
    crp
    wcel
    @33
    @48
    @107
    wb
    epr
    mulog2sumlem1.2
    ceu
    cA
    logleb
    sylancr
    mpbid
    syl5eqbrr
    ltletrd
    #
    @98
    @100
    @7
    lemul2
    syl112anc
    mpbid
    wph
    @20
    @7
    @97
    cmul
    co
    #
    cabs
    cfv
    @7
    cabs
    cfv
    #
    @98
    cmul
    co
    @99
    wph
    @19
    @109
    cabs
    wph
    @19
    @7
    @96
    cmul
    co
    #
    @18
    cmin
    co
    @109
    wph
    @16
    @111
    @18
    cmin
    wph
    @16
    @1
    @7
    @95
    cmul
    co
    #
    vm
    csu
    @111
    wph
    @1
    @15
    @112
    vm
    @32
    @7
    @2
    @82
    @32
    @2
    @65
    rpcnd
    @32
    @2
    @65
    rpne0d
    divrecd
    sumeq2dv
    wph
    @1
    @95
    @7
    vm
    @30
    @59
    @32
    @95
    @104
    recnd
    #
    fsummulc2
    eqtr4d
    oveq1d
    wph
    @7
    @96
    @17
    @59
    wph
    @1
    @95
    vm
    @30
    @113
    fsumcl
    #
    @61
    subdid
    eqtr4d
    fveq2d
    wph
    @7
    @97
    @59
    wph
    @96
    @17
    @114
    @61
    subcld
    absmuld
    wph
    @110
    @7
    @98
    cmul
    wph
    @7
    @38
    wph
    cc0
    @7
    @105
    @38
    @108
    ltled
    absidd
    oveq1d
    3eqtrd
    wph
    @7
    cA
    @59
    wph
    cA
    mulog2sumlem1.2
    rpcnd
    wph
    cA
    mulog2sumlem1.2
    rpne0d
    divrecd
    3brtr4d
    wph
    @51
    @26
    @28
    cle
    wph
    @50
    @25
    cabs
    wph
    @50
    @23
    @9
    cmin
    co
    #
    cL
    cmin
    co
    @25
    wph
    @49
    @115
    cL
    cmin
    wph
    @33
    @49
    @115
    wceq
    mulog2sumlem1.2
    vy
    cA
    c1
    vy
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vi
    cv
    #
    clog
    cfv
    #
    @119
    cdiv
    co
    #
    vi
    csu
    #
    @116
    clog
    cfv
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    @115
    crp
    cF
    @116
    cA
    wceq
    #
    @122
    @23
    @125
    @9
    cmin
    @126
    @122
    @118
    @22
    vm
    csu
    @23
    @118
    @121
    @22
    vi
    vm
    @119
    @2
    wceq
    #
    @120
    @21
    @119
    @2
    cdiv
    @119
    @2
    clog
    fveq2
    @127
    id
    oveq12d
    cbvsumv
    @126
    @118
    @1
    @22
    vm
    @126
    @117
    @0
    c1
    cfz
    @116
    cA
    cfl
    fveq2
    oveq2d
    sumeq1d
    syl5eq
    @126
    @124
    @8
    c2
    cdiv
    @126
    @123
    @7
    c2
    cexp
    @116
    cA
    clog
    fveq2
    oveq1d
    oveq1d
    oveq12d
    logdivsum.1
    @23
    @9
    cmin
    ovex
    fvmpt
    syl
    oveq1d
    wph
    @23
    @9
    cL
    @68
    @69
    @70
    subsub4d
    eqtrd
    fveq2d
    wph
    @47
    @33
    @48
    @52
    mulog2sumlem.1
    mulog2sumlem1.2
    mulog2sumlem1.3
    @45
    @46
    @53
    @54
    simp3i
    syl3anc
    eqbrtrrd
    le2addd
    wph
    @28
    wph
    @28
    @74
    recnd
    2timesd
    breqtrrd
    letrd
end
