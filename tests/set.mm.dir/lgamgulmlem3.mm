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
include "cexp.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "lgamgulmlem1.mm"
include "sseldd.mm"
include "eldifad.mm"
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
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "1red.mm"
include "remulcld.mm"
include "nnsqcld.mm"
include "nndivred.mm"
include "abs3difd.mm"
include "nnrecred.mm"
include "resubcld.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "ltaddrpd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "ltletrd.mm"
include "wb.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rprecred.mm"
include "cle.mm"
include "divrecd.mm"
include "oveq2d.mm"
include "subdid.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "eqtrd.mm"
include "absge0d.mm"
include "cv.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "simpld.mm"
include "relogdivd.mm"
include "logdifbnd.mm"
include "eqbrtrd.mm"
include "abssuble0d.mm"
include "logdiflbnd.mm"
include "lesub2dd.mm"
include "lemul12ad.mm"
include "lgamgulmlem2.mm"
include "le2addd.mm"
include "gtned.mm"
include "subne0d.mm"
include "subrecd.mm"
include "pnncand.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "reccld.mm"
include "npncan3d.mm"
include "eqcomd.mm"
include "adddid.mm"
include "3eqtrd.mm"
include "rpmulcld.mm"
include "rerpdivcld.mm"
include "rpge0d.mm"
include "2z.mm"
include "rpexpcld.mm"
include "rphalfcld.mm"
include "cc0.mm"
include "0le1.mm"
include "addge0d.mm"
include "sqvald.mm"
include "wne.mm"
include "2ne0.mm"
include "div23d.mm"
include "rehalfcld.mm"
include "2rp.mm"
include "divge0d.mm"
include "lemuldiv2d.mm"
include "2halvesd.mm"
include "subaddd.mm"
include "mpbird.mm"
include "lesubd.mm"
include "lep1d.mm"
include "lediv2ad.mm"
include "divdiv2d.mm"
include "mulcomd.mm"
include "lemul2ad.mm"
include "eqbrtrrd.mm"
include "letrd.mm"

theorem lgamgulmlem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cU: class U
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let cG: class G
  let vt: setvar t
  let vm: setvar m
  let vz: setvar z
  let cO: class O
  let cT: class T
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.n: |- ( ph -> N e. NN )
  assume lgamgulm.a: |- ( ph -> A e. U )
  assume lgamgulm.l: |- ( ph -> ( 2 x. R ) <_ N )

  disjoint N x
  disjoint k x
  disjoint R k
  disjoint R x
  disjoint A k
  disjoint A x
  disjoint ph x
  disjoint n r
  disjoint n y
  disjoint G n
  disjoint r y
  disjoint G r
  disjoint G y
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint x y
  disjoint N y
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint R m
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint R n
  disjoint r t
  disjoint r x
  disjoint r z
  disjoint R r
  disjoint t z
  disjoint R t
  disjoint x z
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint U m
  disjoint U n
  disjoint U r
  disjoint U t
  disjoint U y
  disjoint U z
  disjoint A m
  disjoint A t
  disjoint A y
  disjoint O n
  disjoint O r
  disjoint O y
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph y
  disjoint ph z
  disjoint T n
  disjoint T r
  disjoint T y
  assert |- ( ph -> ( abs ` ( ( A x. ( log ` ( ( N + 1 ) / N ) ) ) - ( log ` ( ( A / N ) + 1 ) ) ) ) <_ ( R x. ( ( 2 x. ( R + 1 ) ) / ( N ^ 2 ) ) ) )

  proof
    wph
    cA
    cN
    c1
    caddc
    co
    #
    cN
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cA
    cN
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
    @3
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
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
    cN
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
    wph
    @7
    wph
    @3
    @6
    wph
    cA
    @2
    wph
    cA
    cc
    cz
    cn
    cdif
    #
    wph
    cU
    cc
    @18
    cdif
    cA
    wph
    vx
    cR
    cU
    vk
    lgamgulm.r
    lgamgulm.u
    lgamgulmlem1
    lgamgulm.a
    sseldd
    #
    eldifad
    #
    wph
    @2
    wph
    @1
    wph
    @0
    cN
    wph
    @0
    wph
    cN
    lgamgulm.n
    peano2nnd
    #
    nnrpd
    #
    wph
    cN
    lgamgulm.n
    nnrpd
    #
    rpdivcld
    relogcld
    #
    recnd
    #
    mulcld
    #
    wph
    @5
    wph
    @4
    c1
    wph
    cA
    cN
    @20
    wph
    cN
    lgamgulm.n
    nncnd
    #
    wph
    cN
    lgamgulm.n
    nnne0d
    #
    divcld
    #
    wph
    1cnd
    #
    addcld
    wph
    cA
    cN
    @19
    lgamgulm.n
    dmgmdivn0
    logcld
    #
    subcld
    abscld
    wph
    @9
    @11
    wph
    @8
    wph
    @3
    @4
    @26
    @29
    subcld
    abscld
    #
    wph
    @10
    wph
    @4
    @6
    @29
    @31
    subcld
    abscld
    #
    readdcld
    #
    wph
    cR
    @16
    wph
    cR
    lgamgulm.r
    nnred
    #
    wph
    @14
    @15
    wph
    c2
    @13
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    cR
    c1
    @35
    wph
    1red
    #
    readdcld
    #
    remulcld
    wph
    cN
    lgamgulm.n
    nnsqcld
    #
    nndivred
    #
    remulcld
    #
    wph
    @3
    @6
    @4
    @26
    @31
    @29
    abs3difd
    wph
    @12
    cR
    c1
    cN
    cdiv
    co
    #
    c1
    @0
    cdiv
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    cR
    c1
    cN
    cR
    cmin
    co
    #
    cdiv
    co
    #
    @42
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @17
    @34
    wph
    @45
    @49
    wph
    cR
    @44
    @35
    wph
    @42
    @43
    wph
    cN
    lgamgulm.n
    nnrecred
    #
    wph
    @0
    @21
    nnrecred
    #
    resubcld
    #
    remulcld
    #
    wph
    cR
    @48
    @35
    wph
    @47
    @42
    wph
    @46
    wph
    cR
    cN
    clt
    wbr
    #
    @46
    crp
    wcel
    #
    wph
    cR
    c2
    cR
    cmul
    co
    #
    cN
    @35
    wph
    c2
    cR
    @36
    @35
    remulcld
    wph
    cN
    lgamgulm.n
    nnred
    #
    wph
    cR
    cR
    cR
    caddc
    co
    @57
    clt
    wph
    cR
    cR
    @35
    wph
    cR
    lgamgulm.r
    nnrpd
    #
    ltaddrpd
    wph
    cR
    wph
    cR
    lgamgulm.r
    nncnd
    #
    2timesd
    breqtrrd
    lgamgulm.l
    ltletrd
    #
    wph
    cR
    cr
    wcel
    cN
    cr
    wcel
    @55
    @56
    wb
    @35
    @58
    cR
    cN
    difrp
    syl2anc
    mpbid
    #
    rprecred
    @51
    resubcld
    #
    remulcld
    #
    readdcld
    @41
    wph
    @9
    @11
    @45
    @49
    @32
    @33
    @54
    @64
    wph
    @9
    cA
    cabs
    cfv
    #
    @2
    @42
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @45
    cle
    wph
    @9
    cA
    @66
    cmul
    co
    #
    cabs
    cfv
    @68
    wph
    @8
    @69
    cabs
    wph
    @8
    @3
    cA
    @42
    cmul
    co
    #
    cmin
    co
    @69
    wph
    @4
    @70
    @3
    cmin
    wph
    cA
    cN
    @20
    @27
    @28
    divrecd
    oveq2d
    wph
    cA
    @2
    @42
    @20
    @25
    wph
    @42
    @51
    recnd
    #
    subdid
    eqtr4d
    fveq2d
    wph
    cA
    @66
    @20
    wph
    @2
    @42
    @25
    @71
    subcld
    #
    absmuld
    eqtrd
    wph
    @65
    cR
    @67
    @44
    wph
    cA
    @20
    abscld
    @35
    wph
    @66
    @72
    abscld
    @53
    wph
    cA
    @20
    absge0d
    wph
    @66
    @72
    absge0d
    wph
    @65
    cR
    cle
    wbr
    #
    c1
    cR
    cdiv
    co
    #
    cA
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
    wph
    cA
    cU
    wcel
    #
    @73
    @79
    wa
    #
    lgamgulm.a
    @80
    cA
    cc
    wcel
    @81
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
    @74
    @82
    @75
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
    @81
    vx
    cA
    cc
    cU
    @82
    cA
    wceq
    #
    @84
    @73
    @88
    @79
    @89
    @83
    @65
    cR
    cle
    @82
    cA
    cabs
    fveq2
    breq1d
    @89
    @87
    @78
    vk
    cn0
    @89
    @86
    @77
    @74
    cle
    @89
    @85
    @76
    cabs
    @82
    cA
    @75
    caddc
    oveq1
    fveq2d
    breq2d
    ralbidv
    anbi12d
    lgamgulm.u
    elrab2
    simprbi
    syl
    simpld
    wph
    @67
    @42
    @2
    cmin
    co
    @44
    cle
    wph
    @2
    @42
    @24
    @51
    wph
    @2
    @0
    clog
    cfv
    cN
    clog
    cfv
    cmin
    co
    #
    @42
    cle
    wph
    @0
    cN
    @22
    @23
    relogdivd
    #
    wph
    cN
    crp
    wcel
    #
    @90
    @42
    cle
    wbr
    @23
    cN
    logdifbnd
    syl
    eqbrtrd
    abssuble0d
    wph
    @43
    @2
    @42
    @52
    @24
    @51
    wph
    @43
    @90
    @2
    cle
    wph
    @92
    @43
    @90
    cle
    wbr
    @23
    cN
    logdiflbnd
    syl
    @91
    breqtrrd
    lesub2dd
    eqbrtrd
    lemul12ad
    eqbrtrd
    wph
    vx
    cA
    cR
    cU
    vk
    cN
    lgamgulm.r
    lgamgulm.u
    lgamgulm.n
    lgamgulm.a
    lgamgulm.l
    lgamgulmlem2
    le2addd
    wph
    cR
    @13
    @46
    @0
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @50
    @17
    cle
    wph
    @95
    cR
    @47
    @43
    cmin
    co
    #
    cmul
    co
    cR
    @44
    @48
    caddc
    co
    #
    cmul
    co
    @50
    wph
    @94
    @96
    cR
    cmul
    wph
    @96
    @0
    @46
    cmin
    co
    #
    @93
    cdiv
    co
    @94
    wph
    @46
    @0
    wph
    cN
    cR
    @27
    @60
    subcld
    #
    wph
    cN
    c1
    @27
    @30
    addcld
    #
    wph
    cN
    cR
    @27
    @60
    wph
    cR
    cN
    @35
    @61
    gtned
    subne0d
    #
    wph
    @0
    @21
    nnne0d
    #
    subrecd
    wph
    @98
    @13
    @93
    cdiv
    wph
    @98
    c1
    cR
    caddc
    co
    @13
    wph
    cN
    c1
    cR
    @27
    @30
    @60
    pnncand
    wph
    c1
    cR
    @30
    @60
    addcomd
    eqtrd
    oveq1d
    eqtr2d
    oveq2d
    wph
    @96
    @97
    cR
    cmul
    wph
    @97
    @96
    wph
    @42
    @43
    @47
    @71
    wph
    @0
    @100
    @102
    reccld
    wph
    @46
    @99
    @101
    reccld
    npncan3d
    eqcomd
    oveq2d
    wph
    cR
    @44
    @48
    @60
    wph
    @44
    @53
    recnd
    wph
    @48
    @63
    recnd
    adddid
    3eqtrd
    wph
    @94
    @16
    cR
    wph
    @13
    @93
    @38
    wph
    @46
    @0
    @62
    @22
    rpmulcld
    #
    rerpdivcld
    @40
    @35
    wph
    cR
    @59
    rpge0d
    #
    wph
    @94
    @13
    @15
    c2
    cdiv
    co
    #
    cdiv
    co
    #
    @16
    cle
    wph
    @105
    @93
    @13
    wph
    @15
    wph
    cN
    c2
    @23
    c2
    cz
    wcel
    wph
    2z
    a1i
    rpexpcld
    rphalfcld
    @103
    @38
    wph
    cR
    c1
    @35
    @37
    @104
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    addge0d
    wph
    @105
    cN
    c2
    cdiv
    co
    #
    cN
    cmul
    co
    #
    @93
    cle
    wph
    @105
    cN
    cN
    cmul
    co
    #
    c2
    cdiv
    co
    @108
    wph
    @15
    @109
    c2
    cdiv
    wph
    cN
    @27
    sqvald
    oveq1d
    wph
    cN
    cN
    c2
    @27
    @27
    wph
    c2
    @36
    recnd
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    div23d
    eqtrd
    wph
    @107
    @46
    cN
    @0
    wph
    cN
    @58
    rehalfcld
    #
    wph
    cN
    cR
    @58
    @35
    resubcld
    @58
    wph
    cN
    c1
    @58
    @37
    readdcld
    wph
    cN
    c2
    @58
    c2
    crp
    wcel
    wph
    2rp
    a1i
    #
    wph
    cN
    @23
    rpge0d
    #
    divge0d
    @114
    wph
    cR
    cN
    @107
    @35
    @58
    @112
    wph
    cR
    @107
    cN
    @107
    cmin
    co
    #
    cle
    wph
    @57
    cN
    cle
    wbr
    cR
    @107
    cle
    wbr
    lgamgulm.l
    wph
    cR
    cN
    c2
    @35
    @58
    @113
    lemuldiv2d
    mpbid
    wph
    @115
    @107
    wceq
    @107
    @107
    caddc
    co
    cN
    wceq
    wph
    cN
    @27
    2halvesd
    wph
    cN
    @107
    @107
    @27
    wph
    @107
    @112
    recnd
    #
    @116
    subaddd
    mpbird
    breqtrrd
    lesubd
    wph
    cN
    @58
    lep1d
    lemul12ad
    eqbrtrd
    lediv2ad
    wph
    @106
    @13
    c2
    cmul
    co
    #
    @15
    cdiv
    co
    @16
    wph
    @13
    @15
    c2
    wph
    @13
    wph
    cR
    lgamgulm.r
    peano2nnd
    nncnd
    #
    wph
    @15
    @39
    nncnd
    @110
    wph
    @15
    @39
    nnne0d
    @111
    divdiv2d
    wph
    @117
    @14
    @15
    cdiv
    wph
    @13
    c2
    @118
    @110
    mulcomd
    oveq1d
    eqtr2d
    breqtrrd
    lemul2ad
    eqbrtrrd
    letrd
    letrd
end
