include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "clog.mm"
include "c2.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "vmalogdivsum2.mm"
include "a1i.mm"
include "wa.mm"
include "fzfid.mm"
include "cn.mm"
include "cr.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "remulcld.mm"
include "elioore.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "crp.mm"
include "1rp.mm"
include "1red.mm"
include "ltled.mm"
include "rpgecld.mm"
include "relogcld.mm"
include "rehalfcld.mm"
include "resubcld.mm"
include "recnd.mm"
include "adantr.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpne0d.mm"
include "divsubdird.mm"
include "subdid.mm"
include "sumeq2dv.mm"
include "fsumsub.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "nnncan2d.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "rpred.mm"
include "wss.mm"
include "cc.mm"
include "ioossre.mm"
include "1cnd.mm"
include "o1const.mm"
include "sylancr.mm"
include "subcld.mm"
include "divrecd.mm"
include "dividd.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "ssrdv.mm"
include "vmadivsum.mm"
include "o1res2.mm"
include "cc0.mm"
include "crli.mm"
include "divlogrlim.mm"
include "rlimo1.mm"
include "mp1i.mm"
include "o1mul2.mm"
include "eqeltrrd.mm"
include "o1dif.mm"
include "mpbird.mm"
include "divcld.mm"
include "cabs.mm"
include "cle.mm"
include "abscld.mm"
include "fsumabs.mm"
include "absmuld.mm"
include "vmage0.mm"
include "divge0d.mm"
include "absidd.mm"
include "cico.mm"
include "wral.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "wb.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "eqbrtrd.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "sumeq1d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "lemul2ad.mm"
include "fsumle.mm"
include "fsummulc1.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "lediv1dd.mm"
include "absdivd.mm"
include "rpge0d.mm"
include "fsumge0.mm"
include "mulge0d.mm"
include "div23d.mm"
include "eqtr4d.mm"
include "3brtr4d.mm"
include "adantrr.mm"
include "o1le.mm"

theorem 2vmadivsumlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  assume 2vmadivsum.1: |- ( ph -> A e. RR+ )
  assume 2vmadivsum.2: |- ( ph -> A. y e. ( 1 [,) +oo ) ( abs ` ( sum_ i e. ( 1 ... ( |_ ` y ) ) ( ( Lam ` i ) / i ) - ( log ` y ) ) ) <_ A )

  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( x e. ( 1 (,) +oo ) |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) / n ) x. sum_ m e. ( 1 ... ( |_ ` ( x / n ) ) ) ( ( Lam ` m ) / m ) ) / ( log ` x ) ) - ( ( log ` x ) / 2 ) ) ) e. O(1) )

  proof
    wph
    vx
    c1
    cpnf
    cioo
    co
    #
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @4
    cdiv
    co
    #
    c1
    @1
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vm
    cv
    #
    cvma
    cfv
    #
    @10
    cdiv
    co
    #
    vm
    csu
    #
    cmul
    co
    #
    vn
    csu
    #
    @1
    clog
    cfv
    #
    cdiv
    co
    #
    @16
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    co1
    wcel
    vx
    @0
    @3
    @6
    @7
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    @16
    cdiv
    co
    #
    @18
    cmin
    co
    #
    cmpt
    co1
    wcel
    #
    @25
    wph
    vx
    vn
    vmalogdivsum2
    a1i
    wph
    vx
    @0
    @19
    @24
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @19
    @27
    @17
    @18
    @27
    @15
    @16
    @27
    @3
    @14
    vn
    @27
    c1
    @2
    fzfid
    #
    @27
    @4
    @3
    wcel
    #
    wa
    #
    @6
    @13
    @30
    @5
    @4
    @30
    @4
    cn
    wcel
    #
    @5
    cr
    wcel
    @29
    @31
    @27
    @4
    @2
    elfznn
    adantl
    #
    @4
    vmacl
    syl
    #
    @32
    nndivred
    #
    @30
    @9
    @12
    vm
    @30
    c1
    @8
    fzfid
    @30
    @10
    @9
    wcel
    #
    wa
    #
    @11
    @10
    @36
    @10
    cn
    wcel
    #
    @11
    cr
    wcel
    @35
    @37
    @30
    @10
    @8
    elfznn
    adantl
    #
    @10
    vmacl
    syl
    @38
    nndivred
    fsumrecl
    #
    remulcld
    #
    fsumrecl
    #
    @27
    @1
    @26
    @1
    cr
    wcel
    #
    wph
    @1
    c1
    cpnf
    elioore
    adantl
    #
    @27
    c1
    @1
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    @26
    @44
    @45
    wa
    wph
    @1
    c1
    cpnf
    eliooord
    adantl
    simpld
    #
    rplogcld
    #
    rerpdivcld
    #
    @27
    @16
    @27
    @1
    @27
    @1
    c1
    @43
    c1
    crp
    wcel
    @27
    1rp
    a1i
    @27
    c1
    @1
    @27
    1red
    #
    @43
    @46
    ltled
    rpgecld
    #
    relogcld
    #
    rehalfcld
    #
    resubcld
    recnd
    @27
    @24
    @27
    @23
    @18
    @27
    @22
    @16
    @27
    @3
    @21
    vn
    @28
    @30
    @6
    @20
    @34
    @30
    @7
    @30
    @1
    @4
    @27
    @1
    crp
    wcel
    #
    @29
    @50
    adantr
    @30
    @4
    @32
    nnrpd
    #
    rpdivcld
    #
    relogcld
    #
    remulcld
    #
    fsumrecl
    #
    @47
    rerpdivcld
    #
    @52
    resubcld
    recnd
    wph
    vx
    @0
    @3
    @6
    @13
    @20
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @16
    cdiv
    co
    #
    cmpt
    vx
    @0
    @19
    @24
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    @0
    @63
    @64
    @27
    @15
    @22
    cmin
    co
    #
    @16
    cdiv
    co
    @17
    @23
    cmin
    co
    @63
    @64
    @27
    @15
    @22
    @16
    @27
    @15
    @41
    recnd
    @27
    @22
    @58
    recnd
    @27
    @16
    @51
    recnd
    #
    @27
    @16
    @47
    rpne0d
    #
    divsubdird
    @27
    @62
    @65
    @16
    cdiv
    @27
    @62
    @3
    @14
    @21
    cmin
    co
    #
    vn
    csu
    @65
    @27
    @3
    @61
    @68
    vn
    @30
    @6
    @13
    @20
    @30
    @6
    @34
    recnd
    #
    @30
    @13
    @39
    recnd
    @30
    @20
    @56
    recnd
    subdid
    sumeq2dv
    @27
    @3
    @14
    @21
    vn
    @28
    @30
    @14
    @40
    recnd
    @30
    @21
    @57
    recnd
    fsumsub
    eqtrd
    oveq1d
    @27
    @17
    @23
    @18
    @27
    @17
    @48
    recnd
    @27
    @23
    @59
    recnd
    @27
    @18
    @52
    recnd
    nnncan2d
    3eqtr4d
    mpteq2dva
    wph
    vx
    @0
    @3
    @6
    vn
    csu
    #
    @16
    cdiv
    co
    #
    cA
    cmul
    co
    #
    @63
    c1
    cr
    wph
    1red
    wph
    vx
    @0
    @71
    cA
    cr
    @27
    @70
    @16
    @27
    @3
    @6
    vn
    @28
    @34
    fsumrecl
    #
    @47
    rerpdivcld
    #
    wph
    cA
    cr
    wcel
    #
    @26
    wph
    cA
    2vmadivsum.1
    rpred
    #
    adantr
    #
    wph
    vx
    @0
    @71
    cmpt
    co1
    wcel
    vx
    @0
    c1
    cmpt
    co1
    wcel
    #
    wph
    @0
    cr
    wss
    #
    c1
    cc
    wcel
    @78
    c1
    cpnf
    ioossre
    #
    wph
    1cnd
    vx
    @0
    c1
    o1const
    sylancr
    wph
    vx
    @0
    @71
    c1
    @27
    @71
    @74
    recnd
    @27
    1cnd
    wph
    vx
    @0
    @70
    @16
    cmin
    co
    #
    c1
    @16
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    vx
    @0
    @71
    c1
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    @0
    @83
    @84
    @27
    @81
    @16
    cdiv
    co
    @71
    @16
    @16
    cdiv
    co
    #
    cmin
    co
    @83
    @84
    @27
    @70
    @16
    @16
    @27
    @70
    @73
    recnd
    #
    @66
    @66
    @67
    divsubdird
    @27
    @81
    @16
    @27
    @70
    @16
    @86
    @66
    subcld
    @66
    @67
    divrecd
    @27
    @85
    c1
    @71
    cmin
    @27
    @16
    @66
    @67
    dividd
    oveq2d
    3eqtr3d
    mpteq2dva
    wph
    vx
    @0
    @81
    @82
    cr
    @27
    @70
    @16
    @73
    @51
    resubcld
    @27
    c1
    @16
    @49
    @47
    rerpdivcld
    wph
    vx
    @0
    crp
    @81
    wph
    vx
    @0
    crp
    wph
    @26
    @53
    @50
    ex
    ssrdv
    vx
    crp
    @81
    cmpt
    co1
    wcel
    wph
    vx
    vn
    vmadivsum
    a1i
    o1res2
    vx
    @0
    @82
    cmpt
    #
    cc0
    crli
    wbr
    @87
    co1
    wcel
    wph
    vx
    divlogrlim
    cc0
    @87
    rlimo1
    mp1i
    o1mul2
    eqeltrrd
    o1dif
    mpbird
    wph
    @79
    cA
    cc
    wcel
    #
    vx
    @0
    cA
    cmpt
    co1
    wcel
    @80
    wph
    cA
    @76
    recnd
    #
    vx
    @0
    cA
    o1const
    sylancr
    o1mul2
    @27
    @71
    cA
    @74
    @77
    remulcld
    #
    @27
    @62
    @16
    @27
    @62
    @27
    @3
    @61
    vn
    @28
    @30
    @6
    @60
    @34
    @30
    @13
    @20
    @39
    @56
    resubcld
    #
    remulcld
    #
    fsumrecl
    recnd
    #
    @66
    @67
    divcld
    wph
    @26
    @63
    cabs
    cfv
    #
    @72
    cabs
    cfv
    #
    cle
    wbr
    c1
    @1
    cle
    wbr
    @27
    @62
    cabs
    cfv
    #
    @16
    cdiv
    co
    #
    @70
    cA
    cmul
    co
    #
    @16
    cdiv
    co
    #
    @94
    @95
    cle
    @27
    @96
    @98
    @16
    @27
    @62
    @93
    abscld
    #
    @27
    @70
    cA
    @73
    @77
    remulcld
    #
    @47
    @27
    @96
    @3
    @61
    cabs
    cfv
    #
    vn
    csu
    #
    @98
    @100
    @27
    @3
    @102
    vn
    @28
    @30
    @61
    @30
    @61
    @92
    recnd
    #
    abscld
    #
    fsumrecl
    @101
    @27
    @3
    @61
    vn
    @28
    @104
    fsumabs
    @27
    @103
    @3
    @6
    cA
    cmul
    co
    #
    vn
    csu
    @98
    cle
    @27
    @3
    @102
    @106
    vn
    @28
    @105
    @30
    @6
    cA
    @34
    @27
    @75
    @29
    @77
    adantr
    #
    remulcld
    @30
    @102
    @6
    @60
    cabs
    cfv
    #
    cmul
    co
    #
    @106
    cle
    @30
    @102
    @6
    cabs
    cfv
    #
    @108
    cmul
    co
    @109
    @30
    @6
    @60
    @69
    @30
    @60
    @91
    recnd
    #
    absmuld
    @30
    @110
    @6
    @108
    cmul
    @30
    @6
    @34
    @30
    @5
    @4
    @33
    @54
    @30
    @31
    cc0
    @5
    cle
    wbr
    @32
    @4
    vmage0
    syl
    divge0d
    #
    absidd
    oveq1d
    eqtrd
    @30
    @108
    cA
    @6
    @30
    @60
    @111
    abscld
    @107
    @34
    @112
    @30
    @7
    c1
    cpnf
    cico
    co
    #
    wcel
    #
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
    cvma
    cfv
    #
    @118
    cdiv
    co
    #
    vi
    csu
    #
    @115
    clog
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    vy
    @113
    wral
    #
    @108
    cA
    cle
    wbr
    #
    @30
    @7
    cr
    wcel
    #
    c1
    @7
    cle
    wbr
    #
    @114
    @30
    @7
    @55
    rpred
    @30
    c1
    @4
    cmul
    co
    #
    @1
    cle
    wbr
    @129
    @30
    @130
    @4
    @1
    cle
    @30
    @4
    @30
    @4
    @32
    nncnd
    mulid2d
    @27
    @29
    @31
    @4
    @1
    cle
    wbr
    #
    @27
    @42
    @29
    @31
    @131
    wa
    wb
    @43
    @4
    @1
    fznnfl
    syl
    simplbda
    eqbrtrd
    @30
    c1
    @1
    @4
    @30
    1red
    @27
    @42
    @29
    @43
    adantr
    @54
    lemuldivd
    mpbid
    c1
    cr
    wcel
    @114
    @128
    @129
    wa
    wb
    1re
    c1
    @7
    elicopnf
    ax-mp
    sylanbrc
    wph
    @126
    @26
    @29
    2vmadivsum.2
    ad2antrr
    @125
    @127
    vy
    @7
    @113
    @115
    @7
    wceq
    #
    @124
    @108
    cA
    cle
    @132
    @123
    @60
    cabs
    @132
    @121
    @13
    @122
    @20
    cmin
    @132
    @121
    @117
    @12
    vm
    csu
    @13
    @117
    @120
    @12
    vi
    vm
    @118
    @10
    wceq
    #
    @119
    @11
    @118
    @10
    cdiv
    @118
    @10
    cvma
    fveq2
    @133
    id
    oveq12d
    cbvsumv
    @132
    @117
    @9
    @12
    vm
    @132
    @116
    @8
    c1
    cfz
    @115
    @7
    cfl
    fveq2
    oveq2d
    sumeq1d
    syl5eq
    @115
    @7
    clog
    fveq2
    oveq12d
    fveq2d
    breq1d
    rspcv
    sylc
    lemul2ad
    eqbrtrd
    fsumle
    @27
    @3
    @6
    cA
    vn
    @28
    wph
    @88
    @26
    @89
    adantr
    #
    @69
    fsummulc1
    breqtrrd
    letrd
    lediv1dd
    @27
    @94
    @96
    @16
    cabs
    cfv
    #
    cdiv
    co
    @97
    @27
    @62
    @16
    @93
    @66
    @67
    absdivd
    @27
    @135
    @16
    @96
    cdiv
    @27
    @16
    @51
    @27
    @16
    @47
    rpge0d
    absidd
    oveq2d
    eqtrd
    @27
    @95
    @72
    @99
    @27
    @72
    @90
    @27
    @71
    cA
    @74
    @77
    @27
    @70
    @16
    @73
    @47
    @27
    @3
    @6
    vn
    @28
    @34
    @112
    fsumge0
    divge0d
    @27
    cA
    wph
    cA
    crp
    wcel
    @26
    2vmadivsum.1
    adantr
    rpge0d
    mulge0d
    absidd
    @27
    @70
    cA
    @16
    @86
    @134
    @66
    @67
    div23d
    eqtr4d
    3brtr4d
    adantrr
    o1le
    eqeltrrd
    o1dif
    mpbird
end
