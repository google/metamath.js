include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "cabs.mm"
include "clog.mm"
include "caddc.mm"
include "cmul.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "fsumcl.mm"
include "abscld.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpld.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "0lt1.mm"
include "a1i.mm"
include "simprd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "relogcld.mm"
include "readdcld.mm"
include "remulcld.mm"
include "fsumabs.mm"
include "absdivd.mm"
include "wceq.mm"
include "nnrpd.mm"
include "rprege0d.mm"
include "absid.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "breqtrd.mm"
include "cin.mm"
include "c0.mm"
include "cn0.mm"
include "rpdivcld.mm"
include "flge0nn0.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "cuz.mm"
include "cun.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "rpred.mm"
include "wb.mm"
include "jca.mm"
include "rpregt0d.mm"
include "lediv2.mm"
include "syl211anc.mm"
include "mpbid.mm"
include "recnd.mm"
include "div1d.mm"
include "flword2.mm"
include "syl3anc.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "fsumsplit.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "ssun2.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "adantr.mm"
include "lemuldiv2.mm"
include "lemuldivd.mm"
include "bitr3d.mm"
include "wi.mm"
include "ex.mm"
include "mpd.mm"
include "cc.mm"
include "ledivmul2d.mm"
include "mpbird.mm"
include "fsumle.mm"
include "fsumless.mm"
include "letrd.mm"
include "nnrecred.mm"
include "divrecd.mm"
include "eqeltrrd.mm"
include "crp.mm"
include "wn.mm"
include "noel.mm"
include "elin.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "mtbiri.mm"
include "imnan.mm"
include "sylibr.mm"
include "con2d.mm"
include "imp.mm"
include "baibd.mm"
include "syl2an.mm"
include "bitrd.mm"
include "mtbid.mm"
include "ltnled.mm"
include "lediv1dd.mm"
include "fsummulc2.mm"
include "breqtrrd.mm"
include "cmin.mm"
include "oveq1d.mm"
include "pncan2d.mm"
include "resubcld.mm"
include "adantlr.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "simpr.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "cz.mm"
include "0z.mm"
include "flbi.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "fz10.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "suble0d.mm"
include "logge0d.mm"
include "0le1.mm"
include "addge0d.mm"
include "harmonicubnd.mm"
include "sylan.mm"
include "harmoniclbnd.mm"
include "peano2re.mm"
include "le2sub.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "pnncand.mm"
include "relogdivd.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "3eqtr4d.mm"
include "ltlecasei.mm"
include "eqbrtrrd.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "le2addd.mm"
include "eqbrtrd.mm"

theorem fsumharmonic
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cT: class T
  let vn: setvar n
  assume fsumharmonic.a: |- ( ph -> A e. RR+ )
  assume fsumharmonic.t: |- ( ph -> ( T e. RR /\ 1 <_ T ) )
  assume fsumharmonic.r: |- ( ph -> ( R e. RR /\ 0 <_ R ) )
  assume fsumharmonic.b: |- ( ( ph /\ n e. ( 1 ... ( |_ ` A ) ) ) -> B e. CC )
  assume fsumharmonic.c: |- ( ( ph /\ n e. ( 1 ... ( |_ ` A ) ) ) -> C e. RR )
  assume fsumharmonic.0: |- ( ( ph /\ n e. ( 1 ... ( |_ ` A ) ) ) -> 0 <_ C )
  assume fsumharmonic.1: |- ( ( ( ph /\ n e. ( 1 ... ( |_ ` A ) ) ) /\ T <_ ( A / n ) ) -> ( abs ` B ) <_ ( C x. n ) )
  assume fsumharmonic.2: |- ( ( ( ph /\ n e. ( 1 ... ( |_ ` A ) ) ) /\ ( A / n ) < T ) -> ( abs ` B ) <_ R )

  disjoint A n
  disjoint n ph
  disjoint R n
  disjoint T n
  assert |- ( ph -> ( abs ` sum_ n e. ( 1 ... ( |_ ` A ) ) ( B / n ) ) <_ ( sum_ n e. ( 1 ... ( |_ ` A ) ) C + ( R x. ( ( log ` T ) + 1 ) ) ) )

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
    cB
    vn
    cv
    #
    cdiv
    co
    #
    vn
    csu
    #
    cabs
    cfv
    #
    @1
    cB
    cabs
    cfv
    #
    @2
    cdiv
    co
    #
    vn
    csu
    #
    @1
    cC
    vn
    csu
    #
    cR
    cT
    clog
    cfv
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    wph
    @4
    wph
    @1
    @3
    vn
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
    cB
    @2
    fsumharmonic.b
    @16
    @2
    @15
    @2
    cn
    wcel
    #
    wph
    @2
    @0
    elfznn
    #
    adantl
    #
    nncnd
    #
    @16
    @2
    @19
    nnne0d
    #
    divcld
    #
    fsumcl
    abscld
    wph
    @1
    @7
    vn
    @14
    @16
    @6
    @2
    @16
    cB
    fsumharmonic.b
    abscld
    #
    @19
    nndivred
    #
    fsumrecl
    wph
    @9
    @12
    wph
    @1
    cC
    vn
    @14
    fsumharmonic.c
    fsumrecl
    #
    wph
    cR
    @11
    wph
    cR
    cr
    wcel
    #
    cc0
    cR
    cle
    wbr
    #
    fsumharmonic.r
    simpld
    #
    wph
    @10
    c1
    wph
    cT
    wph
    cT
    wph
    cT
    cr
    wcel
    #
    c1
    cT
    cle
    wbr
    #
    fsumharmonic.t
    simpld
    #
    wph
    cc0
    c1
    cT
    wph
    0red
    wph
    1red
    #
    @31
    cc0
    c1
    clt
    wbr
    #
    wph
    0lt1
    a1i
    #
    wph
    @29
    @30
    fsumharmonic.t
    simprd
    #
    ltletrd
    #
    elrpd
    #
    relogcld
    #
    @32
    readdcld
    #
    remulcld
    #
    readdcld
    wph
    @5
    @1
    @3
    cabs
    cfv
    #
    vn
    csu
    @8
    cle
    wph
    @1
    @3
    vn
    @14
    @22
    fsumabs
    wph
    @1
    @41
    @7
    vn
    @16
    @41
    @6
    @2
    cabs
    cfv
    #
    cdiv
    co
    @7
    @16
    cB
    @2
    fsumharmonic.b
    @20
    @21
    absdivd
    @16
    @42
    @2
    @6
    cdiv
    @16
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    wa
    @42
    @2
    wceq
    @16
    @2
    @16
    @2
    @19
    nnrpd
    #
    rprege0d
    @2
    absid
    syl
    oveq2d
    eqtrd
    sumeq2dv
    breqtrd
    wph
    @8
    c1
    cA
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    vn
    csu
    #
    @46
    c1
    caddc
    co
    #
    @0
    cfz
    co
    #
    @7
    vn
    csu
    #
    caddc
    co
    @13
    cle
    wph
    @47
    @50
    @7
    @1
    vn
    wph
    @46
    @49
    clt
    wbr
    @47
    @50
    cin
    #
    c0
    wceq
    wph
    @46
    wph
    @46
    wph
    @45
    cr
    wcel
    #
    cc0
    @45
    cle
    wbr
    wa
    @46
    cn0
    wcel
    #
    wph
    @45
    wph
    cA
    cT
    fsumharmonic.a
    @37
    rpdivcld
    #
    rprege0d
    @45
    flge0nn0
    syl
    #
    nn0red
    ltp1d
    c1
    @46
    @49
    @0
    fzdisj
    syl
    #
    wph
    @49
    c1
    cuz
    cfv
    #
    wcel
    @0
    @46
    cuz
    cfv
    wcel
    #
    @1
    @47
    @50
    cun
    #
    wceq
    wph
    @49
    cn
    @58
    wph
    @54
    @49
    cn
    wcel
    @56
    @46
    nn0p1nn
    syl
    nnuz
    syl6eleq
    wph
    @53
    cA
    cr
    wcel
    #
    @45
    cA
    cle
    wbr
    @59
    wph
    @45
    @55
    rpred
    #
    wph
    cA
    fsumharmonic.a
    rpred
    #
    wph
    @45
    cA
    c1
    cdiv
    co
    #
    cA
    cle
    wph
    @30
    @45
    @64
    cle
    wbr
    #
    @35
    wph
    c1
    cr
    wcel
    @33
    @29
    cc0
    cT
    clt
    wbr
    #
    wa
    #
    @61
    cc0
    cA
    clt
    wbr
    wa
    @30
    @65
    wb
    @32
    @34
    wph
    @29
    @66
    @31
    @36
    jca
    #
    wph
    cA
    fsumharmonic.a
    rpregt0d
    c1
    cT
    cA
    lediv2
    syl211anc
    mpbid
    wph
    cA
    wph
    cA
    @63
    recnd
    div1d
    breqtrd
    @45
    cA
    flword2
    syl3anc
    @46
    c1
    @0
    fzsplit2
    syl2anc
    #
    @14
    @16
    @7
    @24
    recnd
    fsumsplit
    wph
    @48
    @51
    @9
    @12
    wph
    @47
    @7
    vn
    wph
    c1
    @46
    fzfid
    #
    wph
    @2
    @47
    wcel
    #
    @15
    @7
    cr
    wcel
    #
    wph
    @47
    @1
    @2
    wph
    @60
    @47
    @1
    @47
    @50
    ssun1
    @69
    syl5sseqr
    #
    sselda
    #
    @24
    syldan
    #
    fsumrecl
    #
    wph
    @50
    @7
    vn
    wph
    @49
    @0
    fzfid
    #
    wph
    @2
    @50
    wcel
    #
    @15
    @72
    wph
    @50
    @1
    @2
    wph
    @60
    @50
    @1
    @50
    @47
    ssun2
    @69
    syl5sseqr
    sselda
    #
    @24
    syldan
    #
    fsumrecl
    #
    @25
    @40
    wph
    @48
    @47
    cC
    vn
    csu
    @9
    @76
    wph
    @47
    cC
    vn
    @70
    wph
    @71
    @15
    cC
    cr
    wcel
    @74
    fsumharmonic.c
    syldan
    #
    fsumrecl
    @25
    wph
    @47
    @7
    cC
    vn
    @70
    @75
    @82
    wph
    @71
    wa
    #
    @7
    cC
    cle
    wbr
    @6
    cC
    @2
    cmul
    co
    cle
    wbr
    #
    @83
    cT
    cA
    @2
    cdiv
    co
    #
    cle
    wbr
    #
    @84
    @83
    @2
    @45
    cle
    wbr
    #
    @86
    wph
    @71
    @17
    @87
    wph
    @53
    @71
    @17
    @87
    wa
    wb
    @62
    @2
    @45
    fznnfl
    #
    syl
    simplbda
    wph
    @71
    @15
    @87
    @86
    wb
    @74
    @16
    cT
    @2
    cmul
    co
    cA
    cle
    wbr
    #
    @87
    @86
    @16
    @43
    @61
    @67
    @89
    @87
    wb
    @16
    @2
    @44
    rpred
    wph
    @61
    @15
    @63
    adantr
    #
    wph
    @67
    @15
    @68
    adantr
    @2
    cA
    cT
    lemuldiv2
    syl3anc
    @16
    cT
    cA
    @2
    wph
    @29
    @15
    @31
    adantr
    @90
    @44
    lemuldivd
    bitr3d
    #
    syldan
    mpbid
    wph
    @71
    @15
    @86
    @84
    wi
    @74
    @16
    @86
    @84
    fsumharmonic.1
    ex
    syldan
    mpd
    @83
    @6
    cC
    @2
    @83
    cB
    wph
    @71
    @15
    cB
    cc
    wcel
    @74
    fsumharmonic.b
    syldan
    abscld
    @82
    @83
    @2
    @83
    @15
    @17
    @74
    @18
    syl
    #
    nnrpd
    #
    ledivmul2d
    mpbird
    fsumle
    wph
    @1
    cC
    @47
    vn
    @14
    fsumharmonic.c
    fsumharmonic.0
    @73
    fsumless
    letrd
    wph
    @51
    cR
    @50
    c1
    @2
    cdiv
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    @12
    @81
    wph
    cR
    @95
    @28
    wph
    @50
    @94
    vn
    @77
    wph
    @78
    wa
    #
    @2
    @97
    @15
    @17
    @79
    @18
    syl
    #
    nnrecred
    #
    fsumrecl
    #
    remulcld
    @40
    wph
    @51
    @50
    cR
    @94
    cmul
    co
    #
    vn
    csu
    @96
    cle
    wph
    @50
    @7
    @101
    vn
    @77
    @80
    @97
    cR
    @2
    cdiv
    co
    #
    @101
    cr
    @97
    cR
    @2
    @97
    cR
    wph
    @26
    @78
    @28
    adantr
    #
    recnd
    @97
    @2
    @98
    nncnd
    @97
    @2
    @98
    nnne0d
    divrecd
    #
    @97
    cR
    @2
    @103
    @98
    nndivred
    eqeltrrd
    @97
    @7
    @102
    @101
    cle
    @97
    @6
    cR
    @2
    wph
    @78
    @15
    @6
    cr
    wcel
    @79
    @23
    syldan
    @103
    wph
    @78
    @15
    @2
    crp
    wcel
    #
    @79
    @44
    syldan
    @97
    @85
    cT
    clt
    wbr
    #
    @6
    cR
    cle
    wbr
    #
    @97
    @106
    @86
    wn
    @97
    @71
    @86
    wph
    @78
    @71
    wn
    wph
    @71
    @78
    wph
    @71
    @78
    wa
    #
    wn
    @71
    @78
    wn
    wi
    wph
    @108
    @2
    c0
    wcel
    #
    @2
    noel
    @108
    @2
    @52
    wcel
    wph
    @109
    @2
    @47
    @50
    elin
    wph
    @52
    c0
    @2
    @57
    eleq2d
    syl5bbr
    mtbiri
    @71
    @78
    imnan
    sylibr
    con2d
    imp
    wph
    @78
    @15
    @71
    @86
    wb
    @79
    @16
    @71
    @87
    @86
    wph
    @53
    @17
    @71
    @87
    wb
    @15
    @62
    @18
    @53
    @71
    @17
    @87
    @88
    baibd
    syl2an
    @91
    bitrd
    syldan
    mtbid
    @97
    @85
    cT
    @97
    cA
    @2
    wph
    @61
    @78
    @63
    adantr
    @98
    nndivred
    wph
    @29
    @78
    @31
    adantr
    ltnled
    mpbird
    wph
    @78
    @15
    @106
    @107
    wi
    @79
    @16
    @106
    @107
    fsumharmonic.2
    ex
    syldan
    mpd
    lediv1dd
    @104
    breqtrd
    fsumle
    wph
    @50
    @94
    cR
    vn
    @77
    wph
    cR
    @28
    recnd
    @97
    @94
    @99
    recnd
    fsummulc2
    breqtrrd
    wph
    @95
    cr
    wcel
    @11
    cr
    wcel
    #
    @26
    @27
    wa
    @95
    @11
    cle
    wbr
    @96
    @12
    cle
    wbr
    @100
    @39
    fsumharmonic.r
    wph
    @1
    @94
    vn
    csu
    #
    @47
    @94
    vn
    csu
    #
    cmin
    co
    #
    @95
    @11
    cle
    wph
    @113
    @112
    @95
    caddc
    co
    #
    @112
    cmin
    co
    @95
    wph
    @111
    @114
    @112
    cmin
    wph
    @47
    @50
    @94
    @1
    vn
    @57
    @69
    @14
    @16
    @94
    @16
    @2
    @19
    nnrecred
    #
    recnd
    fsumsplit
    oveq1d
    wph
    @112
    @95
    wph
    @112
    wph
    @47
    @94
    vn
    @70
    @83
    @2
    @92
    nnrecred
    fsumrecl
    #
    recnd
    wph
    @95
    @100
    recnd
    pncan2d
    eqtrd
    wph
    @113
    @11
    cle
    wbr
    cA
    c1
    wph
    cA
    c1
    clt
    wbr
    #
    wa
    #
    @113
    cc0
    @11
    @118
    @111
    @112
    wph
    @111
    cr
    wcel
    #
    @117
    wph
    @1
    @94
    vn
    @14
    @115
    fsumrecl
    #
    adantr
    #
    wph
    @112
    cr
    wcel
    #
    @117
    @116
    adantr
    #
    resubcld
    @118
    0red
    wph
    @110
    @117
    @39
    adantr
    @118
    @113
    cc0
    cle
    wbr
    @111
    @112
    cle
    wbr
    @118
    @47
    @94
    @1
    vn
    @118
    c1
    @46
    fzfid
    @118
    @71
    wa
    #
    @94
    @124
    @2
    wph
    @71
    @105
    @117
    @93
    adantlr
    rpreccld
    #
    rpred
    @124
    @94
    @125
    rpge0d
    @118
    @1
    c0
    @47
    @118
    @1
    c1
    cc0
    cfz
    co
    c0
    @118
    @0
    cc0
    c1
    cfz
    @118
    @0
    cc0
    wceq
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @118
    cA
    wph
    cA
    crp
    wcel
    @117
    fsumharmonic.a
    adantr
    rpge0d
    @118
    cA
    c1
    @128
    clt
    wph
    @117
    simpr
    0p1e1
    syl6breqr
    @118
    @61
    cc0
    cz
    wcel
    @126
    @127
    @129
    wa
    wb
    wph
    @61
    @117
    @63
    adantr
    0z
    cA
    cc0
    flbi
    sylancl
    mpbir2and
    oveq2d
    fz10
    syl6eq
    @47
    0ss
    syl6eqss
    fsumless
    @118
    @111
    @112
    @121
    @123
    suble0d
    mpbird
    wph
    cc0
    @11
    cle
    wbr
    @117
    wph
    @10
    c1
    @38
    @32
    wph
    cT
    @31
    @35
    logge0d
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    addge0d
    adantr
    letrd
    wph
    c1
    cA
    cle
    wbr
    #
    wa
    #
    @113
    cA
    clog
    cfv
    #
    c1
    caddc
    co
    #
    @45
    clog
    cfv
    #
    cmin
    co
    #
    @11
    cle
    @131
    @111
    @133
    cle
    wbr
    #
    @134
    @112
    cle
    wbr
    #
    @113
    @135
    cle
    wbr
    #
    wph
    @61
    @130
    @136
    @63
    cA
    vn
    harmonicubnd
    sylan
    wph
    @137
    @130
    wph
    @45
    crp
    wcel
    @137
    @55
    @45
    vn
    harmoniclbnd
    syl
    adantr
    wph
    @136
    @137
    wa
    @138
    wi
    #
    @130
    wph
    @119
    @122
    @133
    cr
    wcel
    #
    @134
    cr
    wcel
    @139
    @120
    @116
    wph
    @132
    cr
    wcel
    @140
    wph
    cA
    fsumharmonic.a
    relogcld
    #
    @132
    peano2re
    syl
    wph
    @45
    @55
    relogcld
    @111
    @112
    @133
    @134
    le2sub
    syl22anc
    adantr
    mp2and
    wph
    @135
    @11
    wceq
    @130
    wph
    @133
    @132
    @10
    cmin
    co
    #
    cmin
    co
    c1
    @10
    caddc
    co
    #
    @135
    @11
    wph
    @132
    c1
    @10
    wph
    @132
    @141
    recnd
    wph
    c1
    @32
    recnd
    wph
    @10
    @38
    recnd
    #
    pnncand
    wph
    @134
    @142
    @133
    cmin
    wph
    cA
    cT
    fsumharmonic.a
    @37
    relogdivd
    oveq2d
    wph
    @10
    cc
    wcel
    c1
    cc
    wcel
    @11
    @143
    wceq
    @144
    ax-1cn
    @10
    c1
    addcom
    sylancl
    3eqtr4d
    adantr
    breqtrd
    @63
    @32
    ltlecasei
    eqbrtrrd
    @95
    @11
    cR
    lemul2a
    syl31anc
    letrd
    le2addd
    eqbrtrd
    letrd
end
