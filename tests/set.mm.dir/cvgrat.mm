include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cabs.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmpt.mm"
include "cuz.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "syl.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancr.mm"
include "adantr.mm"
include "cn0.mm"
include "simpr.mm"
include "uznn0sub.mm"
include "reexpcld.mm"
include "eqeltrd.mm"
include "cc.mm"
include "wss.mm"
include "uzss.mm"
include "3sstr4g.mm"
include "sselda.mm"
include "syldan.mm"
include "cshi.mm"
include "oveq2.mm"
include "zcnd.mm"
include "nn0ex.mm"
include "mptex.mm"
include "shftval.mm"
include "syl2an.mm"
include "3eqtr4rd.mm"
include "seqfeq.mm"
include "seqshft.mm"
include "syl2anc.mm"
include "subidd.mm"
include "seqeq1d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "c1.mm"
include "cdiv.mm"
include "recnd.mm"
include "clt.mm"
include "max2.mm"
include "sylancl.mm"
include "absidd.mm"
include "0lt1.mm"
include "breq1.mm"
include "ifboth.mm"
include "eqbrtrd.mm"
include "geolim.mm"
include "cvv.mm"
include "wb.mm"
include "seqex.mm"
include "climshft.mm"
include "mpbird.mm"
include "breldm.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "abscld.mm"
include "cmul.mm"
include "wi.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "leidd.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "a1i.mm"
include "remulcld.mm"
include "w3a.mm"
include "lemul2a.mm"
include "ex.mm"
include "syl112anc.mm"
include "mul12d.mm"
include "expp1d.mm"
include "eleq2s.mm"
include "ax-1cn.mm"
include "addsub.mm"
include "mp3an2.mm"
include "syl2anr.mm"
include "mulcomd.mm"
include "breq2d.mm"
include "sylibd.mm"
include "peano2uzs.mm"
include "sylan2.mm"
include "cbvralv.mm"
include "sylib.mm"
include "absge0d.mm"
include "max1.mm"
include "lemul1ad.mm"
include "letrd.mm"
include "peano2uz.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "syld.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "cvgcmpce.mm"
include "iserex.mm"

theorem cvgrat
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vn: setvar n
  assume cvgrat.1: |- Z = ( ZZ>= ` M )
  assume cvgrat.2: |- W = ( ZZ>= ` N )
  assume cvgrat.3: |- ( ph -> A e. RR )
  assume cvgrat.4: |- ( ph -> A < 1 )
  assume cvgrat.5: |- ( ph -> N e. Z )
  assume cvgrat.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume cvgrat.7: |- ( ( ph /\ k e. W ) -> ( abs ` ( F ` ( k + 1 ) ) ) <_ ( A x. ( abs ` ( F ` k ) ) ) )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint W k
  disjoint Z k
  disjoint k n
  disjoint A n
  disjoint F n
  disjoint N n
  disjoint n ph
  disjoint W n
  disjoint Z n
  assert |- ( ph -> seq M ( + , F ) e. dom ~~> )

  proof
    wph
    caddc
    cF
    cM
    cseq
    cli
    cdm
    #
    wcel
    caddc
    cF
    cN
    cseq
    @0
    wcel
    wph
    cN
    cF
    cfv
    #
    cabs
    cfv
    #
    vk
    vn
    cW
    cA
    cc0
    cle
    wbr
    #
    cc0
    cA
    cif
    #
    vn
    cv
    #
    cN
    cmin
    co
    #
    cexp
    co
    #
    cmpt
    #
    cF
    cN
    cN
    cW
    cvgrat.2
    wph
    cN
    cN
    cuz
    cfv
    #
    cW
    wph
    cN
    cz
    wcel
    #
    cN
    @9
    wcel
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @10
    wph
    cN
    cZ
    @11
    cvgrat.5
    cvgrat.1
    syl6eleq
    #
    cM
    cN
    eluzelz
    syl
    #
    cN
    uzid
    syl
    cvgrat.2
    syl6eleqr
    wph
    vk
    cv
    #
    cW
    wcel
    #
    wa
    #
    @15
    @8
    cfv
    #
    @4
    @15
    cN
    cmin
    co
    #
    cexp
    co
    #
    cr
    @16
    @18
    @20
    wceq
    #
    wph
    vn
    @15
    @7
    @20
    cW
    @8
    vn
    vk
    weq
    #
    @6
    @19
    @4
    cexp
    @5
    @15
    cN
    cmin
    oveq1
    oveq2d
    #
    @8
    eqid
    @4
    @19
    cexp
    ovex
    #
    fvmpt
    #
    adantl
    @17
    @4
    @19
    wph
    @4
    cr
    wcel
    #
    @16
    wph
    cc0
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @26
    0re
    cvgrat.3
    @3
    cc0
    cA
    cr
    ifcl
    sylancr
    #
    adantr
    #
    @17
    @15
    @9
    wcel
    #
    @19
    cn0
    wcel
    #
    @17
    @15
    cW
    @9
    wph
    @16
    simpr
    cvgrat.2
    syl6eleq
    #
    cN
    @15
    uznn0sub
    #
    syl
    #
    reexpcld
    #
    eqeltrd
    wph
    @16
    @15
    cZ
    wcel
    @15
    cF
    cfv
    #
    cc
    wcel
    #
    wph
    cW
    cZ
    @15
    wph
    @9
    @11
    cW
    cZ
    wph
    @12
    @9
    @11
    wss
    @13
    cM
    cN
    uzss
    syl
    cvgrat.2
    cvgrat.1
    3sstr4g
    #
    sselda
    cvgrat.6
    syldan
    #
    wph
    caddc
    @8
    cN
    cseq
    #
    caddc
    vn
    cn0
    @4
    @5
    cexp
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    cN
    cshi
    co
    #
    @0
    wph
    @41
    caddc
    @43
    cN
    cshi
    co
    #
    cN
    cseq
    #
    caddc
    @43
    cN
    cN
    cmin
    co
    #
    cseq
    #
    cN
    cshi
    co
    #
    @45
    wph
    caddc
    vk
    @8
    @46
    cN
    @14
    wph
    @31
    wa
    #
    @19
    @43
    cfv
    #
    @20
    @15
    @46
    cfv
    #
    @18
    @51
    @32
    @52
    @20
    wceq
    @31
    @32
    wph
    @34
    adantl
    vn
    @19
    @42
    @20
    cn0
    @43
    @5
    @19
    @4
    cexp
    oveq2
    @43
    eqid
    #
    @24
    fvmpt
    syl
    wph
    cN
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @53
    @52
    wceq
    @31
    wph
    cN
    @14
    zcnd
    #
    @31
    @15
    cN
    @15
    eluzelz
    zcnd
    #
    cN
    @15
    @43
    vn
    cn0
    @42
    nn0ex
    mptex
    #
    shftval
    syl2an
    @51
    @16
    @21
    @51
    @15
    @9
    cW
    wph
    @31
    simpr
    cvgrat.2
    syl6eleqr
    #
    @25
    syl
    #
    3eqtr4rd
    seqfeq
    wph
    @10
    @10
    @47
    @50
    wceq
    @14
    @14
    caddc
    @43
    cN
    cN
    @59
    seqshft
    syl2anc
    wph
    @49
    @44
    cN
    cshi
    wph
    @48
    cc0
    caddc
    @43
    wph
    cN
    @57
    subidd
    #
    seqeq1d
    oveq1d
    3eqtrd
    wph
    @45
    c1
    c1
    @4
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wbr
    #
    @45
    @0
    wcel
    wph
    @65
    @44
    @64
    cli
    wbr
    #
    wph
    @4
    vk
    @43
    wph
    @4
    @29
    recnd
    #
    wph
    @4
    cabs
    cfv
    @4
    c1
    clt
    wph
    @4
    @29
    wph
    @28
    @27
    cc0
    @4
    cle
    wbr
    #
    cvgrat.3
    0re
    cA
    cc0
    max2
    sylancl
    #
    absidd
    wph
    cc0
    c1
    clt
    wbr
    #
    cA
    c1
    clt
    wbr
    #
    @4
    c1
    clt
    wbr
    #
    0lt1
    cvgrat.4
    @3
    @70
    @71
    @72
    cc0
    cA
    cc0
    @4
    c1
    clt
    breq1
    cA
    @4
    c1
    clt
    breq1
    ifboth
    sylancr
    eqbrtrd
    @15
    cn0
    wcel
    @15
    @43
    cfv
    @4
    @15
    cexp
    co
    #
    wceq
    wph
    vn
    @15
    @42
    @73
    cn0
    @43
    @5
    @15
    @4
    cexp
    oveq2
    @54
    @4
    @15
    cexp
    ovex
    fvmpt
    adantl
    geolim
    wph
    @10
    @44
    cvv
    wcel
    @65
    @66
    wb
    @14
    caddc
    @43
    cc0
    seqex
    @64
    @44
    cN
    cvv
    climshft
    sylancl
    mpbird
    @45
    @64
    cli
    @44
    cN
    cshi
    ovex
    c1
    @63
    cdiv
    ovex
    breldm
    syl
    eqeltrd
    wph
    @1
    wph
    cN
    cZ
    wcel
    @38
    vk
    cZ
    wral
    #
    @1
    cc
    wcel
    #
    cvgrat.5
    wph
    @38
    vk
    cZ
    cvgrat.6
    ralrimiva
    #
    @38
    @75
    vk
    cN
    cZ
    @15
    cN
    wceq
    @37
    @1
    cc
    @15
    cN
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    abscld
    #
    @51
    @37
    cabs
    cfv
    #
    @2
    @20
    cmul
    co
    #
    @2
    @18
    cmul
    co
    cle
    @31
    wph
    @78
    @79
    cle
    wbr
    #
    wph
    @5
    cF
    cfv
    #
    cabs
    cfv
    #
    @2
    @7
    cmul
    co
    #
    cle
    wbr
    #
    wi
    wph
    @2
    @2
    @4
    @48
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    wph
    @80
    wi
    #
    wph
    @15
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    @2
    @4
    @90
    cN
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @89
    vn
    vk
    cN
    @15
    @5
    cN
    wceq
    #
    @84
    @87
    wph
    @97
    @82
    @2
    @83
    @86
    cle
    @97
    @81
    @1
    cabs
    @5
    cN
    cF
    fveq2
    fveq2d
    @97
    @7
    @85
    @2
    cmul
    @97
    @6
    @48
    @4
    cexp
    @5
    cN
    cN
    cmin
    oveq1
    oveq2d
    oveq2d
    breq12d
    imbi2d
    @22
    @84
    @80
    wph
    @22
    @82
    @78
    @83
    @79
    cle
    @22
    @81
    @37
    cabs
    @5
    @15
    cF
    fveq2
    fveq2d
    @22
    @7
    @20
    @2
    cmul
    @23
    oveq2d
    breq12d
    imbi2d
    #
    @5
    @90
    wceq
    #
    @84
    @96
    wph
    @99
    @82
    @92
    @83
    @95
    cle
    @99
    @81
    @91
    cabs
    @5
    @90
    cF
    fveq2
    #
    fveq2d
    @99
    @7
    @94
    @2
    cmul
    @99
    @6
    @93
    @4
    cexp
    @5
    @90
    cN
    cmin
    oveq1
    oveq2d
    oveq2d
    breq12d
    imbi2d
    @98
    @88
    @10
    wph
    @2
    @2
    @86
    cle
    wph
    @2
    @77
    leidd
    wph
    @86
    @2
    c1
    cmul
    co
    @2
    wph
    @85
    c1
    @2
    cmul
    wph
    @85
    @4
    cc0
    cexp
    co
    c1
    wph
    @48
    cc0
    @4
    cexp
    @62
    oveq2d
    wph
    @4
    @67
    exp0d
    eqtrd
    oveq2d
    wph
    @2
    wph
    @2
    @77
    recnd
    #
    mulid1d
    eqtrd
    breqtrrd
    a1i
    @31
    wph
    @80
    @96
    wph
    @31
    @80
    @96
    wi
    #
    wph
    @31
    @16
    @102
    @60
    @17
    @80
    @4
    @78
    cmul
    co
    #
    @95
    cle
    wbr
    #
    @96
    @17
    @80
    @103
    @4
    @79
    cmul
    co
    #
    cle
    wbr
    #
    @104
    @17
    @78
    cr
    wcel
    #
    @79
    cr
    wcel
    #
    @26
    @68
    @80
    @106
    wi
    @17
    @37
    @40
    abscld
    #
    @17
    @2
    @20
    wph
    @2
    cr
    wcel
    @16
    @77
    adantr
    #
    @36
    remulcld
    @30
    wph
    @68
    @16
    @69
    adantr
    @107
    @108
    @26
    @68
    wa
    w3a
    @80
    @106
    @78
    @79
    @4
    lemul2a
    ex
    syl112anc
    @17
    @105
    @95
    @103
    cle
    @17
    @105
    @2
    @4
    @20
    cmul
    co
    #
    cmul
    co
    @95
    @17
    @4
    @2
    @20
    wph
    @4
    cc
    wcel
    @16
    @67
    adantr
    #
    wph
    @2
    cc
    wcel
    @16
    @101
    adantr
    @17
    @20
    @36
    recnd
    #
    mul12d
    @17
    @111
    @94
    @2
    cmul
    @17
    @4
    @19
    c1
    caddc
    co
    #
    cexp
    co
    @20
    @4
    cmul
    co
    @94
    @111
    @17
    @4
    @19
    @112
    @35
    expp1d
    @17
    @93
    @114
    @4
    cexp
    @16
    @56
    @55
    @93
    @114
    wceq
    #
    wph
    @56
    @15
    @9
    cW
    @58
    cvgrat.2
    eleq2s
    @57
    @56
    c1
    cc
    wcel
    @55
    @115
    ax-1cn
    @15
    c1
    cN
    addsub
    mp3an2
    syl2anr
    oveq2d
    @17
    @4
    @20
    @112
    @113
    mulcomd
    3eqtr4rd
    oveq2d
    eqtrd
    breq2d
    sylibd
    @17
    @92
    @103
    cle
    wbr
    #
    @104
    @96
    @17
    @92
    cA
    @78
    cmul
    co
    @103
    @17
    @91
    @17
    @90
    cZ
    wcel
    #
    @81
    cc
    wcel
    #
    vn
    cZ
    wral
    #
    @91
    cc
    wcel
    #
    @16
    wph
    @90
    cW
    wcel
    @117
    cN
    @15
    cW
    cvgrat.2
    peano2uzs
    wph
    cW
    cZ
    @90
    @39
    sselda
    sylan2
    wph
    @119
    @16
    wph
    @74
    @119
    @76
    @38
    @118
    vk
    vn
    cZ
    vk
    vn
    weq
    @37
    @81
    cc
    @15
    @5
    cF
    fveq2
    eleq1d
    cbvralv
    sylib
    adantr
    @118
    @120
    vn
    @90
    cZ
    @99
    @81
    @91
    cc
    @100
    eleq1d
    rspcv
    sylc
    abscld
    #
    @17
    cA
    @78
    wph
    @28
    @16
    cvgrat.3
    adantr
    #
    @109
    remulcld
    @17
    @4
    @78
    @30
    @109
    remulcld
    #
    cvgrat.7
    @17
    cA
    @4
    @78
    @122
    @30
    @109
    @17
    @37
    @40
    absge0d
    wph
    cA
    @4
    cle
    wbr
    #
    @16
    wph
    @28
    @27
    @124
    cvgrat.3
    0re
    cA
    cc0
    max1
    sylancl
    adantr
    lemul1ad
    letrd
    @17
    @92
    cr
    wcel
    @103
    cr
    wcel
    @95
    cr
    wcel
    @116
    @104
    wa
    @96
    wi
    @121
    @123
    @17
    @2
    @94
    @110
    @17
    @4
    @93
    @30
    @17
    @90
    @9
    wcel
    #
    @93
    cn0
    wcel
    @17
    @31
    @125
    @33
    cN
    @15
    peano2uz
    syl
    cN
    @90
    uznn0sub
    syl
    reexpcld
    remulcld
    @92
    @103
    @95
    letr
    syl3anc
    mpand
    syld
    syldan
    expcom
    a2d
    uzind4
    impcom
    @51
    @18
    @20
    @2
    cmul
    @61
    oveq2d
    breqtrrd
    cvgcmpce
    wph
    vk
    cF
    cM
    cN
    cZ
    cvgrat.1
    cvgrat.5
    cvgrat.6
    iserex
    mpbird
end
