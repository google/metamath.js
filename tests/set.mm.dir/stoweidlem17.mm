include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "nnnn0d.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "syl.mm"
include "ancli.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "weq.mm"
include "csn.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "sumeq1i.mm"
include "mpteq2i.mm"
include "cc.mm"
include "cr.mm"
include "adantr.mm"
include "recnd.mm"
include "wf.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "nnz.mm"
include "clt.mm"
include "nngt0.mm"
include "0re.mm"
include "nnre.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "jca.mm"
include "eluz1i.mm"
include "sylibr.mm"
include "eluzfz1.mm"
include "ffvelrnd.mm"
include "feq1.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "ffvelrnda.mm"
include "mulcld.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "sumsn.mm"
include "mpteq2da.mm"
include "syl5eq.mm"
include "stoweidlem2.mm"
include "eqeltrd.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "eqcomi.mm"
include "a1i.mm"
include "simpr.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "simpl.mm"
include "id.mm"
include "fveq1.mm"
include "eleq1i.mm"
include "fveq1i.mm"
include "syl6eq.mm"
include "3com12.mm"
include "3expib.mm"
include "sylbir.mm"
include "3impib.mm"
include "3com13.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "ad2antll.mm"
include "simprrl.mm"
include "simprl.mm"
include "ad2antrl.mm"
include "nn0re.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "nnred.mm"
include "lep1.mm"
include "3syl.mm"
include "elfzle2.mm"
include "letrd.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "jca32.mm"
include "adantl.mm"
include "pm3.31.mm"
include "sumeq2sdv.mm"
include "w3a.mm"
include "wb.mm"
include "3anass.mm"
include "biimpri.mm"
include "nfv.mm"
include "nf3an.mm"
include "fzfid.mm"
include "3ad2ant2.mm"
include "fzelp1.mm"
include "anim2i.mm"
include "an32.mm"
include "sylib.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "sselda.mm"
include "3ad2antl3.mm"
include "simpl2.mm"
include "sylc.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "3simpc.mm"
include "cmin.mm"
include "elfzuz.mm"
include "3ad2ant3.mm"
include "an32s.mm"
include "remulcl.mm"
include "fsumm1.mm"
include "nn0cn.mm"
include "3ad2ant1.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "mpbird.mm"
include "exp32.mm"
include "pm2.86i.mm"
include "nn0ind.mm"

theorem stoweidlem17
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cE: class E
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vr: setvar r
  let vn: setvar n
  let vk: setvar k
  assume stoweidlem17.1: |- F/ t ph
  assume stoweidlem17.2: |- ( ph -> N e. NN )
  assume stoweidlem17.3: |- ( ph -> X : ( 0 ... N ) --> A )
  assume stoweidlem17.4: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem17.5: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem17.6: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem17.7: |- ( ph -> E e. RR )
  assume stoweidlem17.8: |- ( ( ph /\ f e. A ) -> f : T --> RR )

  disjoint f g
  disjoint f i
  disjoint f t
  disjoint E f
  disjoint g i
  disjoint g t
  disjoint E g
  disjoint i t
  disjoint E i
  disjoint E t
  disjoint A f
  disjoint A g
  disjoint T f
  disjoint T g
  disjoint T i
  disjoint T t
  disjoint X f
  disjoint X g
  disjoint X i
  disjoint X t
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint N i
  disjoint N t
  disjoint t x
  disjoint E x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint f m
  disjoint f r
  disjoint g m
  disjoint g r
  disjoint i m
  disjoint i r
  disjoint m r
  disjoint m t
  disjoint E m
  disjoint r t
  disjoint E r
  disjoint A m
  disjoint T m
  disjoint T r
  disjoint X m
  disjoint X r
  disjoint m ph
  disjoint ph r
  disjoint i n
  disjoint m n
  disjoint n t
  disjoint E n
  disjoint N m
  disjoint N n
  disjoint A n
  disjoint T n
  disjoint X n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( t e. T |-> sum_ i e. ( 0 ... N ) ( E x. ( ( X ` i ) ` t ) ) ) e. A )

  proof
    wph
    cN
    cn0
    wcel
    #
    wph
    cN
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    vt
    cT
    @1
    cE
    vt
    cv
    #
    vi
    cv
    #
    cX
    cfv
    #
    cfv
    #
    cmul
    co
    #
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    wph
    cN
    stoweidlem17.2
    nnnn0d
    #
    wph
    @2
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    #
    @2
    wph
    cN
    cn0
    @13
    @12
    nn0uz
    syl6eleq
    cc0
    cN
    eluzfz2
    syl
    ancli
    wph
    vn
    cv
    #
    @1
    wcel
    #
    wa
    #
    vt
    cT
    cc0
    @15
    cfz
    co
    #
    @8
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    cc0
    @1
    wcel
    #
    wa
    #
    vt
    cT
    cc0
    cc0
    cfz
    co
    #
    @8
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    vm
    cv
    #
    @1
    wcel
    #
    wa
    #
    vt
    cT
    cc0
    @28
    cfz
    co
    #
    @8
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    #
    wph
    @28
    c1
    caddc
    co
    #
    @1
    wcel
    #
    wa
    #
    vt
    cT
    cc0
    @36
    cfz
    co
    #
    @8
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    #
    @3
    @11
    wi
    vn
    vm
    cN
    @15
    cc0
    wceq
    #
    @17
    @23
    @21
    @27
    @44
    @16
    @22
    wph
    @15
    cc0
    @1
    eleq1
    anbi2d
    @44
    @20
    @26
    cA
    @44
    vt
    cT
    @19
    @25
    @44
    @18
    @24
    @8
    vi
    @15
    cc0
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    vn
    vm
    weq
    #
    @17
    @30
    @21
    @34
    @45
    @16
    @29
    wph
    @15
    @28
    @1
    eleq1
    anbi2d
    @45
    @20
    @33
    cA
    @45
    vt
    cT
    @19
    @32
    @45
    @18
    @31
    @8
    vi
    @15
    @28
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    @15
    @36
    wceq
    #
    @17
    @38
    @21
    @42
    @46
    @16
    @37
    wph
    @15
    @36
    @1
    eleq1
    anbi2d
    @46
    @20
    @41
    cA
    @46
    vt
    cT
    @19
    @40
    @46
    @18
    @39
    @8
    vi
    @15
    @36
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    @15
    cN
    wceq
    #
    @17
    @3
    @21
    @11
    @47
    @16
    @2
    wph
    @15
    cN
    @1
    eleq1
    anbi2d
    @47
    @20
    @10
    cA
    @47
    vt
    cT
    @19
    @9
    @47
    @18
    @1
    @8
    vi
    @15
    cN
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    wph
    @27
    @22
    wph
    @26
    vt
    cT
    cE
    @4
    cc0
    cX
    cfv
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
    @26
    vt
    cT
    cc0
    csn
    #
    @8
    vi
    csu
    #
    cmpt
    @51
    vt
    cT
    @25
    @53
    @24
    @52
    @8
    vi
    cc0
    cz
    wcel
    #
    @24
    @52
    wceq
    0z
    cc0
    fzsn
    ax-mp
    sumeq1i
    mpteq2i
    wph
    vt
    cT
    @53
    @50
    stoweidlem17.1
    wph
    @4
    cT
    wcel
    #
    wa
    #
    @54
    @50
    cc
    wcel
    @53
    @50
    wceq
    0z
    @56
    cE
    @49
    @56
    cE
    wph
    cE
    cr
    wcel
    #
    @55
    stoweidlem17.7
    adantr
    #
    recnd
    @56
    @49
    wph
    cT
    cr
    @4
    @48
    @48
    cA
    wcel
    wph
    cT
    cr
    @48
    wf
    #
    wph
    @1
    cA
    cc0
    cX
    stoweidlem17.3
    wph
    @14
    @22
    wph
    cN
    cz
    wcel
    #
    cc0
    cN
    cle
    wbr
    #
    wa
    #
    @14
    wph
    cN
    cn
    wcel
    #
    @62
    stoweidlem17.2
    @63
    @60
    @61
    cN
    nnz
    @63
    cc0
    cN
    clt
    wbr
    #
    @61
    cN
    nngt0
    @63
    cc0
    cr
    wcel
    cN
    cr
    wcel
    #
    @64
    @61
    wi
    0re
    cN
    nnre
    cc0
    cN
    ltle
    sylancr
    mpd
    jca
    syl
    cc0
    cN
    0z
    eluz1i
    sylibr
    cc0
    cN
    eluzfz1
    syl
    ffvelrnd
    #
    wph
    cT
    cr
    vf
    cv
    #
    wf
    #
    wi
    #
    wph
    @59
    wi
    vf
    @48
    cA
    @67
    @48
    wceq
    @68
    @59
    wph
    cT
    cr
    @67
    @48
    feq1
    imbi2d
    wph
    @67
    cA
    wcel
    #
    @68
    stoweidlem17.8
    expcom
    #
    vtoclga
    mpcom
    ffvelrnda
    recnd
    mulcld
    @8
    @50
    vi
    cc0
    cz
    @5
    cc0
    wceq
    #
    @7
    @49
    cE
    cmul
    @72
    @4
    @6
    @48
    @5
    cc0
    cX
    fveq2
    fveq1d
    oveq2d
    sumsn
    sylancr
    mpteq2da
    syl5eq
    wph
    vx
    vt
    cA
    cT
    vf
    vg
    cE
    @48
    stoweidlem17.1
    stoweidlem17.5
    stoweidlem17.6
    stoweidlem17.8
    stoweidlem17.7
    @66
    stoweidlem2
    eqeltrd
    adantr
    @28
    cn0
    wcel
    #
    @35
    @43
    @73
    @35
    wi
    #
    @73
    @38
    @42
    @74
    @73
    @38
    wa
    #
    wa
    #
    @42
    vt
    cT
    @4
    @33
    cfv
    #
    @4
    vt
    cT
    cE
    @4
    @36
    cX
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    @76
    @81
    cA
    wcel
    #
    wph
    @34
    @85
    @38
    @86
    @74
    @73
    @38
    vt
    cT
    @4
    vt
    cT
    cE
    cmpt
    #
    cfv
    #
    @79
    cmul
    co
    #
    cmpt
    #
    @81
    cA
    wph
    @90
    @81
    wceq
    @37
    wph
    vt
    cT
    @89
    @80
    stoweidlem17.1
    @56
    @88
    cE
    @79
    cmul
    @56
    vr
    @4
    cE
    cE
    cT
    @87
    cr
    @87
    vr
    cT
    cE
    cmpt
    #
    wceq
    @56
    @91
    @87
    vr
    vt
    cT
    cE
    cE
    vr
    vt
    weq
    #
    cE
    eqidd
    cbvmptv
    #
    eqcomi
    a1i
    @56
    @92
    wa
    cE
    eqidd
    wph
    @55
    simpr
    @58
    fvmptd
    oveq1d
    mpteq2da
    adantr
    @38
    @78
    cA
    wcel
    #
    wph
    @87
    cA
    wcel
    #
    @90
    cA
    wcel
    #
    wph
    @1
    cA
    @36
    cX
    stoweidlem17.3
    ffvelrnda
    #
    wph
    @37
    simpl
    #
    wph
    @95
    @37
    @57
    wph
    @95
    stoweidlem17.7
    wph
    vt
    cT
    vx
    cv
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @95
    wi
    vx
    cE
    cr
    @99
    cE
    wceq
    #
    @101
    @95
    wph
    @102
    @100
    @87
    cA
    @102
    vt
    cT
    @99
    cE
    @102
    id
    mpteq2dv
    eleq1d
    imbi2d
    wph
    @99
    cr
    wcel
    @101
    stoweidlem17.6
    expcom
    vtoclga
    mpcom
    adantr
    @94
    wph
    @95
    @96
    wph
    @95
    wa
    #
    vt
    cT
    @88
    @4
    vg
    cv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @103
    @96
    wi
    vg
    @78
    cA
    @104
    @78
    wceq
    #
    @108
    @96
    @103
    @109
    @107
    @90
    cA
    @109
    vt
    cT
    @106
    @89
    @109
    @105
    @79
    @88
    cmul
    @4
    @104
    @78
    fveq1
    oveq2d
    mpteq2dv
    eleq1d
    imbi2d
    @104
    cA
    wcel
    #
    wph
    @95
    @108
    @95
    wph
    @110
    @108
    @95
    wph
    @110
    @108
    @95
    @91
    cA
    wcel
    wph
    @110
    wa
    #
    @108
    wi
    #
    @91
    @87
    cA
    @93
    eleq1i
    @111
    vt
    cT
    @4
    @67
    cfv
    #
    @105
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @112
    vf
    @91
    cA
    @67
    @91
    wceq
    #
    @116
    @108
    @111
    @117
    @115
    @107
    cA
    @117
    vt
    cT
    @114
    @106
    @117
    @113
    @88
    @105
    cmul
    @117
    @113
    @4
    @91
    cfv
    @88
    @4
    @67
    @91
    fveq1
    @4
    @91
    @87
    @93
    fveq1i
    syl6eq
    oveq1d
    mpteq2dv
    eleq1d
    imbi2d
    @70
    wph
    @110
    @116
    wph
    @70
    @110
    @116
    stoweidlem17.5
    3com12
    3expib
    vtoclga
    sylbir
    3impib
    3com13
    3expib
    vtoclga
    3impib
    syl3anc
    eqeltrrd
    ad2antll
    @74
    @73
    wph
    @37
    simprrl
    @76
    @73
    @30
    wa
    #
    @34
    @75
    @118
    @74
    @75
    @73
    wph
    @29
    @73
    @38
    simpl
    #
    @73
    wph
    @37
    simprl
    @75
    @73
    @0
    @28
    cN
    cle
    wbr
    @29
    @119
    @75
    cN
    wph
    @63
    @73
    @37
    stoweidlem17.2
    ad2antrl
    nnnn0d
    @75
    @28
    @36
    cN
    @73
    @28
    cr
    wcel
    #
    @38
    @28
    nn0re
    #
    adantr
    @73
    @36
    cr
    wcel
    @38
    @73
    @36
    @28
    peano2nn0
    nn0red
    adantr
    wph
    @65
    @73
    @37
    wph
    cN
    stoweidlem17.2
    nnred
    ad2antrl
    @75
    @73
    @120
    @28
    @36
    cle
    wbr
    @119
    @121
    @28
    lep1
    3syl
    @37
    @36
    cN
    cle
    wbr
    @73
    wph
    @36
    cc0
    cN
    elfzle2
    ad2antll
    letrd
    @28
    cN
    elfz2nn0
    syl3anbrc
    jca32
    adantl
    @74
    @118
    @34
    wi
    @75
    @73
    @30
    @34
    pm3.31
    adantr
    mpd
    @86
    wph
    @34
    @85
    @86
    vr
    cT
    cE
    vr
    cv
    #
    @78
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    wph
    @34
    wa
    #
    @85
    wi
    #
    @125
    @81
    cA
    vr
    vt
    cT
    @124
    @80
    @92
    @123
    @79
    cE
    cmul
    @122
    @4
    @78
    fveq2
    oveq2d
    cbvmptv
    #
    eleq1i
    @126
    vt
    cT
    @77
    @105
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @127
    vg
    @125
    cA
    @104
    @125
    wceq
    #
    @131
    @85
    @126
    @132
    @130
    @84
    cA
    @132
    vt
    cT
    @129
    @83
    @132
    @105
    @82
    @77
    caddc
    @132
    @105
    @4
    @125
    cfv
    @82
    @4
    @104
    @125
    fveq1
    @4
    @125
    @81
    @128
    fveq1i
    syl6eq
    oveq2d
    mpteq2dv
    eleq1d
    imbi2d
    @110
    wph
    @34
    @131
    @34
    wph
    @110
    @131
    @34
    wph
    @110
    @131
    @34
    vr
    cT
    @31
    cE
    @122
    @6
    cfv
    #
    cmul
    co
    #
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    @111
    @131
    wi
    #
    @136
    @33
    cA
    vr
    vt
    cT
    @135
    @32
    @92
    @31
    @134
    @8
    vi
    @92
    @133
    @7
    cE
    cmul
    @122
    @4
    @6
    fveq2
    oveq2d
    sumeq2sdv
    cbvmptv
    #
    eleq1i
    @111
    vt
    cT
    @113
    @105
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @137
    vf
    @136
    cA
    @67
    @136
    wceq
    #
    @141
    @131
    @111
    @142
    @140
    @130
    cA
    @142
    vt
    cT
    @139
    @129
    @142
    @113
    @77
    @105
    caddc
    @142
    @113
    @4
    @136
    cfv
    @77
    @4
    @67
    @136
    fveq1
    @4
    @136
    @33
    @138
    fveq1i
    syl6eq
    oveq1d
    mpteq2dv
    eleq1d
    imbi2d
    @70
    wph
    @110
    @141
    wph
    @70
    @110
    @141
    stoweidlem17.4
    3com12
    3expib
    vtoclga
    sylbir
    3impib
    3com13
    3expib
    vtoclga
    sylbir
    3impib
    syl3anc
    @76
    @73
    wph
    @37
    w3a
    #
    @42
    @85
    wb
    @75
    @143
    @74
    @143
    @75
    @73
    wph
    @37
    3anass
    biimpri
    adantl
    @143
    @41
    @84
    cA
    @143
    vt
    cT
    @40
    @83
    @73
    wph
    @37
    vt
    @73
    vt
    nfv
    stoweidlem17.1
    @37
    vt
    nfv
    nf3an
    @143
    @55
    wa
    #
    @77
    @80
    caddc
    co
    @32
    @80
    caddc
    co
    #
    @83
    @40
    @144
    @77
    @32
    @80
    caddc
    @144
    @55
    @32
    cr
    wcel
    @77
    @32
    wceq
    @143
    @55
    simpr
    #
    @144
    @31
    @8
    vi
    @144
    cc0
    @28
    fzfid
    @144
    @5
    @31
    wcel
    #
    wa
    #
    cE
    @7
    @144
    @57
    @147
    @143
    @57
    @55
    wph
    @73
    @57
    @37
    stoweidlem17.7
    3ad2ant2
    adantr
    #
    adantr
    @148
    @143
    @5
    @39
    wcel
    #
    wa
    #
    @55
    wa
    #
    @7
    cr
    wcel
    #
    @148
    @144
    @150
    wa
    #
    @152
    @147
    @150
    @144
    @5
    cc0
    @28
    fzelp1
    anim2i
    @143
    @55
    @150
    an32
    sylib
    @151
    cT
    cr
    @4
    @6
    @151
    @6
    cA
    wcel
    wph
    cT
    cr
    @6
    wf
    #
    @151
    @1
    cA
    @5
    cX
    @143
    @1
    cA
    cX
    wf
    #
    @150
    wph
    @73
    @156
    @37
    stoweidlem17.3
    3ad2ant2
    adantr
    @37
    @73
    @150
    @5
    @1
    wcel
    wph
    @37
    @39
    @1
    @5
    @37
    cN
    @36
    cuz
    cfv
    wcel
    @39
    @1
    wss
    @36
    cc0
    cN
    elfzuz3
    @36
    cc0
    cN
    fzss2
    syl
    sselda
    3ad2antl3
    ffvelrnd
    @73
    wph
    @37
    @150
    simpl2
    @69
    wph
    @155
    wi
    vf
    @6
    cA
    @67
    @6
    wceq
    @68
    @155
    wph
    cT
    cr
    @67
    @6
    feq1
    imbi2d
    @71
    vtoclga
    sylc
    ffvelrnda
    #
    syl
    remulcld
    fsumrecl
    vt
    cT
    @32
    cr
    @33
    @33
    eqid
    fvmpt2
    syl2anc
    oveq1d
    @144
    @82
    @80
    @77
    caddc
    @144
    @55
    @80
    cr
    wcel
    @82
    @80
    wceq
    @146
    @144
    cE
    @79
    @149
    @144
    cT
    cr
    @4
    @78
    @144
    @38
    cT
    cr
    @78
    wf
    #
    @143
    @38
    @55
    @73
    wph
    @37
    3simpc
    adantr
    @38
    @94
    wph
    @158
    @97
    @98
    @69
    wph
    @158
    wi
    vf
    @78
    cA
    @67
    @78
    wceq
    @68
    @158
    wph
    cT
    cr
    @67
    @78
    feq1
    imbi2d
    @71
    vtoclga
    sylc
    syl
    @146
    ffvelrnd
    remulcld
    vt
    cT
    @80
    cr
    @81
    @81
    eqid
    fvmpt2
    syl2anc
    oveq2d
    @144
    @40
    cc0
    @36
    c1
    cmin
    co
    #
    cfz
    co
    #
    @8
    vi
    csu
    #
    @80
    caddc
    co
    @145
    @144
    @8
    @80
    vi
    cc0
    @36
    @143
    @36
    @13
    wcel
    #
    @55
    @37
    @73
    @162
    wph
    @36
    cc0
    cN
    elfzuz
    3ad2ant3
    adantr
    @154
    @57
    @153
    @8
    cc
    wcel
    @144
    @57
    @150
    @149
    adantr
    @143
    @150
    @55
    @153
    @157
    an32s
    @57
    @153
    wa
    @8
    cE
    @7
    remulcl
    recnd
    syl2anc
    @5
    @36
    wceq
    #
    @7
    @79
    cE
    cmul
    @163
    @4
    @6
    @78
    @5
    @36
    cX
    fveq2
    fveq1d
    oveq2d
    fsumm1
    @144
    @161
    @32
    @80
    caddc
    @144
    @160
    @31
    @8
    vi
    @144
    @159
    @28
    cc0
    cfz
    @144
    @28
    c1
    @143
    @28
    cc
    wcel
    #
    @55
    @73
    wph
    @164
    @37
    @28
    nn0cn
    3ad2ant1
    adantr
    @144
    1cnd
    pncand
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
    3eqtr4rd
    mpteq2da
    eleq1d
    syl
    mpbird
    exp32
    pm2.86i
    nn0ind
    sylc
end
