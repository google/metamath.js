include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "cn.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "nnred.mm"
include "leidd.mm"
include "ancli.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "caddc.mm"
include "cz.mm"
include "cc.mm"
include "1z.mm"
include "cr.mm"
include "wf.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "feq1.mm"
include "vtoclg.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fsum1.mm"
include "sylancr.mm"
include "mpteq2da.mm"
include "feqmptd.mm"
include "eqtr4d.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "simprl.mm"
include "simpll.mm"
include "simprr.mm"
include "w3a.mm"
include "simp1.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "1red.mm"
include "readdcld.mm"
include "3ad2ant1.mm"
include "lep1d.mm"
include "simp3.mm"
include "letrd.mm"
include "jca.mm"
include "syl3anc.mm"
include "simplr.mm"
include "mpd.mm"
include "nfv.mm"
include "nf3an.mm"
include "simpl2.mm"
include "simpll1.mm"
include "1zzd.mm"
include "nnzd.mm"
include "ad2antrr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "elfzle1.mm"
include "zred.mm"
include "elfzle2.mm"
include "simpll3.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "3adant3.mm"
include "fsump1.mm"
include "simpr.mm"
include "fzfid.mm"
include "letrp1.mm"
include "simpl3.mm"
include "adantlr.mm"
include "fsumrecl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "peano2nn.mm"
include "nnge1d.mm"
include "anabsi7.mm"
include "oveq2d.mm"
include "simpl1.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "nfmpt1.mm"
include "stoweidlem8.mm"
include "syl31anc.mm"
include "exp31.mm"
include "nnind.mm"
include "syl3c.mm"
include "syl5eqel.mm"

theorem stoweidlem20
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cM: class M
  let vy: setvar y
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  assume stoweidlem20.1: |- F/ t ph
  assume stoweidlem20.2: |- F = ( t e. T |-> sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) )
  assume stoweidlem20.3: |- ( ph -> M e. NN )
  assume stoweidlem20.4: |- ( ph -> G : ( 1 ... M ) --> A )
  assume stoweidlem20.5: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem20.6: |- ( ( ph /\ f e. A ) -> f : T --> RR )

  disjoint f g
  disjoint f i
  disjoint f t
  disjoint G f
  disjoint g i
  disjoint g t
  disjoint G g
  disjoint i t
  disjoint G i
  disjoint G t
  disjoint A f
  disjoint A g
  disjoint T f
  disjoint T g
  disjoint T i
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint M i
  disjoint M t
  disjoint f y
  disjoint g y
  disjoint i y
  disjoint t y
  disjoint G y
  disjoint A y
  disjoint T y
  disjoint ph y
  disjoint i n
  disjoint i x
  disjoint n t
  disjoint n x
  disjoint G n
  disjoint t x
  disjoint G x
  disjoint M n
  disjoint M x
  disjoint A n
  disjoint A x
  disjoint T n
  disjoint T x
  disjoint n ph
  disjoint ph x
  disjoint x y
  disjoint M y
  disjoint k x
  assert |- ( ph -> F e. A )

  proof
    wph
    cF
    vt
    cT
    c1
    cM
    cfz
    co
    #
    vt
    cv
    #
    vi
    cv
    #
    cG
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmpt
    #
    cA
    stoweidlem20.2
    wph
    cM
    cn
    wcel
    #
    @7
    wph
    cM
    cM
    cle
    wbr
    #
    wa
    #
    @6
    cA
    wcel
    #
    stoweidlem20.3
    stoweidlem20.3
    wph
    @8
    wph
    cM
    wph
    cM
    stoweidlem20.3
    nnred
    leidd
    ancli
    vn
    cv
    #
    cn
    wcel
    #
    wph
    @11
    cM
    cle
    wbr
    #
    wa
    #
    vt
    cT
    c1
    @11
    cfz
    co
    #
    @4
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
    wi
    @7
    @9
    @10
    wi
    #
    wi
    vn
    cM
    cn
    @11
    cM
    wceq
    #
    @12
    @7
    @19
    @20
    @11
    cM
    cn
    eleq1
    @21
    @14
    @9
    @18
    @10
    @21
    @13
    @8
    wph
    @11
    cM
    cM
    cle
    breq1
    anbi2d
    @21
    @17
    @6
    cA
    @21
    vt
    cT
    @16
    @5
    @21
    @15
    @0
    @4
    vi
    @11
    cM
    c1
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    imbi12d
    wph
    vx
    cv
    #
    cM
    cle
    wbr
    #
    wa
    #
    vt
    cT
    c1
    @22
    cfz
    co
    #
    @4
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
    c1
    cM
    cle
    wbr
    #
    wa
    #
    vt
    cT
    c1
    c1
    cfz
    co
    #
    @4
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
    vy
    cv
    #
    cM
    cle
    wbr
    #
    wa
    #
    vt
    cT
    c1
    @35
    cfz
    co
    #
    @4
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
    @35
    c1
    caddc
    co
    #
    cM
    cle
    wbr
    #
    wa
    #
    vt
    cT
    c1
    @43
    cfz
    co
    #
    @4
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @19
    vx
    vy
    @11
    @22
    c1
    wceq
    #
    @24
    @30
    @28
    @34
    @50
    @23
    @29
    wph
    @22
    c1
    cM
    cle
    breq1
    anbi2d
    @50
    @27
    @33
    cA
    @50
    vt
    cT
    @26
    @32
    @50
    @25
    @31
    @4
    vi
    @22
    c1
    c1
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    @22
    @35
    wceq
    #
    @24
    @37
    @28
    @41
    @51
    @23
    @36
    wph
    @22
    @35
    cM
    cle
    breq1
    anbi2d
    @51
    @27
    @40
    cA
    @51
    vt
    cT
    @26
    @39
    @51
    @25
    @38
    @4
    vi
    @22
    @35
    c1
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    @22
    @43
    wceq
    #
    @24
    @45
    @28
    @49
    @52
    @23
    @44
    wph
    @22
    @43
    cM
    cle
    breq1
    anbi2d
    @52
    @27
    @48
    cA
    @52
    vt
    cT
    @26
    @47
    @52
    @25
    @46
    @4
    vi
    @22
    @43
    c1
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    @22
    @11
    wceq
    #
    @24
    @14
    @28
    @18
    @53
    @23
    @13
    wph
    @22
    @11
    cM
    cle
    breq1
    anbi2d
    @53
    @27
    @17
    cA
    @53
    vt
    cT
    @26
    @16
    @53
    @25
    @15
    @4
    vi
    @22
    @11
    c1
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi12d
    wph
    @34
    @29
    wph
    @33
    c1
    cG
    cfv
    #
    cA
    wph
    @33
    vt
    cT
    @1
    @54
    cfv
    #
    cmpt
    @54
    wph
    vt
    cT
    @32
    @55
    stoweidlem20.1
    wph
    @1
    cT
    wcel
    #
    wa
    #
    c1
    cz
    wcel
    #
    @55
    cc
    wcel
    @32
    @55
    wceq
    1z
    @57
    @55
    wph
    cT
    cr
    @1
    @54
    wph
    @54
    cA
    wcel
    #
    wph
    @59
    wa
    #
    cT
    cr
    @54
    wf
    #
    wph
    @0
    cA
    c1
    cG
    stoweidlem20.4
    wph
    cM
    c1
    cuz
    cfv
    #
    wcel
    c1
    @0
    wcel
    wph
    cM
    cn
    @62
    stoweidlem20.3
    nnuz
    syl6eleq
    c1
    cM
    eluzfz1
    syl
    ffvelrnd
    #
    wph
    @59
    @63
    ancli
    wph
    vf
    cv
    #
    cA
    wcel
    #
    wa
    #
    cT
    cr
    @64
    wf
    #
    wi
    #
    @60
    @61
    wi
    vf
    @54
    cA
    @64
    @54
    wceq
    #
    @66
    @60
    @67
    @61
    @69
    @65
    @59
    wph
    @64
    @54
    cA
    eleq1
    anbi2d
    cT
    cr
    @64
    @54
    feq1
    imbi12d
    stoweidlem20.6
    vtoclg
    sylc
    #
    ffvelrnda
    recnd
    @4
    @55
    vi
    c1
    @2
    c1
    wceq
    @1
    @3
    @54
    @2
    c1
    cG
    fveq2
    fveq1d
    fsum1
    sylancr
    mpteq2da
    wph
    vt
    cT
    cr
    @54
    @70
    feqmptd
    eqtr4d
    @63
    eqeltrd
    adantr
    @35
    cn
    wcel
    #
    @42
    @45
    @49
    @71
    @42
    wa
    #
    @45
    wa
    #
    wph
    @71
    @44
    @41
    @49
    @72
    wph
    @44
    simprl
    #
    @71
    @42
    @45
    simpll
    #
    @72
    wph
    @44
    simprr
    #
    @73
    @37
    @41
    @73
    wph
    @71
    @44
    @37
    @74
    @75
    @76
    wph
    @71
    @44
    w3a
    #
    wph
    @36
    wph
    @71
    @44
    simp1
    #
    @77
    @35
    @43
    cM
    @71
    wph
    @35
    cr
    wcel
    #
    @44
    @35
    nnre
    3ad2ant2
    #
    @77
    @35
    c1
    @80
    @77
    1red
    readdcld
    #
    @77
    cM
    wph
    @71
    @7
    @44
    stoweidlem20.3
    3ad2ant1
    nnred
    #
    @77
    @35
    @80
    lep1d
    wph
    @71
    @44
    simp3
    #
    letrd
    jca
    syl3anc
    @71
    @42
    @45
    simplr
    mpd
    @77
    @41
    wa
    #
    @48
    vt
    cT
    @1
    @40
    cfv
    #
    @1
    @43
    cG
    cfv
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    @77
    @48
    @89
    wceq
    @41
    @77
    vt
    cT
    @47
    @88
    wph
    @71
    @44
    vt
    stoweidlem20.1
    @71
    vt
    nfv
    @44
    vt
    nfv
    nf3an
    #
    @77
    @56
    wa
    #
    @47
    @39
    @87
    caddc
    co
    @88
    @91
    @4
    @87
    vi
    c1
    @35
    @91
    @35
    cn
    @62
    wph
    @71
    @44
    @56
    simpl2
    nnuz
    syl6eleq
    @91
    @2
    @46
    wcel
    #
    wa
    #
    wph
    @2
    @0
    wcel
    #
    @56
    @4
    cc
    wcel
    wph
    @71
    @44
    @56
    @92
    simpll1
    @93
    @58
    cM
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    c1
    @2
    cle
    wbr
    #
    @2
    cM
    cle
    wbr
    #
    @94
    @93
    1zzd
    @77
    @95
    @56
    @92
    wph
    @71
    @95
    @44
    wph
    cM
    stoweidlem20.3
    nnzd
    3ad2ant1
    #
    ad2antrr
    @92
    @96
    @91
    @2
    c1
    @43
    elfzelz
    #
    adantl
    @92
    @97
    @91
    @2
    c1
    @43
    elfzle1
    adantl
    @93
    @2
    @43
    cM
    @92
    @2
    cr
    wcel
    #
    @91
    @92
    @2
    @100
    zred
    adantl
    @77
    @43
    cr
    wcel
    #
    @56
    @92
    @81
    ad2antrr
    @77
    cM
    cr
    wcel
    #
    @56
    @92
    @82
    ad2antrr
    @92
    @2
    @43
    cle
    wbr
    #
    @91
    @2
    c1
    @43
    elfzle2
    adantl
    wph
    @71
    @44
    @56
    @92
    simpll3
    letrd
    @2
    c1
    cM
    elfz4
    #
    syl32anc
    @77
    @56
    @92
    simplr
    wph
    @94
    @56
    w3a
    #
    @4
    @106
    cT
    cr
    @1
    @3
    @106
    @3
    cA
    wcel
    #
    wph
    @107
    wa
    #
    cT
    cr
    @3
    wf
    #
    wph
    @94
    @107
    @56
    wph
    @0
    cA
    @2
    cG
    stoweidlem20.4
    ffvelrnda
    3adant3
    #
    @106
    wph
    @107
    wph
    @94
    @56
    simp1
    @110
    jca
    @68
    @108
    @109
    wi
    vf
    @3
    cA
    @64
    @3
    wceq
    #
    @66
    @108
    @67
    @109
    @111
    @65
    @107
    wph
    @64
    @3
    cA
    eleq1
    anbi2d
    cT
    cr
    @64
    @3
    feq1
    imbi12d
    stoweidlem20.6
    vtoclg
    sylc
    wph
    @94
    @56
    simp3
    ffvelrnd
    #
    recnd
    syl3anc
    @2
    @43
    wceq
    @1
    @3
    @86
    @2
    @43
    cG
    fveq2
    fveq1d
    fsump1
    @91
    @85
    @39
    @87
    caddc
    @91
    @56
    @39
    cr
    wcel
    @85
    @39
    wceq
    @77
    @56
    simpr
    #
    @91
    @38
    @4
    vi
    @91
    c1
    @35
    fzfid
    @91
    @2
    @38
    wcel
    #
    wa
    #
    wph
    @94
    @56
    @4
    cr
    wcel
    wph
    @71
    @44
    @56
    @114
    simpll1
    @115
    @58
    @95
    @96
    @97
    @98
    @94
    @115
    1zzd
    @77
    @95
    @56
    @114
    @99
    ad2antrr
    @114
    @96
    @91
    @2
    c1
    @35
    elfzelz
    #
    adantl
    @114
    @97
    @91
    @2
    c1
    @35
    elfzle1
    adantl
    @77
    @114
    @98
    @56
    @77
    @114
    wa
    #
    @2
    @43
    cM
    @114
    @101
    @77
    @114
    @2
    @116
    zred
    adantl
    #
    @77
    @102
    @114
    @81
    adantr
    @77
    @103
    @114
    @82
    adantr
    @117
    @101
    @79
    @2
    @35
    cle
    wbr
    #
    @104
    @118
    @77
    @79
    @114
    @80
    adantr
    @114
    @119
    @77
    @2
    c1
    @35
    elfzle2
    adantl
    @2
    @35
    letrp1
    syl3anc
    wph
    @71
    @44
    @114
    simpl3
    letrd
    adantlr
    @105
    syl32anc
    @77
    @56
    @114
    simplr
    @112
    syl3anc
    fsumrecl
    vt
    cT
    @39
    cr
    @40
    @40
    eqid
    fvmpt2
    syl2anc
    oveq1d
    eqtr4d
    mpteq2da
    adantr
    @84
    vt
    cT
    @85
    @1
    vt
    cT
    @87
    cmpt
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    @89
    cA
    @77
    @123
    @89
    wceq
    @41
    @77
    vt
    cT
    @122
    @88
    @90
    @91
    @121
    @87
    @85
    caddc
    @91
    @56
    @87
    cr
    wcel
    @121
    @87
    wceq
    @113
    @77
    cT
    cr
    @1
    @86
    @77
    wph
    @86
    cA
    wcel
    #
    cT
    cr
    @86
    wf
    #
    @78
    @77
    wph
    @43
    @0
    wcel
    #
    @124
    @78
    @77
    @58
    @95
    @43
    cz
    wcel
    #
    c1
    @43
    cle
    wbr
    #
    @44
    @126
    @77
    1zzd
    @99
    @71
    wph
    @127
    @44
    @71
    @43
    @35
    peano2nn
    #
    nnzd
    3ad2ant2
    @71
    wph
    @128
    @44
    @71
    @43
    @129
    nnge1d
    3ad2ant2
    @83
    @43
    c1
    cM
    elfz4
    syl32anc
    #
    wph
    @0
    cA
    @43
    cG
    stoweidlem20.4
    ffvelrnda
    #
    syl2anc
    wph
    @124
    @125
    @68
    wph
    @124
    wa
    #
    @125
    wi
    vf
    @86
    cA
    @64
    @86
    wceq
    #
    @66
    @132
    @67
    @125
    @133
    @65
    @124
    wph
    @64
    @86
    cA
    eleq1
    anbi2d
    cT
    cr
    @64
    @86
    feq1
    imbi12d
    stoweidlem20.6
    vtoclg
    anabsi7
    #
    syl2anc
    ffvelrnda
    vt
    cT
    @87
    cr
    @120
    @120
    eqid
    fvmpt2
    syl2anc
    oveq2d
    mpteq2da
    adantr
    @84
    wph
    @41
    @120
    cA
    wcel
    #
    @123
    cA
    wcel
    wph
    @71
    @44
    @41
    simpl1
    #
    @77
    @41
    simpr
    @84
    wph
    @126
    @135
    @136
    @77
    @126
    @41
    @130
    adantr
    wph
    @126
    wa
    @86
    @120
    cA
    wph
    @126
    @124
    @86
    @120
    wceq
    @131
    @132
    vt
    cT
    cr
    @86
    @134
    feqmptd
    syldan
    @131
    eqeltrrd
    syl2anc
    wph
    vt
    cA
    cT
    vf
    vg
    @40
    @120
    stoweidlem20.5
    vt
    cT
    @39
    nfmpt1
    vt
    cT
    @87
    nfmpt1
    stoweidlem8
    syl3anc
    eqeltrrd
    eqeltrd
    syl31anc
    exp31
    nnind
    vtoclg
    syl3c
    syl5eqel
end
