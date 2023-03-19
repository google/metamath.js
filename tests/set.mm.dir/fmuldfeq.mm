include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cmul.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "nnge1d.mm"
include "adantr.mm"
include "cn.mm"
include "cr.mm"
include "nnre.mm"
include "leid.mm"
include "3syl.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "1zzd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "caddc.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "weq.mm"
include "1z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "cmpt.mm"
include "1le1.mm"
include "a1i.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nffvmpt1.mm"
include "nfeq.mm"
include "nfim.mm"
include "imbi2d.mm"
include "cvv.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "vtoclg1f.mm"
include "syl.mm"
include "imp.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "ancli.mm"
include "anbi2d.mm"
include "feq1.mm"
include "vtoclga.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "fveq1i.mm"
include "syl6eqr.mm"
include "syl5req.mm"
include "3adant3.mm"
include "simp31.mm"
include "cuz.mm"
include "simp1.mm"
include "simp33.mm"
include "jca.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "anim1i.mm"
include "peano2fzr.mm"
include "simp32.mm"
include "simp2.mm"
include "mp3and.mm"
include "3jca.mm"
include "cmpt2.mm"
include "nfmpt21.mm"
include "nfseq.mm"
include "nf3an.mm"
include "nfan.mm"
include "nfmpt22.mm"
include "3adant1r.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "adantlr.mm"
include "fmuldfeqlem1.mm"
include "syl21anc.mm"
include "3exp.mm"
include "nnind.mm"
include "mpcom.mm"
include "mpd3an3.mm"
include "simpr.mm"
include "sylib.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "ad2antlr.mm"
include "simpl.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "chvar.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqcl.mm"
include "3eqtr4d.mm"

theorem fmuldfeq
  let wph: wff ph
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m
  assume fmuldfeq.1: |- F/ i ph
  assume fmuldfeq.2: |- F/_ t Y
  assume fmuldfeq.3: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume fmuldfeq.4: |- X = ( seq 1 ( P , U ) ` M )
  assume fmuldfeq.5: |- F = ( t e. T |-> ( i e. ( 1 ... M ) |-> ( ( U ` i ) ` t ) ) )
  assume fmuldfeq.6: |- Z = ( t e. T |-> ( seq 1 ( x. , ( F ` t ) ) ` M ) )
  assume fmuldfeq.7: |- ( ph -> T e. _V )
  assume fmuldfeq.8: |- ( ph -> M e. NN )
  assume fmuldfeq.9: |- ( ph -> U : ( 1 ... M ) --> Y )
  assume fmuldfeq.10: |- ( ( ph /\ f e. Y ) -> f : T --> RR )
  assume fmuldfeq.11: |- ( ( ph /\ f e. Y /\ g e. Y ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. Y )

  disjoint T t
  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint f i
  disjoint i t
  disjoint T i
  disjoint F f
  disjoint F g
  disjoint M f
  disjoint M g
  disjoint U f
  disjoint U g
  disjoint U t
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint M i
  disjoint U i
  disjoint b k
  disjoint b t
  disjoint T b
  disjoint k t
  disjoint T k
  disjoint F b
  disjoint F k
  disjoint b ph
  disjoint k ph
  disjoint f n
  disjoint g n
  disjoint n t
  disjoint T n
  disjoint F n
  disjoint M n
  disjoint U n
  disjoint n ph
  disjoint i k
  disjoint M k
  disjoint m n
  disjoint m t
  disjoint T m
  disjoint F m
  disjoint M m
  disjoint P m
  disjoint P n
  disjoint U m
  disjoint m ph
  assert |- ( ( ph /\ t e. T ) -> ( X ` t ) = ( Z ` t ) )

  proof
    wph
    vt
    cv
    #
    cT
    wcel
    #
    wa
    #
    @0
    cM
    cP
    cU
    c1
    cseq
    #
    cfv
    #
    cfv
    #
    cM
    cmul
    @0
    cF
    cfv
    #
    c1
    cseq
    #
    cfv
    #
    @0
    cX
    cfv
    #
    @0
    cZ
    cfv
    #
    wph
    @1
    cM
    c1
    cM
    cfz
    co
    #
    wcel
    #
    @5
    @8
    wceq
    #
    @2
    @12
    c1
    cM
    cle
    wbr
    #
    cM
    cM
    cle
    wbr
    #
    wph
    @14
    @1
    wph
    cM
    fmuldfeq.8
    nnge1d
    #
    adantr
    wph
    @15
    @1
    wph
    cM
    cn
    wcel
    #
    cM
    cr
    wcel
    @15
    fmuldfeq.8
    cM
    nnre
    cM
    leid
    3syl
    adantr
    @2
    cM
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @18
    @12
    @14
    @15
    wa
    wb
    wph
    @18
    @1
    wph
    cM
    fmuldfeq.8
    nnzd
    #
    adantr
    #
    @2
    1zzd
    @21
    cM
    c1
    cM
    elfz
    syl3anc
    mpbir2and
    @17
    wph
    @1
    @12
    w3a
    #
    @13
    wph
    @1
    @17
    @12
    fmuldfeq.8
    3ad2ant1
    wph
    @1
    vm
    cv
    #
    @11
    wcel
    #
    w3a
    #
    @0
    @23
    @3
    cfv
    #
    cfv
    #
    @23
    @7
    cfv
    #
    wceq
    #
    wi
    wph
    @1
    c1
    @11
    wcel
    #
    w3a
    #
    @0
    c1
    @3
    cfv
    #
    cfv
    #
    c1
    @7
    cfv
    #
    wceq
    #
    wi
    wph
    @1
    vn
    cv
    #
    @11
    wcel
    #
    w3a
    #
    @0
    @36
    @3
    cfv
    #
    cfv
    #
    @36
    @7
    cfv
    #
    wceq
    #
    wi
    #
    wph
    @1
    @36
    c1
    caddc
    co
    #
    @11
    wcel
    #
    w3a
    #
    @0
    @44
    @3
    cfv
    #
    cfv
    #
    @44
    @7
    cfv
    #
    wceq
    #
    wi
    @22
    @13
    wi
    vm
    vn
    cM
    @23
    c1
    wceq
    #
    @25
    @31
    @29
    @35
    @51
    @24
    @30
    wph
    @1
    @23
    c1
    @11
    eleq1
    3anbi3d
    @51
    @27
    @33
    @28
    @34
    @51
    @0
    @26
    @32
    @23
    c1
    @3
    fveq2
    fveq1d
    @23
    c1
    @7
    fveq2
    eqeq12d
    imbi12d
    vm
    vn
    weq
    #
    @25
    @38
    @29
    @42
    @52
    @24
    @37
    wph
    @1
    @23
    @36
    @11
    eleq1
    3anbi3d
    @52
    @27
    @40
    @28
    @41
    @52
    @0
    @26
    @39
    @23
    @36
    @3
    fveq2
    fveq1d
    @23
    @36
    @7
    fveq2
    eqeq12d
    imbi12d
    @23
    @44
    wceq
    #
    @25
    @46
    @29
    @50
    @53
    @24
    @45
    wph
    @1
    @23
    @44
    @11
    eleq1
    3anbi3d
    @53
    @27
    @48
    @28
    @49
    @53
    @0
    @26
    @47
    @23
    @44
    @3
    fveq2
    fveq1d
    @23
    @44
    @7
    fveq2
    eqeq12d
    imbi12d
    @23
    cM
    wceq
    #
    @25
    @22
    @29
    @13
    @54
    @24
    @12
    wph
    @1
    @23
    cM
    @11
    eleq1
    3anbi3d
    @54
    @27
    @5
    @28
    @8
    @54
    @0
    @26
    @4
    @23
    cM
    @3
    fveq2
    fveq1d
    @23
    cM
    @7
    fveq2
    eqeq12d
    imbi12d
    wph
    @1
    @35
    @30
    @2
    @34
    c1
    @6
    cfv
    #
    @33
    @19
    @34
    @55
    wceq
    1z
    cmul
    @6
    c1
    seq1
    ax-mp
    @2
    @55
    @0
    c1
    cU
    cfv
    #
    cfv
    #
    @33
    @2
    @55
    c1
    vi
    @11
    @0
    vi
    cv
    #
    cU
    cfv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    @57
    wph
    @1
    @55
    @62
    wceq
    #
    wph
    @30
    @1
    @63
    wi
    #
    wph
    @30
    c1
    c1
    cle
    wbr
    #
    @14
    @65
    wph
    1le1
    a1i
    @16
    wph
    @19
    @19
    @18
    @30
    @65
    @14
    wa
    wb
    wph
    1zzd
    #
    @66
    @20
    c1
    c1
    cM
    elfz
    syl3anc
    mpbir2and
    #
    @1
    @58
    @6
    cfv
    #
    @58
    @61
    cfv
    #
    wceq
    #
    wi
    @64
    vi
    c1
    @11
    @1
    @63
    vi
    @1
    vi
    nfv
    #
    vi
    @55
    @62
    vi
    c1
    @6
    vi
    @0
    cF
    vi
    cF
    vt
    cT
    @61
    cmpt
    fmuldfeq.5
    vi
    vt
    cT
    @61
    vi
    cT
    nfcv
    vi
    @11
    @60
    nfmpt1
    nfmpt
    nfcxfr
    vi
    @0
    nfcv
    nffv
    #
    vi
    c1
    nfcv
    nffv
    vi
    @11
    @60
    c1
    nffvmpt1
    nfeq
    nfim
    @58
    c1
    wceq
    #
    @70
    @63
    @1
    @73
    @68
    @55
    @69
    @62
    @58
    c1
    @6
    fveq2
    @58
    c1
    @61
    fveq2
    eqeq12d
    imbi2d
    @1
    @58
    @6
    @61
    @1
    @61
    cvv
    wcel
    @6
    @61
    wceq
    vi
    @11
    @60
    c1
    cM
    cfz
    ovex
    mptex
    vt
    cT
    @61
    cvv
    cF
    fmuldfeq.5
    fvmpt2
    mpan2
    fveq1d
    #
    vtoclg1f
    syl
    imp
    @2
    @30
    @57
    cr
    wcel
    @62
    @57
    wceq
    wph
    @30
    @1
    @67
    adantr
    wph
    cT
    cr
    @0
    @56
    wph
    @56
    cY
    wcel
    #
    wph
    @75
    wa
    #
    cT
    cr
    @56
    wf
    #
    wph
    @11
    cY
    c1
    cU
    fmuldfeq.9
    @67
    ffvelrnd
    #
    wph
    @75
    @78
    ancli
    wph
    vf
    cv
    #
    cY
    wcel
    #
    wa
    #
    cT
    cr
    @79
    wf
    #
    wi
    #
    @76
    @77
    wi
    vf
    @56
    cY
    @79
    @56
    wceq
    #
    @81
    @76
    @82
    @77
    @84
    @80
    @75
    wph
    @79
    @56
    cY
    eleq1
    anbi2d
    cT
    cr
    @79
    @56
    feq1
    imbi12d
    @83
    @80
    fmuldfeq.10
    a1i
    #
    vtoclga
    sylc
    ffvelrnda
    vi
    c1
    @60
    @57
    @11
    cr
    @61
    @73
    @0
    @59
    @56
    @58
    c1
    cU
    fveq2
    fveq1d
    @61
    eqid
    #
    fvmptg
    syl2anc
    eqtrd
    @0
    @32
    @56
    @19
    @32
    @56
    wceq
    1z
    cP
    cU
    c1
    seq1
    ax-mp
    fveq1i
    syl6eqr
    syl5req
    3adant3
    @36
    cn
    wcel
    #
    @43
    @46
    @50
    @87
    @43
    @46
    w3a
    #
    wph
    @37
    @45
    @42
    w3a
    #
    @1
    @50
    @87
    @43
    wph
    @1
    @45
    simp31
    #
    @88
    @37
    @45
    @42
    @88
    @87
    @45
    wa
    @36
    c1
    cuz
    cfv
    #
    wcel
    #
    @45
    wa
    @37
    @88
    @87
    @45
    @87
    @43
    @46
    simp1
    @87
    @43
    wph
    @1
    @45
    simp33
    #
    jca
    @87
    @92
    @45
    @87
    @92
    @36
    elnnuz
    biimpi
    anim1i
    @36
    c1
    cM
    peano2fzr
    3syl
    #
    @93
    @88
    wph
    @1
    @37
    @42
    @90
    @87
    @43
    wph
    @1
    @45
    simp32
    #
    @94
    @87
    @43
    @46
    simp2
    mp3and
    3jca
    @95
    wph
    @89
    wa
    vt
    cP
    cT
    cU
    vf
    vg
    vi
    cF
    cM
    @36
    cY
    wph
    @89
    vf
    wph
    vf
    nfv
    @37
    @45
    @42
    vf
    @37
    vf
    nfv
    @45
    vf
    nfv
    vf
    @40
    @41
    vf
    @0
    @39
    vf
    @36
    @3
    vf
    cP
    cU
    c1
    vf
    c1
    nfcv
    vf
    cP
    vf
    vg
    cY
    cY
    vt
    cT
    @0
    @79
    cfv
    @0
    vg
    cv
    #
    cfv
    cmul
    co
    cmpt
    #
    cmpt2
    #
    fmuldfeq.3
    vf
    vg
    cY
    cY
    @97
    nfmpt21
    nfcxfr
    vf
    cU
    nfcv
    nfseq
    vf
    @36
    nfcv
    nffv
    vf
    @0
    nfcv
    nffv
    vf
    @41
    nfcv
    nfeq
    nf3an
    nfan
    wph
    @89
    vg
    wph
    vg
    nfv
    @37
    @45
    @42
    vg
    @37
    vg
    nfv
    @45
    vg
    nfv
    vg
    @40
    @41
    vg
    @0
    @39
    vg
    @36
    @3
    vg
    cP
    cU
    c1
    vg
    c1
    nfcv
    vg
    cP
    @98
    fmuldfeq.3
    vf
    vg
    cY
    cY
    @97
    nfmpt22
    nfcxfr
    vg
    cU
    nfcv
    nfseq
    vg
    @36
    nfcv
    nffv
    vg
    @0
    nfcv
    nffv
    vg
    @41
    nfcv
    nfeq
    nf3an
    nfan
    fmuldfeq.2
    fmuldfeq.3
    fmuldfeq.5
    wph
    cT
    cvv
    wcel
    @89
    fmuldfeq.7
    adantr
    wph
    @11
    cY
    cU
    wf
    @89
    fmuldfeq.9
    adantr
    wph
    @80
    @96
    cY
    wcel
    @97
    cY
    wcel
    @89
    fmuldfeq.11
    3adant1r
    wph
    @37
    @45
    @42
    simpr1
    wph
    @37
    @45
    @42
    simpr2
    wph
    @37
    @45
    @42
    simpr3
    wph
    @80
    @82
    @89
    fmuldfeq.10
    adantlr
    fmuldfeqlem1
    syl21anc
    3exp
    nnind
    mpcom
    mpd3an3
    @9
    @5
    wceq
    @2
    @0
    cX
    @4
    fmuldfeq.4
    fveq1i
    a1i
    @2
    @1
    @8
    cr
    wcel
    @10
    @8
    wceq
    wph
    @1
    simpr
    @2
    vk
    vb
    cmul
    cr
    @6
    c1
    cM
    wph
    cM
    @91
    wcel
    #
    @1
    wph
    @17
    @99
    fmuldfeq.8
    cM
    elnnuz
    sylib
    adantr
    @2
    @58
    @11
    wcel
    #
    wa
    #
    @68
    cr
    wcel
    #
    wi
    @2
    vk
    cv
    #
    @11
    wcel
    #
    wa
    #
    @103
    @6
    cfv
    #
    cr
    wcel
    #
    wi
    vi
    vk
    @105
    @107
    vi
    @2
    @104
    vi
    wph
    @1
    vi
    fmuldfeq.1
    @71
    nfan
    @104
    vi
    nfv
    nfan
    vi
    @106
    cr
    vi
    @103
    @6
    @72
    vi
    @103
    nfcv
    nffv
    nfel1
    nfim
    vi
    vk
    weq
    #
    @101
    @105
    @102
    @107
    @108
    @100
    @104
    @2
    @58
    @103
    @11
    eleq1
    anbi2d
    @108
    @68
    @106
    cr
    @58
    @103
    @6
    fveq2
    eleq1d
    imbi12d
    @101
    @68
    @69
    cr
    @1
    @70
    wph
    @100
    @74
    ad2antlr
    @101
    @69
    @60
    cr
    @101
    @100
    @60
    cr
    wcel
    @69
    @60
    wceq
    @2
    @100
    simpr
    @101
    cT
    cr
    @0
    @59
    wph
    @100
    cT
    cr
    @59
    wf
    #
    @1
    wph
    @100
    wa
    #
    @59
    cY
    wcel
    #
    wph
    @111
    wa
    #
    @109
    wph
    @11
    cY
    @58
    cU
    fmuldfeq.9
    ffvelrnda
    #
    @110
    wph
    @111
    wph
    @100
    simpl
    @113
    jca
    @83
    @112
    @109
    wi
    vf
    @59
    cY
    @79
    @59
    wceq
    #
    @81
    @112
    @82
    @109
    @114
    @80
    @111
    wph
    @79
    @59
    cY
    eleq1
    anbi2d
    cT
    cr
    @79
    @59
    feq1
    imbi12d
    @85
    vtoclga
    sylc
    adantlr
    wph
    @1
    @100
    simplr
    ffvelrnd
    #
    vi
    @11
    @60
    cr
    @61
    @86
    fvmpt2
    syl2anc
    @115
    eqeltrd
    eqeltrd
    chvar
    @103
    cr
    wcel
    vb
    cv
    #
    cr
    wcel
    wa
    @103
    @116
    cmul
    co
    cr
    wcel
    @2
    @103
    @116
    remulcl
    adantl
    seqcl
    vt
    cT
    @8
    cr
    cZ
    fmuldfeq.6
    fvmpt2
    syl2anc
    3eqtr4d
end
