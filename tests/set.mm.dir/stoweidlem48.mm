include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "sselda.mm"
include "cc0.mm"
include "cle.mm"
include "c1.mm"
include "wral.mm"
include "crab.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "cr.mm"
include "wf.mm"
include "eleq2i.mm"
include "weq.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylbb.mm"
include "simpld.mm"
include "sylan2.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "stoweidlem16.mm"
include "fmuldfeq.mm"
include "syldan.mm"
include "cseq.mm"
include "cuz.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "adantr.mm"
include "cfz.mm"
include "nfv.mm"
include "nfan.mm"
include "ffvelrnda.mm"
include "elrab2.mm"
include "simpl.mm"
include "jca.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "adantlr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "fmptdf.mm"
include "cvv.mm"
include "simpr.mm"
include "ovex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "feq1d.mm"
include "mpbird.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqcl.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nffv.mm"
include "simpll.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "syl21anc.mm"
include "fveq1d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "eqbrtrd.mm"
include "crp.mm"
include "wrex.mm"
include "crn.mm"
include "wex.mm"
include "cuni.mm"
include "eluni.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "3syl.mm"
include "biimpa.mm"
include "adantrl.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "reximdv.mm"
include "adantrr.mm"
include "mpd.mm"
include "exlimdv.mm"
include "simplll.mm"
include "w3a.mm"
include "nf3an.mm"
include "nfim.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "3anbi23d.mm"
include "3impa.mm"
include "chvar.mm"
include "syl3anc.mm"
include "reximdva.mm"
include "nfeq1.mm"
include "eqeq12d.mm"
include "biimprd.mm"
include "fmul01lt1.mm"
include "ralrimi.mm"

theorem stoweidlem48
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  assume stoweidlem48.1: |- F/ i ph
  assume stoweidlem48.2: |- F/ t ph
  assume stoweidlem48.3: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem48.4: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume stoweidlem48.5: |- X = ( seq 1 ( P , U ) ` M )
  assume stoweidlem48.6: |- F = ( t e. T |-> ( i e. ( 1 ... M ) |-> ( ( U ` i ) ` t ) ) )
  assume stoweidlem48.7: |- Z = ( t e. T |-> ( seq 1 ( x. , ( F ` t ) ) ` M ) )
  assume stoweidlem48.8: |- ( ph -> M e. NN )
  assume stoweidlem48.9: |- ( ph -> W : ( 1 ... M ) --> V )
  assume stoweidlem48.10: |- ( ph -> U : ( 1 ... M ) --> Y )
  assume stoweidlem48.11: |- ( ph -> D C_ U. ran W )
  assume stoweidlem48.12: |- ( ph -> D C_ T )
  assume stoweidlem48.13: |- ( ( ph /\ i e. ( 1 ... M ) ) -> A. t e. ( W ` i ) ( ( U ` i ) ` t ) < E )
  assume stoweidlem48.14: |- ( ph -> T e. _V )
  assume stoweidlem48.15: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem48.16: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem48.17: |- ( ph -> E e. RR+ )

  disjoint f g
  disjoint f h
  disjoint f t
  disjoint A f
  disjoint g h
  disjoint g t
  disjoint A g
  disjoint h t
  disjoint A h
  disjoint A t
  disjoint f i
  disjoint T f
  disjoint h i
  disjoint T h
  disjoint i t
  disjoint T i
  disjoint T t
  disjoint F f
  disjoint F g
  disjoint M f
  disjoint M g
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U t
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint T g
  disjoint D i
  disjoint E i
  disjoint M i
  disjoint U i
  disjoint W i
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint j t
  disjoint k t
  disjoint D j
  disjoint D k
  disjoint E j
  disjoint M j
  disjoint M k
  disjoint W j
  disjoint j w
  disjoint t w
  disjoint F j
  disjoint F k
  disjoint j ph
  disjoint k ph
  disjoint M w
  disjoint W w
  disjoint ph w
  disjoint k x
  assert |- ( ph -> A. t e. D ( X ` t ) < E )

  proof
    wph
    vt
    cv
    #
    cX
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cD
    stoweidlem48.2
    wph
    @0
    cD
    wcel
    #
    @2
    wph
    @3
    wa
    #
    @1
    @0
    cZ
    cfv
    #
    cE
    clt
    wph
    @3
    @0
    cT
    wcel
    #
    @1
    @5
    wceq
    wph
    cD
    cT
    @0
    stoweidlem48.12
    sselda
    #
    wph
    vt
    cP
    cT
    cU
    vf
    vg
    vi
    cF
    cM
    cX
    cY
    cZ
    stoweidlem48.1
    vt
    cY
    cc0
    @0
    vh
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @9
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    vh
    cA
    crab
    #
    stoweidlem48.3
    @13
    vt
    vh
    cA
    @12
    vt
    cT
    nfra1
    vt
    cA
    nfcv
    nfrab
    nfcxfr
    stoweidlem48.4
    stoweidlem48.5
    stoweidlem48.6
    stoweidlem48.7
    stoweidlem48.14
    stoweidlem48.8
    stoweidlem48.10
    vf
    cv
    #
    cY
    wcel
    #
    wph
    @15
    cA
    wcel
    #
    cT
    cr
    @15
    wf
    #
    @16
    @17
    cc0
    @0
    @15
    cfv
    #
    cle
    wbr
    #
    @19
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @16
    @15
    @14
    wcel
    @17
    @23
    wa
    cY
    @14
    @15
    stoweidlem48.3
    eleq2i
    @13
    @23
    vh
    @15
    cA
    vh
    vf
    weq
    #
    @12
    @22
    vt
    cT
    @24
    @10
    @20
    @11
    @21
    @24
    @9
    @19
    cc0
    cle
    @0
    @8
    @15
    fveq1
    #
    breq2d
    @24
    @9
    @19
    c1
    cle
    @25
    breq1d
    anbi12d
    ralbidv
    elrab
    sylbb
    simpld
    stoweidlem48.15
    sylan2
    wph
    vt
    cA
    cT
    vf
    vg
    vh
    vt
    cT
    @19
    @0
    vg
    cv
    cfv
    cmul
    co
    cmpt
    #
    cY
    stoweidlem48.2
    stoweidlem48.3
    @26
    eqid
    stoweidlem48.15
    stoweidlem48.16
    stoweidlem16
    fmuldfeq
    syldan
    @4
    @5
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
    cE
    clt
    @4
    @6
    @29
    cr
    wcel
    @5
    @29
    wceq
    @7
    @4
    vk
    vj
    cmul
    cr
    @27
    c1
    cM
    wph
    cM
    c1
    cuz
    cfv
    wcel
    #
    @3
    wph
    cM
    cn
    wcel
    #
    @30
    stoweidlem48.8
    cM
    elnnuz
    sylib
    adantr
    @4
    c1
    cM
    cfz
    co
    #
    cr
    vk
    cv
    #
    @27
    wph
    @3
    @6
    @32
    cr
    @27
    wf
    #
    @7
    wph
    @6
    wa
    #
    @34
    @32
    cr
    vi
    @32
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
    wf
    @35
    vi
    @32
    @38
    cr
    @39
    wph
    @6
    vi
    stoweidlem48.1
    @6
    vi
    nfv
    nfan
    @35
    @36
    @32
    wcel
    #
    wa
    cT
    cr
    @0
    @37
    wph
    @40
    cT
    cr
    @37
    wf
    #
    @6
    wph
    @40
    wa
    #
    @37
    cA
    wcel
    #
    wph
    @43
    wa
    #
    @41
    @42
    @43
    cc0
    @38
    cle
    wbr
    #
    @38
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @42
    @37
    cY
    wcel
    @43
    @48
    wa
    wph
    @32
    cY
    @36
    cU
    stoweidlem48.10
    ffvelrnda
    @13
    @48
    vh
    @37
    cA
    cY
    @8
    @37
    wceq
    #
    @12
    @47
    vt
    cT
    @49
    @10
    @45
    @11
    @46
    @49
    @9
    @38
    cc0
    cle
    @0
    @8
    @37
    fveq1
    #
    breq2d
    @49
    @9
    @38
    c1
    cle
    @50
    breq1d
    anbi12d
    ralbidv
    stoweidlem48.3
    elrab2
    sylib
    #
    simpld
    #
    @42
    wph
    @43
    wph
    @40
    simpl
    @52
    jca
    wph
    @17
    wa
    #
    @18
    wi
    @44
    @41
    wi
    vf
    @37
    cA
    @15
    @37
    wceq
    #
    @53
    @44
    @18
    @41
    @54
    @17
    @43
    wph
    @15
    @37
    cA
    eleq1
    anbi2d
    cT
    cr
    @15
    @37
    feq1
    imbi12d
    stoweidlem48.15
    vtoclg
    sylc
    adantlr
    wph
    @6
    @40
    simplr
    ffvelrnd
    #
    @39
    eqid
    #
    fmptdf
    @35
    @32
    cr
    @27
    @39
    @35
    @6
    @39
    cvv
    wcel
    #
    @27
    @39
    wceq
    wph
    @6
    simpr
    @32
    cvv
    wcel
    @57
    @35
    c1
    cM
    cfz
    ovex
    vi
    @32
    @38
    cvv
    mptexg
    mp1i
    vt
    cT
    @39
    cvv
    cF
    stoweidlem48.6
    fvmpt2
    syl2anc
    #
    feq1d
    mpbird
    syldan
    #
    ffvelrnda
    @33
    cr
    wcel
    vj
    cv
    #
    cr
    wcel
    wa
    @33
    @60
    cmul
    co
    cr
    wcel
    @4
    @33
    @60
    remulcl
    adantl
    seqcl
    vt
    cT
    @29
    cr
    cZ
    stoweidlem48.7
    fvmpt2
    syl2anc
    @4
    @28
    @27
    vi
    vj
    cE
    cM
    vi
    @0
    cF
    vi
    cF
    vt
    cT
    @39
    cmpt
    stoweidlem48.6
    vi
    vt
    cT
    @39
    vi
    cT
    nfcv
    vi
    @32
    @38
    nfmpt1
    nfmpt
    nfcxfr
    vi
    @0
    nfcv
    nffv
    #
    wph
    @3
    vi
    stoweidlem48.1
    @3
    vi
    nfv
    nfan
    #
    vj
    @28
    nfcv
    @28
    eqid
    wph
    @31
    @3
    stoweidlem48.8
    adantr
    @59
    @4
    @40
    wa
    #
    cc0
    @38
    @36
    @27
    cfv
    #
    cle
    @63
    wph
    @40
    @6
    @45
    wph
    @3
    @40
    simpll
    #
    @4
    @40
    simpr
    #
    @4
    @6
    @40
    @7
    adantr
    #
    @42
    @6
    wa
    #
    @45
    @46
    @42
    @47
    vt
    cT
    @42
    @43
    @48
    @51
    simprd
    r19.21bi
    #
    simpld
    syl21anc
    @63
    @64
    @36
    @39
    cfv
    #
    @38
    @63
    wph
    @6
    @64
    @70
    wceq
    @65
    @67
    @35
    @36
    @27
    @39
    @58
    fveq1d
    syl2anc
    @63
    @40
    @38
    cr
    wcel
    #
    @70
    @38
    wceq
    @66
    @63
    wph
    @6
    @40
    @71
    @65
    @67
    @66
    @55
    syl21anc
    vi
    @32
    @38
    cr
    @39
    @56
    fvmpt2
    syl2anc
    eqtrd
    #
    breqtrrd
    @63
    @64
    @38
    c1
    cle
    @72
    @63
    wph
    @40
    @6
    @46
    @65
    @66
    @67
    @68
    @45
    @46
    @69
    simprd
    syl21anc
    eqbrtrd
    wph
    cE
    crp
    wcel
    @3
    stoweidlem48.17
    adantr
    @4
    @0
    @60
    cU
    cfv
    #
    cfv
    #
    cE
    clt
    wbr
    #
    vj
    @32
    wrex
    #
    @60
    @27
    cfv
    #
    cE
    clt
    wbr
    #
    vj
    @32
    wrex
    @4
    @0
    @60
    cW
    cfv
    #
    wcel
    #
    vj
    @32
    wrex
    #
    @76
    @4
    @0
    vw
    cv
    #
    wcel
    #
    @82
    cW
    crn
    #
    wcel
    #
    wa
    #
    vw
    wex
    #
    @81
    @4
    @0
    @84
    cuni
    #
    wcel
    @87
    wph
    cD
    @88
    @0
    stoweidlem48.11
    sselda
    vw
    @0
    @84
    eluni
    sylib
    wph
    @87
    @81
    wi
    @3
    wph
    @86
    @81
    vw
    wph
    @86
    @81
    wph
    @86
    wa
    @79
    @82
    wceq
    #
    vj
    @32
    wrex
    #
    @81
    wph
    @85
    @90
    @83
    wph
    @85
    @90
    wph
    @32
    cV
    cW
    wf
    cW
    @32
    wfn
    @85
    @90
    wb
    stoweidlem48.9
    @32
    cV
    cW
    ffn
    vj
    @32
    @82
    cW
    fvelrnb
    3syl
    biimpa
    adantrl
    wph
    @83
    @90
    @81
    wi
    @85
    wph
    @83
    wa
    #
    @89
    @80
    vj
    @32
    @91
    @89
    @80
    @91
    @89
    wa
    @0
    @82
    @79
    wph
    @83
    @89
    simplr
    @91
    @89
    simpr
    eleqtrrd
    ex
    reximdv
    adantrr
    mpd
    ex
    exlimdv
    adantr
    mpd
    @4
    @80
    @75
    vj
    @32
    @4
    @60
    @32
    wcel
    #
    wa
    #
    @80
    @75
    @93
    @80
    wa
    wph
    @92
    @80
    @75
    wph
    @3
    @92
    @80
    simplll
    @4
    @92
    @80
    simplr
    @93
    @80
    simpr
    wph
    @40
    @0
    @36
    cW
    cfv
    #
    wcel
    #
    w3a
    #
    @38
    cE
    clt
    wbr
    #
    wi
    wph
    @92
    @80
    w3a
    #
    @75
    wi
    vi
    vj
    @98
    @75
    vi
    wph
    @92
    @80
    vi
    stoweidlem48.1
    @92
    vi
    nfv
    #
    @80
    vi
    nfv
    nf3an
    @75
    vi
    nfv
    nfim
    vi
    vj
    weq
    #
    @96
    @98
    @97
    @75
    @100
    @40
    @92
    @95
    @80
    wph
    @36
    @60
    @32
    eleq1
    #
    @100
    @94
    @79
    @0
    @36
    @60
    cW
    fveq2
    eleq2d
    3anbi23d
    @100
    @38
    @74
    cE
    clt
    @100
    @0
    @37
    @73
    @36
    @60
    cU
    fveq2
    fveq1d
    #
    breq1d
    imbi12d
    wph
    @40
    @95
    @97
    @42
    @97
    vt
    @94
    stoweidlem48.13
    r19.21bi
    3impa
    chvar
    syl3anc
    ex
    reximdva
    mpd
    @4
    @75
    @78
    vj
    @32
    @93
    @78
    @75
    @93
    @77
    @74
    cE
    clt
    @63
    @64
    @38
    wceq
    #
    wi
    @93
    @77
    @74
    wceq
    #
    wi
    vi
    vj
    @93
    @104
    vi
    @4
    @92
    vi
    @62
    @99
    nfan
    vi
    @77
    @74
    vi
    @60
    @27
    @61
    vi
    @60
    nfcv
    nffv
    nfeq1
    nfim
    @100
    @63
    @93
    @103
    @104
    @100
    @40
    @92
    @4
    @101
    anbi2d
    @100
    @64
    @77
    @38
    @74
    @36
    @60
    @27
    fveq2
    @102
    eqeq12d
    imbi12d
    @72
    chvar
    breq1d
    biimprd
    reximdva
    mpd
    fmul01lt1
    eqbrtrd
    eqbrtrd
    ex
    ralrimi
end
