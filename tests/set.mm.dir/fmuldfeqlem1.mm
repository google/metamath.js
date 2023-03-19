include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cfv.mm"
include "c1.mm"
include "cseq.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cr.mm"
include "cmpt.mm"
include "wceq.mm"
include "cvv.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "adantl.mm"
include "adantr.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "ancli.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "fvmptd.mm"
include "oveq2d.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl.mm"
include "seqp1.mm"
include "cmpt2.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq2dv.mm"
include "cbvmpt2.mm"
include "eqtri.mm"
include "a1i.mm"
include "nfmpt1.mm"
include "nfmpt2.mm"
include "nfcxfr.mm"
include "nfseq.mm"
include "nffv.mm"
include "nfeq2.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "oveq12d.mm"
include "mpteq2da.mm"
include "eqid.mm"
include "w3a.mm"
include "3simpc.mm"
include "nf3an.mm"
include "3anbi2d.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "3anbi3d.mm"
include "vtocl2gf.mm"
include "mpcom.mm"
include "fmulcl.mm"
include "mptexg.mm"
include "ovmpt2d.mm"
include "eqtrd.mm"
include "nfmpt21.mm"
include "nfel1.mm"
include "nff.mm"
include "remulcld.mm"
include "fvmpt2d.mm"
include "3eqtr4rd.mm"

theorem fmuldfeqlem1
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
  let cN: class N
  let cY: class Y
  let vh: setvar h
  let vl: setvar l
  let vj: setvar j
  assume fmuldfeqlem1.1: |- F/ f ph
  assume fmuldfeqlem1.2: |- F/ g ph
  assume fmuldfeqlem1.3: |- F/_ t Y
  assume fmuldfeqlem1.5: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume fmuldfeqlem1.6: |- F = ( t e. T |-> ( i e. ( 1 ... M ) |-> ( ( U ` i ) ` t ) ) )
  assume fmuldfeqlem1.7: |- ( ph -> T e. _V )
  assume fmuldfeqlem1.8: |- ( ph -> U : ( 1 ... M ) --> Y )
  assume fmuldfeqlem1.9: |- ( ( ph /\ f e. Y /\ g e. Y ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. Y )
  assume fmuldfeqlem1.10: |- ( ph -> N e. ( 1 ... M ) )
  assume fmuldfeqlem1.11: |- ( ph -> ( N + 1 ) e. ( 1 ... M ) )
  assume fmuldfeqlem1.12: |- ( ph -> ( ( seq 1 ( P , U ) ` N ) ` t ) = ( seq 1 ( x. , ( F ` t ) ) ` N ) )
  assume fmuldfeqlem1.13: |- ( ( ph /\ f e. Y ) -> f : T --> RR )

  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint N f
  disjoint N t
  disjoint U f
  disjoint U t
  disjoint Y f
  disjoint Y g
  disjoint i t
  disjoint U i
  disjoint M i
  disjoint f h
  disjoint f l
  disjoint g h
  disjoint g l
  disjoint h l
  disjoint h t
  disjoint T h
  disjoint l t
  disjoint T l
  disjoint N h
  disjoint N l
  disjoint U h
  disjoint U l
  disjoint Y h
  disjoint Y l
  disjoint P h
  disjoint P l
  disjoint h ph
  disjoint l ph
  disjoint i j
  disjoint j t
  disjoint U j
  disjoint M j
  disjoint N j
  disjoint T j
  disjoint j ph
  assert |- ( ( ph /\ t e. T ) -> ( ( seq 1 ( P , U ) ` ( N + 1 ) ) ` t ) = ( seq 1 ( x. , ( F ` t ) ) ` ( N + 1 ) ) )

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
    cN
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
    cN
    c1
    caddc
    co
    #
    @3
    cfv
    #
    cmul
    co
    #
    @5
    @0
    @6
    cU
    cfv
    #
    cfv
    #
    cmul
    co
    #
    @6
    @4
    cfv
    #
    @0
    @6
    cP
    cU
    c1
    cseq
    #
    cfv
    #
    cfv
    #
    @2
    @7
    @10
    @5
    cmul
    @2
    vj
    @6
    @0
    vj
    cv
    #
    cU
    cfv
    #
    cfv
    #
    @10
    c1
    cM
    cfz
    co
    #
    @3
    cr
    @1
    @3
    vj
    @19
    @18
    cmpt
    #
    wceq
    wph
    @1
    @3
    vi
    @19
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
    @20
    @1
    @24
    cvv
    wcel
    @3
    @24
    wceq
    vi
    @19
    @23
    c1
    cM
    cfz
    ovex
    mptex
    vt
    cT
    @24
    cvv
    cF
    fmuldfeqlem1.6
    fvmpt2
    mpan2
    vi
    vj
    @19
    @23
    @18
    @21
    @16
    wceq
    @0
    @22
    @17
    @21
    @16
    cU
    fveq2
    fveq1d
    cbvmptv
    syl6eq
    adantl
    @16
    @6
    wceq
    #
    @18
    @10
    wceq
    @2
    @25
    @0
    @17
    @9
    @16
    @6
    cU
    fveq2
    fveq1d
    adantl
    wph
    @6
    @19
    wcel
    @1
    fmuldfeqlem1.11
    adantr
    wph
    cT
    cr
    @0
    @9
    wph
    @9
    cY
    wcel
    #
    wph
    @26
    wa
    #
    cT
    cr
    @9
    wf
    #
    wph
    @19
    cY
    @6
    cU
    fmuldfeqlem1.8
    fmuldfeqlem1.11
    ffvelrnd
    #
    wph
    @26
    @29
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
    @30
    wf
    #
    wi
    #
    @27
    @28
    wi
    vf
    @9
    cY
    vf
    @9
    nfcv
    @27
    @28
    vf
    wph
    @26
    vf
    fmuldfeqlem1.1
    @26
    vf
    nfv
    nfan
    @28
    vf
    nfv
    nfim
    @30
    @9
    wceq
    #
    @32
    @27
    @33
    @28
    @35
    @31
    @26
    wph
    @30
    @9
    cY
    eleq1
    anbi2d
    cT
    cr
    @30
    @9
    feq1
    imbi12d
    fmuldfeqlem1.13
    vtoclgf
    sylc
    ffvelrnda
    #
    fvmptd
    oveq2d
    wph
    @12
    @8
    wceq
    #
    @1
    wph
    cN
    c1
    cuz
    cfv
    wcel
    #
    @37
    wph
    cN
    @19
    wcel
    @38
    fmuldfeqlem1.10
    cN
    c1
    cM
    elfzuz
    syl
    #
    cmul
    @3
    c1
    cN
    seqp1
    syl
    adantr
    @2
    @15
    @0
    cN
    @13
    cfv
    #
    cfv
    #
    @10
    cmul
    co
    #
    @11
    wph
    vt
    cT
    @42
    @14
    cr
    wph
    @14
    @40
    @9
    cP
    co
    #
    vt
    cT
    @42
    cmpt
    #
    wph
    @38
    @14
    @43
    wceq
    @39
    cP
    cU
    c1
    cN
    seqp1
    syl
    wph
    vh
    vl
    @40
    @9
    cY
    cY
    vt
    cT
    @0
    vh
    cv
    #
    cfv
    #
    @0
    vl
    cv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @44
    cP
    cvv
    cP
    vh
    vl
    cY
    cY
    @50
    cmpt2
    #
    wceq
    wph
    cP
    vf
    vg
    cY
    cY
    vt
    cT
    @0
    @30
    cfv
    #
    @0
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
    cmpt2
    #
    @51
    fmuldfeqlem1.5
    vf
    vg
    vh
    vl
    cY
    cY
    @56
    @50
    vh
    @56
    nfcv
    vl
    @56
    nfcv
    vf
    @50
    nfcv
    vg
    @50
    nfcv
    @30
    @45
    wceq
    #
    @53
    @47
    wceq
    #
    wa
    vt
    cT
    @55
    @49
    @58
    @59
    @52
    @46
    @54
    @48
    cmul
    @0
    @30
    @45
    fveq1
    #
    @0
    @53
    @47
    fveq1
    #
    oveqan12d
    mpteq2dv
    cbvmpt2
    eqtri
    #
    a1i
    @45
    @40
    wceq
    #
    @47
    @9
    wceq
    #
    wa
    #
    @50
    @44
    wceq
    wph
    @65
    vt
    cT
    @49
    @42
    @63
    @64
    vt
    vt
    @45
    @40
    vt
    cN
    @13
    vt
    cP
    cU
    c1
    vt
    c1
    nfcv
    vt
    cP
    @57
    fmuldfeqlem1.5
    vf
    vg
    vt
    cY
    cY
    @56
    fmuldfeqlem1.3
    fmuldfeqlem1.3
    vt
    cT
    @55
    nfmpt1
    nfmpt2
    nfcxfr
    vt
    cU
    nfcv
    nfseq
    vt
    cN
    nfcv
    nffv
    nfeq2
    @64
    vt
    nfv
    nfan
    @65
    @1
    wa
    @46
    @41
    @48
    @10
    cmul
    @63
    @46
    @41
    wceq
    @64
    @1
    @0
    @45
    @40
    fveq1
    ad2antrr
    @64
    @48
    @10
    wceq
    @63
    @1
    @0
    @47
    @9
    fveq1
    ad2antlr
    oveq12d
    mpteq2da
    adantl
    wph
    vt
    cP
    cT
    cU
    vh
    vl
    cM
    cN
    @40
    cY
    @62
    @40
    eqid
    fmuldfeqlem1.10
    fmuldfeqlem1.8
    @45
    cY
    wcel
    #
    @47
    cY
    wcel
    #
    wa
    wph
    @66
    @67
    w3a
    #
    @50
    cY
    wcel
    #
    wph
    @66
    @67
    3simpc
    wph
    @31
    @53
    cY
    wcel
    #
    w3a
    #
    @56
    cY
    wcel
    #
    wi
    wph
    @66
    @70
    w3a
    #
    vt
    cT
    @46
    @54
    cmul
    co
    #
    cmpt
    #
    cY
    wcel
    #
    wi
    @68
    @69
    wi
    vf
    vg
    @45
    @47
    cY
    cY
    vf
    @45
    nfcv
    vg
    @45
    nfcv
    vg
    @47
    nfcv
    @73
    @76
    vf
    wph
    @66
    @70
    vf
    fmuldfeqlem1.1
    @66
    vf
    nfv
    @70
    vf
    nfv
    nf3an
    @76
    vf
    nfv
    nfim
    @68
    @69
    vg
    wph
    @66
    @67
    vg
    fmuldfeqlem1.2
    @66
    vg
    nfv
    @67
    vg
    nfv
    nf3an
    @69
    vg
    nfv
    nfim
    @58
    @71
    @73
    @72
    @76
    @58
    @31
    @66
    wph
    @70
    @30
    @45
    cY
    eleq1
    3anbi2d
    @58
    @56
    @75
    cY
    @58
    vt
    cT
    @55
    @74
    @58
    @52
    @46
    @54
    cmul
    @60
    oveq1d
    mpteq2dv
    eleq1d
    imbi12d
    @59
    @73
    @68
    @76
    @69
    @59
    @70
    @67
    wph
    @66
    @53
    @47
    cY
    eleq1
    3anbi3d
    @59
    @75
    @50
    cY
    @59
    vt
    cT
    @74
    @49
    @59
    @54
    @48
    @46
    cmul
    @61
    oveq2d
    mpteq2dv
    eleq1d
    imbi12d
    fmuldfeqlem1.9
    vtocl2gf
    mpcom
    fmuldfeqlem1.7
    fmulcl
    #
    @29
    wph
    cT
    cvv
    wcel
    @44
    cvv
    wcel
    fmuldfeqlem1.7
    vt
    cT
    @42
    cvv
    mptexg
    syl
    ovmpt2d
    eqtrd
    @2
    @41
    @10
    wph
    cT
    cr
    @0
    @40
    wph
    @40
    cY
    wcel
    #
    wph
    @78
    wa
    #
    cT
    cr
    @40
    wf
    #
    @77
    wph
    @78
    @77
    ancli
    @34
    @79
    @80
    wi
    vf
    @40
    cY
    vf
    cN
    @13
    vf
    cP
    cU
    c1
    vf
    c1
    nfcv
    vf
    cP
    @57
    fmuldfeqlem1.5
    vf
    vg
    cY
    cY
    @56
    nfmpt21
    nfcxfr
    vf
    cU
    nfcv
    nfseq
    vf
    cN
    nfcv
    nffv
    #
    @79
    @80
    vf
    wph
    @78
    vf
    fmuldfeqlem1.1
    vf
    @40
    cY
    @81
    nfel1
    nfan
    vf
    cT
    cr
    @40
    @81
    vf
    cT
    nfcv
    vf
    cr
    nfcv
    nff
    nfim
    @30
    @40
    wceq
    #
    @32
    @79
    @33
    @80
    @82
    @31
    @78
    wph
    @30
    @40
    cY
    eleq1
    anbi2d
    cT
    cr
    @30
    @40
    feq1
    imbi12d
    fmuldfeqlem1.13
    vtoclgf
    sylc
    ffvelrnda
    @36
    remulcld
    fvmpt2d
    wph
    @42
    @11
    wceq
    @1
    wph
    @41
    @5
    @10
    cmul
    fmuldfeqlem1.12
    oveq1d
    adantr
    eqtrd
    3eqtr4rd
end
