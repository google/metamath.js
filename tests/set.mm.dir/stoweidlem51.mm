include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "w3a.mm"
include "wex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cz.mm"
include "cfz.mm"
include "1zzd.mm"
include "nnzd.mm"
include "3jca.mm"
include "nnge1d.mm"
include "nnred.mm"
include "leidd.mm"
include "jca.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "cmul.mm"
include "cmpt.mm"
include "eqid.mm"
include "stoweidlem16.mm"
include "fmulcl.mm"
include "sseldi.mm"
include "eleq2i.mm"
include "cseq.mm"
include "nfcv.mm"
include "cmpt2.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfmpt2.mm"
include "nfseq.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfral.mm"
include "wceq.mm"
include "nfra1.mm"
include "nfrab.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "elrabf.mm"
include "bitri.mm"
include "sylib.mm"
include "simprd.mm"
include "nfv.mm"
include "cdiv.mm"
include "cr.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "simplbi.mm"
include "syl.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "feq1.mm"
include "imbi12d.mm"
include "a1i.mm"
include "vtoclga.mm"
include "anabsi7.mm"
include "syldan.mm"
include "adantr.mm"
include "wss.mm"
include "simpl.mm"
include "nfel2.mm"
include "nfim.mm"
include "sseq1.mm"
include "vtoclg1f.mm"
include "sylc.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "rpred.mm"
include "ad2antrr.mm"
include "wne.mm"
include "nnne0d.mm"
include "redivcld.mm"
include "r19.21bi.mm"
include "wb.mm"
include "1red.mm"
include "0lt1.mm"
include "nngt0d.mm"
include "rpregt0d.mm"
include "lediv2.mm"
include "syl221anc.mm"
include "mpbid.mm"
include "rpcnd.mm"
include "div1d.mm"
include "breqtrd.mm"
include "ltletrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "stoweidlem48.mm"
include "sseli.mm"
include "sylan2.mm"
include "stoweidlem42.mm"
include "3anbi123d.mm"
include "spcegv.mm"

theorem stoweidlem51
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
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
  let vk: setvar k
  assume stoweidlem51.1: |- F/ i ph
  assume stoweidlem51.2: |- F/ t ph
  assume stoweidlem51.3: |- F/ w ph
  assume stoweidlem51.4: |- F/_ w V
  assume stoweidlem51.5: |- Y = { h e. A | A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) }
  assume stoweidlem51.6: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume stoweidlem51.7: |- X = ( seq 1 ( P , U ) ` M )
  assume stoweidlem51.8: |- F = ( t e. T |-> ( i e. ( 1 ... M ) |-> ( ( U ` i ) ` t ) ) )
  assume stoweidlem51.9: |- Z = ( t e. T |-> ( seq 1 ( x. , ( F ` t ) ) ` M ) )
  assume stoweidlem51.10: |- ( ph -> M e. NN )
  assume stoweidlem51.11: |- ( ph -> W : ( 1 ... M ) --> V )
  assume stoweidlem51.12: |- ( ph -> U : ( 1 ... M ) --> Y )
  assume stoweidlem51.13: |- ( ( ph /\ w e. V ) -> w C_ T )
  assume stoweidlem51.14: |- ( ph -> D C_ U. ran W )
  assume stoweidlem51.15: |- ( ph -> D C_ T )
  assume stoweidlem51.16: |- ( ph -> B C_ T )
  assume stoweidlem51.17: |- ( ( ph /\ i e. ( 1 ... M ) ) -> A. t e. ( W ` i ) ( ( U ` i ) ` t ) < ( E / M ) )
  assume stoweidlem51.18: |- ( ( ph /\ i e. ( 1 ... M ) ) -> A. t e. B ( 1 - ( E / M ) ) < ( ( U ` i ) ` t ) )
  assume stoweidlem51.19: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem51.20: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem51.21: |- ( ph -> T e. _V )
  assume stoweidlem51.22: |- ( ph -> E e. RR+ )
  assume stoweidlem51.23: |- ( ph -> E < ( 1 / 3 ) )

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
  disjoint M f
  disjoint h i
  disjoint M h
  disjoint i t
  disjoint M i
  disjoint M t
  disjoint F f
  disjoint F g
  disjoint T f
  disjoint T g
  disjoint T h
  disjoint T t
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U t
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint M g
  disjoint i w
  disjoint T i
  disjoint T w
  disjoint B i
  disjoint D i
  disjoint E i
  disjoint U i
  disjoint W i
  disjoint W w
  disjoint t x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint T x
  disjoint X x
  disjoint k x
  assert |- ( ph -> E. x ( x e. A /\ ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. D ( x ` t ) < E /\ A. t e. B ( 1 - E ) < ( x ` t ) ) ) )

  proof
    wph
    cX
    cA
    wcel
    #
    @0
    cc0
    vt
    cv
    #
    cX
    cfv
    #
    cle
    wbr
    #
    @2
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
    @2
    cE
    clt
    wbr
    #
    vt
    cD
    wral
    #
    c1
    cE
    cmin
    co
    #
    @2
    clt
    wbr
    #
    vt
    cB
    wral
    #
    w3a
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    @1
    @14
    cfv
    #
    cle
    wbr
    #
    @16
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
    cE
    clt
    wbr
    #
    vt
    cD
    wral
    #
    @9
    @16
    clt
    wbr
    #
    vt
    cB
    wral
    #
    w3a
    #
    wa
    #
    vx
    wex
    wph
    cY
    cA
    cX
    cY
    cc0
    @1
    vh
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @28
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
    cA
    stoweidlem51.5
    @32
    vh
    cA
    ssrab2
    eqsstri
    #
    wph
    vt
    cP
    cT
    cU
    vf
    vg
    cM
    cM
    cX
    cY
    stoweidlem51.6
    stoweidlem51.7
    wph
    c1
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @36
    w3a
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
    wa
    cM
    c1
    cM
    cfz
    co
    #
    wcel
    wph
    @35
    @36
    @36
    wph
    1zzd
    wph
    cM
    stoweidlem51.10
    nnzd
    #
    @40
    3jca
    wph
    @37
    @38
    wph
    cM
    stoweidlem51.10
    nnge1d
    #
    wph
    cM
    wph
    cM
    stoweidlem51.10
    nnred
    #
    leidd
    jca
    cM
    c1
    cM
    elfz2
    sylanbrc
    stoweidlem51.12
    wph
    vt
    cA
    cT
    vf
    vg
    vh
    vt
    cT
    @1
    vf
    cv
    #
    cfv
    @1
    vg
    cv
    cfv
    cmul
    co
    #
    cmpt
    #
    cY
    stoweidlem51.2
    stoweidlem51.5
    @45
    eqid
    stoweidlem51.20
    stoweidlem51.19
    stoweidlem16
    #
    stoweidlem51.21
    fmulcl
    #
    sseldi
    #
    wph
    @0
    @12
    @48
    wph
    @6
    @8
    @11
    wph
    @0
    @6
    wph
    cX
    cY
    wcel
    #
    @0
    @6
    wa
    #
    @47
    @49
    cX
    @33
    wcel
    @50
    cY
    @33
    cX
    stoweidlem51.5
    eleq2i
    @32
    @6
    vh
    cX
    cA
    vh
    cX
    cM
    cP
    cU
    c1
    cseq
    #
    cfv
    #
    stoweidlem51.7
    vh
    cM
    @51
    vh
    cP
    cU
    c1
    vh
    c1
    nfcv
    #
    vh
    cP
    vf
    vg
    cY
    cY
    @45
    cmpt2
    #
    stoweidlem51.6
    vf
    vg
    vh
    cY
    cY
    @45
    vh
    cY
    @33
    stoweidlem51.5
    @32
    vh
    cA
    nfrab1
    nfcxfr
    #
    @55
    vh
    @45
    nfcv
    nfmpt2
    nfcxfr
    vh
    cU
    nfcv
    nfseq
    vh
    cM
    nfcv
    nffv
    nfcxfr
    #
    vh
    cA
    nfcv
    @5
    vh
    vt
    cT
    vh
    cT
    nfcv
    @3
    @4
    vh
    vh
    cc0
    @2
    cle
    vh
    cc0
    nfcv
    vh
    cle
    nfcv
    #
    vh
    @1
    cX
    @56
    vh
    @1
    nfcv
    nffv
    #
    nfbr
    vh
    @2
    c1
    cle
    @58
    @57
    @53
    nfbr
    nfan
    nfral
    @27
    cX
    wceq
    #
    @31
    @5
    vt
    cT
    vt
    @27
    cX
    vt
    cX
    @52
    stoweidlem51.7
    vt
    cM
    @51
    vt
    cP
    cU
    c1
    vt
    c1
    nfcv
    vt
    cP
    @54
    stoweidlem51.6
    vf
    vg
    vt
    cY
    cY
    @45
    vt
    cY
    @33
    stoweidlem51.5
    @32
    vt
    vh
    cA
    @31
    vt
    cT
    nfra1
    vt
    cA
    nfcv
    nfrab
    nfcxfr
    #
    @60
    vt
    cT
    @44
    nfmpt1
    nfmpt2
    nfcxfr
    vt
    cU
    nfcv
    nfseq
    vt
    cM
    nfcv
    nffv
    nfcxfr
    #
    nfeq2
    @59
    @29
    @3
    @30
    @4
    @59
    @28
    @2
    cc0
    cle
    @1
    @27
    cX
    fveq1
    #
    breq2d
    @59
    @28
    @2
    c1
    cle
    @62
    breq1d
    anbi12d
    ralbid
    elrabf
    bitri
    sylib
    simprd
    wph
    vt
    cA
    cD
    cP
    cT
    cU
    vf
    vg
    vh
    vi
    cE
    cF
    cM
    cV
    cW
    cX
    cY
    cZ
    stoweidlem51.1
    stoweidlem51.2
    stoweidlem51.5
    stoweidlem51.6
    stoweidlem51.7
    stoweidlem51.8
    stoweidlem51.9
    stoweidlem51.10
    stoweidlem51.11
    stoweidlem51.12
    stoweidlem51.14
    stoweidlem51.15
    wph
    vi
    cv
    #
    @39
    wcel
    #
    wa
    #
    @1
    @63
    cU
    cfv
    #
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    @63
    cW
    cfv
    #
    wph
    @64
    vt
    stoweidlem51.2
    @64
    vt
    nfv
    nfan
    @65
    @1
    @69
    wcel
    #
    @68
    @65
    @70
    wa
    #
    @67
    cE
    cM
    cdiv
    co
    #
    cE
    @71
    cT
    cr
    @1
    @66
    @65
    cT
    cr
    @66
    wf
    #
    @70
    wph
    @64
    @66
    cA
    wcel
    #
    @73
    @65
    @66
    cY
    wcel
    #
    @74
    wph
    @39
    cY
    @63
    cU
    stoweidlem51.12
    ffvelrnda
    @75
    @74
    cc0
    @67
    cle
    wbr
    #
    @67
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
    @32
    @79
    vh
    @66
    cA
    cY
    @27
    @66
    wceq
    #
    @31
    @78
    vt
    cT
    @80
    @29
    @76
    @30
    @77
    @80
    @28
    @67
    cc0
    cle
    @1
    @27
    @66
    fveq1
    #
    breq2d
    @80
    @28
    @67
    c1
    cle
    @81
    breq1d
    anbi12d
    ralbidv
    stoweidlem51.5
    elrab2
    simplbi
    syl
    wph
    @74
    @73
    wph
    @43
    cA
    wcel
    #
    wa
    #
    cT
    cr
    @43
    wf
    #
    wi
    #
    wph
    @74
    wa
    #
    @73
    wi
    vf
    @66
    cA
    @43
    @66
    wceq
    #
    @83
    @86
    @84
    @73
    @87
    @82
    @74
    wph
    @43
    @66
    cA
    eleq1
    anbi2d
    cT
    cr
    @43
    @66
    feq1
    imbi12d
    @85
    @82
    stoweidlem51.20
    a1i
    vtoclga
    anabsi7
    syldan
    adantr
    @65
    @69
    cT
    @1
    @65
    @69
    cV
    wcel
    #
    wph
    @88
    wa
    #
    @69
    cT
    wss
    #
    wph
    @39
    cV
    @63
    cW
    stoweidlem51.11
    ffvelrnda
    #
    @65
    wph
    @88
    wph
    @64
    simpl
    @91
    jca
    wph
    vw
    cv
    #
    cV
    wcel
    #
    wa
    #
    @92
    cT
    wss
    #
    wi
    @89
    @90
    wi
    vw
    @69
    cV
    @89
    @90
    vw
    wph
    @88
    vw
    stoweidlem51.3
    vw
    @69
    cV
    stoweidlem51.4
    nfel2
    nfan
    @90
    vw
    nfv
    nfim
    @92
    @69
    wceq
    #
    @94
    @89
    @95
    @90
    @96
    @93
    @88
    wph
    @92
    @69
    cV
    eleq1
    anbi2d
    @92
    @69
    cT
    sseq1
    imbi12d
    stoweidlem51.13
    vtoclg1f
    sylc
    sselda
    ffvelrnd
    @71
    cE
    cM
    wph
    cE
    cr
    wcel
    #
    @64
    @70
    wph
    cE
    stoweidlem51.22
    rpred
    ad2antrr
    #
    wph
    cM
    cr
    wcel
    #
    @64
    @70
    @42
    ad2antrr
    wph
    cM
    cc0
    wne
    @64
    @70
    wph
    cM
    stoweidlem51.10
    nnne0d
    ad2antrr
    redivcld
    @98
    @65
    @67
    @72
    clt
    wbr
    vt
    @69
    stoweidlem51.17
    r19.21bi
    wph
    @72
    cE
    cle
    wbr
    @64
    @70
    wph
    @72
    cE
    c1
    cdiv
    co
    #
    cE
    cle
    wph
    @37
    @72
    @100
    cle
    wbr
    #
    @41
    wph
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @99
    cc0
    cM
    clt
    wbr
    @97
    cc0
    cE
    clt
    wbr
    wa
    @37
    @101
    wb
    wph
    1red
    @102
    wph
    0lt1
    a1i
    @42
    wph
    cM
    stoweidlem51.10
    nngt0d
    wph
    cE
    stoweidlem51.22
    rpregt0d
    c1
    cM
    cE
    lediv2
    syl221anc
    mpbid
    wph
    cE
    wph
    cE
    stoweidlem51.22
    rpcnd
    div1d
    breqtrd
    ad2antrr
    ltletrd
    ex
    ralrimi
    stoweidlem51.21
    stoweidlem51.20
    stoweidlem51.19
    stoweidlem51.22
    stoweidlem48
    wph
    vt
    cB
    cP
    cT
    cU
    vf
    vg
    vi
    cE
    cF
    cM
    cX
    cY
    cZ
    stoweidlem51.1
    stoweidlem51.2
    @60
    stoweidlem51.6
    stoweidlem51.7
    stoweidlem51.8
    stoweidlem51.9
    stoweidlem51.10
    stoweidlem51.12
    stoweidlem51.18
    stoweidlem51.22
    stoweidlem51.23
    @43
    cY
    wcel
    wph
    @82
    @84
    cY
    cA
    @43
    @34
    sseli
    stoweidlem51.20
    sylan2
    @46
    stoweidlem51.21
    stoweidlem51.16
    stoweidlem42
    3jca
    jca
    @26
    @13
    vx
    cX
    cA
    @14
    cX
    wceq
    #
    @15
    @0
    @25
    @12
    @14
    cX
    cA
    eleq1
    @103
    @20
    @6
    @22
    @8
    @24
    @11
    @103
    @19
    @5
    vt
    cT
    vt
    @14
    cX
    @61
    nfeq2
    #
    @103
    @17
    @3
    @18
    @4
    @103
    @16
    @2
    cc0
    cle
    @1
    @14
    cX
    fveq1
    #
    breq2d
    @103
    @16
    @2
    c1
    cle
    @105
    breq1d
    anbi12d
    ralbid
    @103
    @21
    @7
    vt
    cD
    @104
    @103
    @16
    @2
    cE
    clt
    @105
    breq1d
    ralbid
    @103
    @23
    @10
    vt
    cB
    @104
    @103
    @16
    @2
    @9
    clt
    @105
    breq2d
    ralbid
    3anbi123d
    anbi12d
    spcegv
    sylc
end
