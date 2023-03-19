include "cn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "ccnv.mm"
include "cres.mm"
include "wfun.mm"
include "w3a.mm"
include "cfv.mm"
include "cesum.mm"
include "cuni.mm"
include "cle.mm"
include "wbr.mm"
include "com.mm"
include "cdom.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wex.mm"
include "0ex.mm"
include "a1i.mm"
include "padct.mm"
include "syl3anc.mm"
include "wa.mm"
include "cmpt.mm"
include "nfv.mm"
include "simpr1.mm"
include "feqmptd.mm"
include "rneqd.mm"
include "esumeq1d.mm"
include "wceq.mm"
include "ccarsg.mm"
include "fvex.mm"
include "adantr.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "0elcarsg.mm"
include "snssd.mm"
include "unssd.mm"
include "ssexd.mm"
include "carsgcl.mm"
include "sstrd.mm"
include "0elpw.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "frn.mm"
include "syl.mm"
include "esummono.mm"
include "ctex.mm"
include "elsni.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "esumpad.mm"
include "breqtrd.mm"
include "ssexg.mm"
include "sylancl.mm"
include "simpr2.mm"
include "jca.mm"
include "cxr.mm"
include "wb.mm"
include "iccssxr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "xrletri3.mm"
include "mpbird.mm"
include "fveq2.mm"
include "nnex.mm"
include "simpr.mm"
include "sseldd.mm"
include "ad2antrr.mm"
include "cima.mm"
include "cdif.mm"
include "wdisj.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "ffun.mm"
include "difpreima.mm"
include "3syl.mm"
include "fimacnv.mm"
include "difeq1d.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtr3i.mm"
include "difss.mm"
include "eqsstri.mm"
include "sspreima.mm"
include "eqsstr3d.mm"
include "fvimacnvi.mm"
include "wf1o.mm"
include "simpr3.mm"
include "fresf1o.mm"
include "disjrdx.mm"
include "fvres.mm"
include "disjeq2dv.mm"
include "bitr3d.mm"
include "mpbid.mm"
include "disjss3.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "esumrnmpt2.mm"
include "3eqtr3rd.mm"
include "ciun.mm"
include "uniiun.mm"
include "elpwiuncl.mm"
include "syl5eqel.mm"
include "c1.mm"
include "cfz.mm"
include "cin.mm"
include "3adant1r.mm"
include "cbvesum.mm"
include "syl6breq.mm"
include "wfn.mm"
include "cfn.mm"
include "ffn.mm"
include "fz1ssnn.mm"
include "fnssres.mm"
include "mpan2.mm"
include "fzfi.mm"
include "fnfi.mm"
include "rnfi.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "id.mm"
include "cbvdisj.mm"
include "disjun0.mm"
include "sylbi.mm"
include "disjss1.mm"
include "sylc.mm"
include "pwidg.mm"
include "carsgclctunlem1.mm"
include "unissd.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "syl6sseq.mm"
include "uniss.mm"
include "unipw.mm"
include "sseqin2.mm"
include "sylib.mm"
include "elpwid.mm"
include "esumeq2d.mm"
include "reseq1d.mm"
include "resmpt.mm"
include "syl6eq.mm"
include "eqcomd.mm"
include "adantlr.mm"
include "syldan.mm"
include "ad3antrrr.mm"
include "wi.mm"
include "3eqtr2d.mm"
include "3eqtr3d.mm"
include "carsgmon.mm"
include "eqbrtrrd.mm"
include "esumgect.mm"
include "exlimddv.mm"

theorem carsggect
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cM: class M
  let cO: class O
  let cV: class V
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let vb: setvar b
  let cE: class E
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume carsggect.0: |- ( ph -> -. (/) e. A )
  assume carsggect.1: |- ( ph -> A ~<_ _om )
  assume carsggect.2: |- ( ph -> A C_ ( toCaraSiga ` M ) )
  assume carsggect.3: |- ( ph -> Disj_ y e. A y )
  assume carsggect.4: |- ( ( ph /\ x C_ y /\ y e. ~P O ) -> ( M ` x ) <_ ( M ` y ) )

  disjoint A z
  disjoint M z
  disjoint O z
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint A f
  disjoint A k
  disjoint A n
  disjoint f k
  disjoint f n
  disjoint f z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint M f
  disjoint M k
  disjoint M n
  disjoint O f
  disjoint O k
  disjoint k x
  disjoint k y
  disjoint k ph
  disjoint n x
  disjoint n y
  disjoint n ph
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint E x
  disjoint E y
  disjoint M b
  disjoint M f
  disjoint O f
  disjoint b ph
  disjoint f ph
  assert |- ( ph -> sum* z e. A ( M ` z ) <_ ( M ` U. A ) )

  proof
    wph
    cn
    cA
    c0
    csn
    #
    cun
    #
    vf
    cv
    #
    wf
    #
    cA
    @2
    crn
    #
    wss
    #
    @2
    ccnv
    #
    cA
    cres
    wfun
    #
    w3a
    #
    cA
    vz
    cv
    #
    cM
    cfv
    #
    vz
    cesum
    #
    cA
    cuni
    #
    cM
    cfv
    #
    cle
    wbr
    vf
    wph
    cA
    com
    cdom
    wbr
    #
    c0
    cvv
    wcel
    #
    c0
    cA
    wcel
    wn
    @8
    vf
    wex
    carsggect.1
    @15
    wph
    0ex
    a1i
    carsggect.0
    cA
    vf
    cvv
    c0
    padct
    syl3anc
    wph
    @8
    wa
    #
    cn
    vk
    cv
    #
    @2
    cfv
    #
    cM
    cfv
    #
    vk
    cesum
    #
    @11
    @13
    cle
    @16
    @4
    @10
    vz
    cesum
    #
    vk
    cn
    @18
    cmpt
    #
    crn
    #
    @10
    vz
    cesum
    @11
    @20
    @16
    @4
    @23
    @10
    vz
    @16
    vz
    nfv
    #
    @16
    @2
    @22
    @16
    vk
    cn
    @1
    @2
    wph
    @3
    @5
    @7
    simpr1
    #
    feqmptd
    #
    rneqd
    esumeq1d
    @16
    @21
    @11
    wceq
    #
    @21
    @11
    cle
    wbr
    #
    @11
    @21
    cle
    wbr
    #
    wa
    #
    @16
    @28
    @29
    @16
    @21
    @1
    @10
    vz
    cesum
    @11
    cle
    @16
    @4
    @10
    @1
    vz
    cvv
    @24
    @16
    @1
    cM
    ccarsg
    cfv
    #
    cvv
    @31
    cvv
    wcel
    #
    @16
    cM
    ccarsg
    fvex
    #
    a1i
    #
    @16
    cA
    @0
    @31
    wph
    cA
    @31
    wss
    @8
    carsggect.2
    adantr
    @16
    c0
    @31
    @16
    cM
    cO
    cV
    wph
    cO
    cV
    wcel
    #
    @8
    carsgval.1
    adantr
    #
    wph
    cO
    cpw
    #
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    #
    @8
    carsgval.2
    adantr
    #
    wph
    c0
    cM
    cfv
    #
    cc0
    wceq
    #
    @8
    carsgsiga.1
    adantr
    #
    0elcarsg
    snssd
    #
    unssd
    #
    ssexd
    @16
    @9
    @1
    wcel
    #
    wa
    @37
    @38
    @9
    cM
    @16
    @39
    @46
    @40
    adantr
    @16
    @1
    @37
    @9
    @16
    cA
    @0
    @37
    wph
    cA
    @37
    wss
    #
    @8
    wph
    cA
    @31
    @37
    carsggect.2
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgcl
    sstrd
    #
    adantr
    #
    @16
    c0
    @37
    c0
    @37
    wcel
    #
    @16
    cO
    0elpw
    #
    a1i
    snssd
    unssd
    #
    sselda
    ffvelrnd
    @16
    @3
    @4
    @1
    wss
    @25
    cn
    @1
    @2
    frn
    syl
    #
    esummono
    @16
    cA
    @0
    @10
    vz
    cvv
    cvv
    wph
    cA
    cvv
    wcel
    #
    @8
    wph
    @14
    @54
    carsggect.1
    cA
    ctex
    syl
    #
    adantr
    #
    @16
    @0
    @31
    cvv
    @34
    @44
    ssexd
    @16
    @9
    cA
    wcel
    #
    wa
    @37
    @38
    @9
    cM
    @16
    @39
    @57
    @40
    adantr
    @16
    cA
    @37
    @9
    @49
    sselda
    ffvelrnd
    #
    @16
    @9
    @0
    wcel
    #
    wa
    #
    @10
    @41
    cc0
    @60
    @9
    c0
    cM
    @59
    @9
    c0
    wceq
    @16
    @9
    c0
    elsni
    adantl
    fveq2d
    @16
    @42
    @59
    @43
    adantr
    eqtrd
    esumpad
    breqtrd
    @16
    cA
    @10
    @4
    vz
    cvv
    @24
    @16
    @4
    @31
    wss
    @32
    @4
    cvv
    wcel
    #
    @16
    @4
    @1
    @31
    @53
    @45
    sstrd
    #
    @33
    @4
    @31
    cvv
    ssexg
    sylancl
    #
    @16
    @9
    @4
    wcel
    #
    wa
    @37
    @38
    @9
    cM
    @16
    @39
    @64
    @40
    adantr
    @16
    @4
    @37
    @9
    @16
    @4
    @1
    @37
    @53
    @52
    sstrd
    sselda
    ffvelrnd
    #
    wph
    @3
    @5
    @7
    simpr2
    #
    esummono
    jca
    @16
    @21
    cxr
    wcel
    @11
    cxr
    wcel
    @27
    @30
    wb
    @16
    @38
    cxr
    @21
    cc0
    cpnf
    iccssxr
    #
    @16
    @61
    @10
    @38
    wcel
    #
    vz
    @4
    wral
    @21
    @38
    wcel
    @63
    @16
    @68
    vz
    @4
    @65
    ralrimiva
    @4
    @10
    vz
    cvv
    vz
    @4
    nfcv
    esumcl
    syl2anc
    sseldi
    @16
    @38
    cxr
    @11
    @67
    @16
    @54
    @68
    vz
    cA
    wral
    @11
    @38
    wcel
    @56
    @16
    @68
    vz
    cA
    @58
    ralrimiva
    cA
    @10
    vz
    cvv
    vz
    cA
    nfcv
    esumcl
    syl2anc
    sseldi
    @21
    @11
    xrletri3
    syl2anc
    mpbird
    @16
    vz
    cn
    @18
    @10
    @19
    vk
    cvv
    @37
    @9
    @18
    cM
    fveq2
    #
    cn
    cvv
    wcel
    @16
    nnex
    a1i
    @16
    @17
    cn
    wcel
    #
    wa
    #
    @37
    @38
    @18
    cM
    @16
    @39
    @70
    @40
    adantr
    @71
    @1
    @37
    @18
    @16
    @1
    @37
    wss
    @70
    @52
    adantr
    @71
    cn
    @1
    @17
    @2
    @16
    @3
    @70
    @25
    adantr
    @16
    @70
    simpr
    ffvelrnd
    sseldd
    #
    ffvelrnd
    #
    @72
    @71
    @18
    c0
    wceq
    #
    wa
    #
    @19
    @41
    cc0
    @75
    @18
    c0
    cM
    @71
    @74
    simpr
    fveq2d
    @16
    @42
    @70
    @74
    @43
    ad2antrr
    eqtrd
    @16
    @6
    cA
    cima
    #
    cn
    wss
    #
    @74
    vk
    cn
    @76
    cdif
    #
    wral
    #
    vk
    @76
    @18
    wdisj
    #
    vk
    cn
    @18
    wdisj
    #
    @16
    @76
    @2
    cdm
    #
    cn
    @76
    @82
    wss
    @16
    @2
    cA
    cnvimass
    a1i
    @16
    @3
    @82
    cn
    wceq
    @25
    cn
    @1
    @2
    fdm
    syl
    sseqtrd
    @16
    @74
    vk
    @78
    @16
    @17
    @78
    wcel
    #
    wa
    #
    @18
    @0
    wcel
    #
    @74
    @84
    @2
    wfun
    #
    @17
    @6
    @0
    cima
    #
    wcel
    @85
    @16
    @86
    @83
    @16
    @3
    @86
    @25
    cn
    @1
    @2
    ffun
    #
    syl
    #
    adantr
    @16
    @78
    @87
    @17
    @16
    @78
    @6
    @1
    cA
    cdif
    #
    cima
    #
    @87
    @16
    @91
    @6
    @1
    cima
    #
    @76
    cdif
    #
    @78
    @16
    @3
    @86
    @91
    @93
    wceq
    @25
    @88
    @1
    cA
    @2
    difpreima
    3syl
    @16
    @92
    cn
    @76
    @16
    @3
    @92
    cn
    wceq
    @25
    cn
    @1
    @2
    fimacnv
    syl
    difeq1d
    eqtrd
    @16
    @86
    @90
    @0
    wss
    #
    @91
    @87
    wss
    @89
    @94
    @16
    @90
    @0
    cA
    cdif
    #
    @0
    @0
    cA
    cun
    #
    cA
    cdif
    @90
    @95
    @96
    @1
    cA
    @0
    cA
    uncom
    difeq1i
    @0
    cA
    difun2
    eqtr3i
    @0
    cA
    difss
    eqsstri
    a1i
    @90
    @0
    @2
    sspreima
    syl2anc
    eqsstr3d
    sselda
    @17
    @0
    @2
    fvimacnvi
    syl2anc
    @18
    c0
    elsni
    syl
    ralrimiva
    @16
    vy
    cA
    vy
    cv
    #
    wdisj
    #
    @80
    wph
    @98
    @8
    carsggect.3
    adantr
    @16
    vk
    @76
    @17
    @2
    @76
    cres
    #
    cfv
    #
    wdisj
    @98
    @80
    @16
    vk
    vy
    @76
    @100
    cA
    @97
    @99
    @16
    @86
    @5
    @7
    @76
    cA
    @99
    wf1o
    @89
    @66
    wph
    @3
    @5
    @7
    simpr3
    cA
    @2
    fresf1o
    syl3anc
    @16
    @97
    @100
    wceq
    simpr
    disjrdx
    @16
    vk
    @76
    @100
    @18
    @17
    @76
    wcel
    @100
    @18
    wceq
    @16
    @17
    @76
    @2
    fvres
    adantl
    disjeq2dv
    bitr3d
    mpbid
    @77
    @79
    wa
    @80
    @81
    vk
    @76
    cn
    @18
    disjss3
    biimpa
    syl21anc
    #
    esumrnmpt2
    3eqtr3rd
    @16
    @19
    @13
    vk
    vn
    @16
    @37
    @38
    @12
    cM
    @40
    wph
    @12
    @37
    wcel
    @8
    wph
    @12
    vx
    cA
    vx
    cv
    #
    ciun
    @37
    vx
    cA
    uniiun
    wph
    cA
    @102
    cO
    vx
    cvv
    @55
    wph
    cA
    @37
    @102
    @48
    sselda
    elpwiuncl
    syl5eqel
    adantr
    #
    ffvelrnd
    @73
    @16
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    @2
    c1
    @104
    cfz
    co
    #
    cres
    #
    crn
    #
    cuni
    #
    cM
    cfv
    #
    @107
    @19
    vk
    cesum
    #
    @13
    cle
    @106
    cO
    @110
    cin
    #
    cM
    cfv
    #
    @109
    cO
    @9
    cin
    #
    cM
    cfv
    #
    vz
    cesum
    #
    @111
    @112
    @16
    @114
    @117
    wceq
    @105
    @16
    vx
    vz
    @109
    cO
    cM
    cO
    cV
    @36
    @40
    @43
    @16
    @102
    com
    cdom
    wbr
    #
    @102
    @37
    wss
    #
    w3a
    @102
    cuni
    cM
    cfv
    #
    @102
    @97
    cM
    cfv
    #
    vy
    cesum
    #
    @102
    @10
    vz
    cesum
    cle
    wph
    @118
    @119
    @120
    @122
    cle
    wbr
    @8
    carsgsiga.2
    3adant1r
    @102
    @121
    @10
    vy
    vz
    @97
    @9
    cM
    fveq2
    vz
    @102
    nfcv
    vy
    @102
    nfcv
    vz
    @121
    nfcv
    vy
    @10
    nfcv
    cbvesum
    syl6breq
    @16
    @108
    @107
    wfn
    #
    @108
    cfn
    wcel
    #
    @109
    cfn
    wcel
    @16
    @3
    @2
    cn
    wfn
    #
    @123
    @25
    cn
    @1
    @2
    ffn
    @125
    @107
    cn
    wss
    #
    @123
    @104
    fz1ssnn
    #
    cn
    @107
    @2
    fnssres
    mpan2
    3syl
    @123
    @107
    cfn
    wcel
    #
    @124
    c1
    @104
    fzfi
    #
    @107
    @108
    fnfi
    mpan2
    @108
    rnfi
    3syl
    @16
    @109
    @4
    @31
    @109
    @4
    wss
    #
    @16
    @108
    @2
    wss
    @130
    @2
    @107
    resss
    @108
    @2
    rnss
    ax-mp
    a1i
    #
    @62
    sstrd
    @16
    @109
    @1
    wss
    #
    vz
    @1
    @9
    wdisj
    #
    vz
    @109
    @9
    wdisj
    @16
    @109
    @4
    @1
    @131
    @53
    sstrd
    #
    wph
    @133
    @8
    wph
    @98
    @133
    carsggect.3
    @98
    vz
    cA
    @9
    wdisj
    @133
    vy
    vz
    cA
    @97
    @9
    vz
    @97
    nfcv
    vy
    @9
    nfcv
    @97
    @9
    wceq
    id
    cbvdisj
    vz
    cA
    disjun0
    sylbi
    syl
    adantr
    vz
    @109
    @1
    @9
    disjss1
    sylc
    @16
    @35
    cO
    @37
    wcel
    @36
    cO
    cV
    pwidg
    syl
    carsgclctunlem1
    adantr
    @106
    @113
    @110
    cM
    @106
    @110
    cO
    wss
    @113
    @110
    wceq
    @106
    @110
    @12
    cO
    @16
    @110
    @12
    wss
    @105
    @16
    @110
    @1
    cuni
    #
    @12
    @16
    @109
    @1
    @134
    unissd
    @135
    @12
    @0
    cuni
    #
    cun
    @12
    c0
    cun
    @12
    cA
    @0
    uniun
    @136
    c0
    @12
    c0
    0ex
    unisn
    uneq2i
    @12
    un0
    3eqtri
    syl6sseq
    #
    adantr
    wph
    @12
    cO
    wss
    #
    @8
    @105
    wph
    @47
    @138
    @48
    @47
    @12
    @37
    cuni
    cO
    cA
    @37
    uniss
    cO
    unipw
    syl6sseq
    syl
    ad2antrr
    sstrd
    @110
    cO
    sseqin2
    sylib
    fveq2d
    @106
    @117
    @109
    @10
    vz
    cesum
    vk
    @107
    @18
    cmpt
    #
    crn
    #
    @10
    vz
    cesum
    @112
    @106
    @109
    @116
    @10
    vz
    @106
    vz
    nfv
    #
    @106
    @116
    @10
    wceq
    vz
    @109
    @106
    @9
    @109
    wcel
    wa
    #
    @115
    @9
    cM
    @142
    @9
    cO
    wss
    @115
    @9
    wceq
    @142
    @9
    cO
    @106
    @109
    @37
    @9
    @106
    @109
    @1
    @37
    @16
    @132
    @105
    @134
    adantr
    @106
    cA
    @0
    @37
    wph
    @47
    @8
    @105
    @48
    ad2antrr
    @106
    c0
    @37
    @50
    @106
    @51
    a1i
    snssd
    unssd
    sstrd
    sselda
    elpwid
    @9
    cO
    sseqin2
    sylib
    fveq2d
    ralrimiva
    esumeq2d
    @106
    @140
    @109
    @10
    vz
    @141
    @106
    @139
    @108
    @106
    @108
    @139
    @106
    @108
    @22
    @107
    cres
    #
    @139
    @16
    @108
    @143
    wceq
    @105
    @16
    @2
    @22
    @107
    @26
    reseq1d
    adantr
    @126
    @143
    @139
    wceq
    @127
    vk
    cn
    @107
    @18
    resmpt
    ax-mp
    syl6eq
    eqcomd
    rneqd
    esumeq1d
    @106
    vz
    @107
    @18
    @10
    @19
    vk
    cfn
    @37
    @69
    @128
    @106
    @129
    a1i
    @106
    @17
    @107
    wcel
    #
    wa
    #
    @37
    @38
    @18
    cM
    @16
    @39
    @105
    @144
    @40
    ad2antrr
    @106
    @144
    @70
    @18
    @37
    wcel
    #
    @106
    @107
    cn
    @17
    @126
    @106
    @127
    a1i
    sselda
    @16
    @70
    @146
    @105
    @72
    adantlr
    syldan
    #
    ffvelrnd
    @147
    @145
    @74
    wa
    #
    @19
    @41
    cc0
    @148
    @18
    c0
    cM
    @145
    @74
    simpr
    fveq2d
    @16
    @42
    @105
    @144
    @74
    @43
    ad3antrrr
    eqtrd
    @16
    vk
    @107
    @18
    wdisj
    #
    @105
    @16
    @81
    @149
    @101
    @126
    @81
    @149
    wi
    @127
    vk
    @107
    cn
    @18
    disjss1
    ax-mp
    syl
    adantr
    esumrnmpt2
    3eqtr2d
    3eqtr3d
    @16
    @111
    @13
    cle
    wbr
    @105
    @16
    vx
    vy
    @110
    @12
    cM
    cO
    cV
    @36
    @40
    @137
    @103
    wph
    @102
    @97
    wss
    @97
    @37
    wcel
    @102
    cM
    cfv
    @121
    cle
    wbr
    @8
    carsggect.4
    3adant1r
    carsgmon
    adantr
    eqbrtrrd
    esumgect
    eqbrtrrd
    exlimddv
end
