include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "ccom.mm"
include "cmap.mm"
include "crab.mm"
include "wa.mm"
include "cun.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wrex.mm"
include "cmzp.mm"
include "cvv.mm"
include "zex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "cfn.mm"
include "com.mm"
include "ominf.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "caddc.mm"
include "cuz.mm"
include "nnuz.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "difeq2i.mm"
include "0z.mm"
include "lzenom.mm"
include "eqbrtri.mm"
include "enfi.mm"
include "mtbir.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "eldioph4b.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "simpr.mm"
include "simp-4r.mm"
include "ovex.mm"
include "mapco2.mm"
include "syl2anc.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "elrab3.mm"
include "syl.mm"
include "simp-5r.mm"
include "simplr.mm"
include "w3a.mm"
include "coundi.mm"
include "coundir.mm"
include "elmapi.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "ssdisj.mm"
include "mp2an.mm"
include "a1i.mm"
include "coeq0i.mm"
include "syl3anc.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "un0.mm"
include "syl6eq.mm"
include "3ad2ant2.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp3an23.mm"
include "coires1.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "uneq12d.mm"
include "uncom.mm"
include "syl5req.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "reseq2i.mm"
include "res0.mm"
include "elmapresaun.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "mp3an3.mm"
include "sseldi.mm"
include "adantll.mm"
include "coeq1.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "simplll.mm"
include "unex.mm"
include "id.mm"
include "fun.mm"
include "syl21anc.mm"
include "feq1i.mm"
include "sylib.mm"
include "ad3antlr.mm"
include "mzprename.mm"
include "eldioph4i.mm"
include "eqeltrd.mm"
include "eleq2.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "impcom.mm"
include "3impb.mm"

theorem diophren
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e

  disjoint S a
  disjoint M a
  disjoint N a
  disjoint F a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint M b
  disjoint M c
  disjoint M d
  disjoint M e
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  assert |- ( ( S e. ( Dioph ` N ) /\ M e. NN0 /\ F : ( 1 ... N ) --> ( 1 ... M ) ) -> { a e. ( NN0 ^m ( 1 ... M ) ) | ( a o. F ) e. S } e. ( Dioph ` M ) )

  proof
    cS
    cN
    cdioph
    cfv
    wcel
    #
    cM
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    c1
    cM
    cfz
    co
    #
    cF
    wf
    #
    va
    cv
    #
    cF
    ccom
    #
    cS
    wcel
    #
    va
    cn0
    @3
    cmap
    co
    #
    crab
    #
    cM
    cdioph
    cfv
    #
    wcel
    #
    @1
    @4
    wa
    #
    @0
    @11
    @0
    cN
    cn0
    wcel
    #
    cS
    vc
    cv
    #
    vd
    cv
    #
    cun
    #
    vb
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vd
    cn0
    cz
    cn
    cdif
    #
    cmap
    co
    #
    wrex
    #
    vc
    cn0
    @2
    cmap
    co
    #
    crab
    #
    wceq
    #
    vb
    @20
    @2
    cun
    #
    cmzp
    cfv
    #
    wrex
    #
    wa
    @12
    @11
    vd
    vc
    cS
    cN
    @20
    vb
    cz
    cvv
    wcel
    #
    @20
    cvv
    wcel
    zex
    cz
    cn
    cvv
    difexg
    ax-mp
    #
    @20
    cfn
    wcel
    #
    com
    cfn
    wcel
    #
    ominf
    @20
    com
    cen
    wbr
    @31
    @32
    wb
    @20
    cz
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cdif
    #
    com
    cen
    cn
    @34
    cz
    cn
    c1
    cuz
    cfv
    @34
    nnuz
    @33
    c1
    cuz
    0p1e1
    fveq2i
    eqtr4i
    difeq2i
    cc0
    cz
    wcel
    @35
    com
    cen
    wbr
    0z
    cc0
    lzenom
    ax-mp
    eqbrtri
    @20
    com
    enfi
    ax-mp
    mtbir
    #
    @20
    cn
    cin
    cn
    @20
    cin
    #
    c0
    @20
    cn
    incom
    cn
    cz
    disjdif
    #
    eqtri
    #
    eldioph4b
    @12
    @13
    @28
    @11
    @12
    @13
    wa
    #
    @25
    @11
    vb
    @27
    @40
    @17
    @27
    wcel
    #
    wa
    #
    @11
    @25
    @6
    @24
    wcel
    #
    va
    @8
    crab
    #
    @10
    wcel
    @42
    @44
    @5
    @15
    cun
    #
    ve
    cz
    @20
    @3
    cun
    #
    cmap
    co
    #
    ve
    cv
    #
    cF
    cid
    @20
    cres
    #
    cun
    #
    ccom
    #
    @17
    cfv
    #
    cmpt
    #
    cfv
    #
    cc0
    wceq
    #
    vd
    @21
    wrex
    #
    va
    @8
    crab
    #
    @10
    @42
    @43
    @56
    va
    @8
    @42
    @5
    @8
    wcel
    #
    wa
    #
    @43
    @6
    @15
    cun
    #
    @17
    cfv
    #
    cc0
    wceq
    #
    vd
    @21
    wrex
    #
    @56
    @59
    @6
    @23
    wcel
    #
    @43
    @63
    wb
    @59
    @58
    @4
    @64
    @42
    @58
    simpr
    @1
    @4
    @13
    @41
    @58
    simp-4r
    @5
    cn0
    @3
    cF
    @2
    c1
    cN
    cfz
    ovex
    mapco2
    syl2anc
    @22
    @63
    vc
    @6
    @23
    @14
    @6
    wceq
    #
    @19
    @62
    vd
    @21
    @65
    @18
    @61
    cc0
    @65
    @16
    @60
    @17
    @14
    @6
    @15
    uneq1
    fveq2d
    eqeq1d
    rexbidv
    elrab3
    syl
    @59
    @62
    @55
    vd
    @21
    @59
    @15
    @21
    wcel
    #
    wa
    #
    @61
    @54
    cc0
    @67
    @61
    @45
    @50
    ccom
    #
    @17
    cfv
    #
    @54
    @67
    @60
    @68
    @17
    @67
    @4
    @58
    @66
    @60
    @68
    wceq
    @1
    @4
    @13
    @41
    @58
    @66
    simp-5r
    @42
    @58
    @66
    simplr
    @59
    @66
    simpr
    @4
    @58
    @66
    w3a
    #
    @68
    @45
    cF
    ccom
    #
    @45
    @49
    ccom
    #
    cun
    @60
    @45
    cF
    @49
    coundi
    @70
    @71
    @6
    @72
    @15
    @70
    @71
    @6
    c0
    cun
    #
    @6
    @70
    @71
    @6
    @15
    cF
    ccom
    #
    cun
    @73
    @5
    @15
    cF
    coundir
    @70
    @74
    c0
    @6
    @70
    @20
    cn0
    @15
    wf
    #
    @4
    @20
    @3
    cin
    #
    c0
    wceq
    #
    @74
    c0
    wceq
    @66
    @4
    @75
    @58
    @15
    cn0
    @20
    elmapi
    #
    3ad2ant3
    @4
    @58
    @66
    simp1
    @77
    @70
    @76
    @3
    @20
    cin
    #
    c0
    @20
    @3
    incom
    @3
    cn
    wss
    @37
    c0
    wceq
    #
    @79
    c0
    wceq
    #
    cM
    fz1ssnn
    @38
    @3
    cn
    @20
    ssdisj
    mp2an
    #
    eqtri
    a1i
    @15
    cF
    @20
    cn0
    @2
    @3
    coeq0i
    syl3anc
    uneq2d
    syl5eq
    @6
    un0
    syl6eq
    @70
    @72
    c0
    @15
    cun
    #
    @15
    @70
    @72
    @5
    @49
    ccom
    #
    @15
    @49
    ccom
    #
    cun
    @83
    @5
    @15
    @49
    coundir
    @70
    @84
    c0
    @85
    @15
    @70
    @3
    cn0
    @5
    wf
    #
    @84
    c0
    wceq
    #
    @58
    @4
    @86
    @66
    @5
    cn0
    @3
    elmapi
    3ad2ant2
    @86
    @20
    @20
    @49
    wf
    #
    @81
    @87
    @20
    @20
    @49
    wf1o
    @88
    @20
    f1oi
    @20
    @20
    @49
    f1of
    ax-mp
    #
    @82
    @5
    @49
    @3
    cn0
    @20
    @20
    coeq0i
    mp3an23
    syl
    @66
    @4
    @85
    @15
    wceq
    @58
    @66
    @85
    @15
    @20
    cres
    #
    @15
    @15
    @20
    coires1
    @66
    @75
    @15
    @20
    wfn
    @90
    @15
    wceq
    @78
    @20
    cn0
    @15
    ffn
    @20
    @15
    fnresdm
    3syl
    syl5eq
    3ad2ant3
    uneq12d
    syl5eq
    @83
    @15
    c0
    cun
    @15
    c0
    @15
    uncom
    @15
    un0
    eqtri
    syl6eq
    uneq12d
    syl5req
    syl3anc
    fveq2d
    @67
    @45
    @47
    wcel
    #
    @54
    @69
    wceq
    @58
    @66
    @91
    @42
    @58
    @66
    wa
    cn0
    @46
    cmap
    co
    #
    @47
    @45
    @29
    cn0
    cz
    wss
    @92
    @47
    wss
    zex
    nn0ssz
    cn0
    cz
    @46
    cvv
    mapss
    mp2an
    @58
    @66
    @5
    @79
    cres
    #
    @15
    @79
    cres
    #
    wceq
    #
    @45
    @92
    wcel
    @93
    c0
    @94
    @93
    @5
    c0
    cres
    c0
    @79
    c0
    @5
    @82
    reseq2i
    @5
    res0
    eqtri
    @94
    @15
    c0
    cres
    c0
    @79
    c0
    @15
    @82
    reseq2i
    @15
    res0
    eqtri
    eqtr4i
    @58
    @66
    @95
    w3a
    @45
    cn0
    @3
    @20
    cun
    #
    cmap
    co
    @92
    @3
    @20
    cn0
    @5
    @15
    elmapresaun
    @96
    @46
    cn0
    cmap
    @3
    @20
    uncom
    oveq2i
    syl6eleq
    mp3an3
    sseldi
    adantll
    ve
    @45
    @52
    @69
    @47
    @53
    @48
    @45
    wceq
    @51
    @68
    @17
    @48
    @45
    @50
    coeq1
    fveq2d
    @53
    eqid
    @68
    @17
    fvex
    fvmpt
    syl
    eqtr4d
    eqeq1d
    rexbidva
    bitrd
    rabbidva
    @42
    @1
    @53
    @46
    cmzp
    cfv
    wcel
    #
    @57
    @10
    wcel
    @1
    @4
    @13
    @41
    simplll
    @42
    @46
    cvv
    wcel
    #
    @41
    @26
    @46
    @50
    wf
    #
    @97
    @98
    @42
    @20
    @3
    @30
    c1
    cM
    cfz
    ovex
    unex
    a1i
    @40
    @41
    simpr
    @4
    @99
    @1
    @13
    @41
    @4
    @26
    @46
    @49
    cF
    cun
    #
    wf
    #
    @99
    @4
    @88
    @4
    @20
    @2
    cin
    #
    c0
    wceq
    #
    @101
    @88
    @4
    @89
    a1i
    @4
    id
    @103
    @4
    @102
    @2
    @20
    cin
    #
    c0
    @20
    @2
    incom
    @2
    cn
    wss
    @80
    @104
    c0
    wceq
    cN
    fz1ssnn
    @38
    @2
    cn
    @20
    ssdisj
    mp2an
    eqtri
    a1i
    @20
    @2
    @20
    @3
    @49
    cF
    fun
    syl21anc
    @26
    @46
    @100
    @50
    @49
    cF
    uncom
    feq1i
    sylib
    ad3antlr
    ve
    @50
    @17
    @26
    @46
    mzprename
    syl3anc
    vd
    va
    @53
    cM
    @20
    @30
    @36
    @39
    eldioph4i
    syl2anc
    eqeltrd
    @25
    @9
    @44
    @10
    @25
    @7
    @43
    va
    @8
    cS
    @24
    @6
    eleq2
    rabbidv
    eleq1d
    syl5ibrcom
    rexlimdva
    expimpd
    syl5bi
    impcom
    3impb
end
