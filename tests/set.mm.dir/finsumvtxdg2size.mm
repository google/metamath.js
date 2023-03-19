include "cupgr.mm"
include "wcel.mm"
include "cfn.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "c2.mm"
include "chash.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cvtx.mm"
include "ciedg.mm"
include "cvtxdg.mm"
include "wi.mm"
include "cop.mm"
include "upgrop.mm"
include "wnel.mm"
include "cdm.mm"
include "crab.mm"
include "cres.mm"
include "csn.mm"
include "cdif.mm"
include "fvex.mm"
include "resex.mm"
include "wa.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "simpl.mm"
include "oveq12.mm"
include "fveq1d.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "df-ov.mm"
include "syl6eq.mm"
include "vex.mm"
include "opvtxfvi.mm"
include "eqcomi.mm"
include "eqid.mm"
include "upgrres.mm"
include "opeq12.mm"
include "fveq2d.mm"
include "cc0.mm"
include "c0.mm"
include "cvv.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "2t0e0.mm"
include "a1i.mm"
include "opiedgfvi.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "eqeq1i.mm"
include "uhgr0vb.mm"
include "sylan2b.mm"
include "mpbid.mm"
include "syl5eq.mm"
include "sylibr.mm"
include "sumeq1.mm"
include "sum0.mm"
include "3eqtr4rd.mm"
include "a1d.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "w3a.mm"
include "eqcoms.mm"
include "3ad2ant2.mm"
include "hashclb.mm"
include "biimprd.mm"
include "dmeqi.mm"
include "rabeqi.mm"
include "eqidd.mm"
include "neleq12d.mm"
include "rabbiia.mm"
include "eqtri.mm"
include "reseq12i.mm"
include "finsumvtxdg2sstep.mm"
include "fveq1i.mm"
include "sumeq2i.mm"
include "syl6ibr.mm"
include "exp32.mm"
include "com34.mm"
include "3adant2.mm"
include "syl5.mm"
include "sylbid.mm"
include "impcom.mm"
include "imp.mm"
include "opfi1ind.mm"
include "ex.mm"
include "syl.mm"
include "eleq1i.mm"
include "vtxdgop.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "3imtr4d.mm"
include "3imp.mm"

theorem finsumvtxdg2size
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cI: class I
  let cV: class V
  let ve: setvar e
  let vk: setvar k
  let vn: setvar n
  let vf: setvar f
  let vi: setvar i
  let vw: setvar w
  let vy: setvar y
  assume sumvtxdg2size.v: |- V = ( Vtx ` G )
  assume sumvtxdg2size.i: |- I = ( iEdg ` G )
  assume sumvtxdg2size.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint V v
  disjoint G e
  disjoint G k
  disjoint G n
  disjoint e k
  disjoint e n
  disjoint e v
  disjoint k n
  disjoint k v
  disjoint n v
  disjoint e f
  disjoint e i
  disjoint e w
  disjoint f i
  disjoint f k
  disjoint f n
  disjoint f v
  disjoint f w
  disjoint i k
  disjoint i n
  disjoint i v
  disjoint i w
  disjoint k w
  disjoint n w
  disjoint v w
  disjoint e y
  disjoint f y
  disjoint k y
  disjoint n y
  disjoint v y
  disjoint w y
  assert |- ( ( G e. UPGraph /\ V e. Fin /\ I e. Fin ) -> sum_ v e. V ( D ` v ) = ( 2 x. ( # ` I ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cI
    cfn
    wcel
    #
    cV
    vv
    cv
    #
    cD
    cfv
    #
    vv
    csu
    #
    c2
    cI
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    cG
    ciedg
    cfv
    #
    cfn
    wcel
    #
    @9
    @3
    @9
    @11
    cvtxdg
    co
    #
    cfv
    #
    vv
    csu
    #
    c2
    @11
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    @1
    @2
    @8
    wi
    @0
    @9
    @11
    cop
    cupgr
    wcel
    #
    @10
    @19
    wi
    cG
    upgrop
    @20
    @10
    @19
    @19
    ve
    cv
    #
    cfn
    wcel
    #
    vk
    cv
    #
    @3
    @23
    @21
    cvtxdg
    co
    #
    cfv
    #
    vv
    csu
    #
    c2
    @21
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    @23
    @21
    cop
    #
    ciedg
    cfv
    #
    vn
    cv
    #
    vi
    cv
    #
    @32
    cfv
    #
    wnel
    #
    vi
    @32
    cdm
    #
    crab
    #
    cres
    #
    cfn
    wcel
    #
    @23
    @33
    csn
    cdif
    #
    @3
    @41
    @39
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    vv
    csu
    #
    c2
    @39
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    #
    vf
    cv
    #
    cfn
    wcel
    #
    vw
    cv
    #
    @3
    @52
    @50
    cop
    #
    cvtxdg
    cfv
    #
    cfv
    #
    vv
    csu
    #
    c2
    @50
    chash
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    vy
    vw
    vk
    ve
    vf
    vn
    @11
    @39
    cupgr
    @9
    cG
    ciedg
    fvex
    @32
    @38
    @31
    ciedg
    fvex
    resex
    @23
    @9
    wceq
    #
    @21
    @11
    wceq
    #
    wa
    #
    @22
    @12
    @29
    @18
    @61
    @22
    @12
    wb
    @60
    @21
    @11
    cfn
    eleq1
    adantl
    @62
    @26
    @15
    @28
    @17
    @62
    @23
    @9
    @25
    @14
    vv
    @60
    @61
    simpl
    @62
    @25
    @14
    wceq
    @3
    @23
    wcel
    #
    @62
    @3
    @24
    @13
    @23
    @9
    @21
    @11
    cvtxdg
    oveq12
    fveq1d
    adantr
    sumeq12dv
    @61
    @28
    @17
    wceq
    @60
    @61
    @27
    @16
    c2
    cmul
    @21
    @11
    chash
    fveq2
    oveq2d
    adantl
    eqeq12d
    imbi12d
    @23
    @52
    wceq
    #
    @21
    @50
    wceq
    #
    wa
    #
    @22
    @51
    @29
    @59
    @65
    @22
    @51
    wb
    @64
    @21
    @50
    cfn
    eleq1
    adantl
    @66
    @26
    @56
    @28
    @58
    @66
    @23
    @52
    @25
    @55
    vv
    @64
    @65
    simpl
    @66
    @25
    @55
    wceq
    @63
    @66
    @3
    @24
    @54
    @66
    @24
    @52
    @50
    cvtxdg
    co
    @54
    @23
    @52
    @21
    @50
    cvtxdg
    oveq12
    @52
    @50
    cvtxdg
    df-ov
    syl6eq
    fveq1d
    adantr
    sumeq12dv
    @65
    @28
    @58
    wceq
    @64
    @65
    @27
    @57
    c2
    cmul
    @21
    @50
    chash
    fveq2
    oveq2d
    adantl
    eqeq12d
    imbi12d
    @42
    vi
    @32
    @38
    @31
    @33
    @23
    @31
    cvtx
    cfv
    #
    @23
    @21
    @23
    vk
    vex
    #
    ve
    vex
    #
    opvtxfvi
    eqcomi
    #
    @32
    eqid
    @38
    eqid
    @42
    eqid
    #
    upgrres
    @52
    @41
    wceq
    #
    @50
    @39
    wceq
    #
    wa
    #
    @51
    @40
    @59
    @48
    @73
    @51
    @40
    wb
    @72
    @50
    @39
    cfn
    eleq1
    adantl
    @74
    @56
    @45
    @58
    @47
    @74
    @52
    @41
    @55
    @44
    vv
    @72
    @73
    simpl
    @74
    @55
    @44
    wceq
    @3
    @52
    wcel
    @74
    @3
    @54
    @43
    @74
    @53
    @42
    cvtxdg
    @52
    @50
    @41
    @39
    opeq12
    fveq2d
    fveq1d
    adantr
    sumeq12dv
    @73
    @58
    @47
    wceq
    @72
    @73
    @57
    @46
    c2
    cmul
    @50
    @39
    chash
    fveq2
    oveq2d
    adantl
    eqeq12d
    imbi12d
    @31
    cupgr
    wcel
    #
    @23
    chash
    cfv
    #
    cc0
    wceq
    #
    wa
    @29
    @22
    @77
    @75
    @23
    c0
    wceq
    #
    @29
    @23
    cvv
    wcel
    #
    @77
    @78
    wb
    @68
    @23
    cvv
    hasheq0
    ax-mp
    @75
    @78
    wa
    #
    c2
    cc0
    cmul
    co
    #
    cc0
    @28
    @26
    @81
    cc0
    wceq
    @80
    2t0e0
    a1i
    @80
    @27
    cc0
    c2
    cmul
    @80
    @21
    c0
    wceq
    #
    @27
    cc0
    wceq
    #
    @80
    @21
    @32
    c0
    @32
    @21
    @21
    @23
    @68
    @69
    opiedgfvi
    #
    eqcomi
    #
    @80
    @31
    cuhgr
    wcel
    #
    @32
    c0
    wceq
    #
    @75
    @86
    @78
    @31
    upgruhgr
    adantr
    @78
    @75
    @67
    c0
    wceq
    @86
    @87
    wb
    @23
    @67
    c0
    @70
    eqeq1i
    @31
    cupgr
    uhgr0vb
    sylan2b
    mpbid
    syl5eq
    @21
    cvv
    wcel
    @83
    @82
    wb
    @69
    @21
    cvv
    hasheq0
    ax-mp
    sylibr
    oveq2d
    @78
    @26
    cc0
    wceq
    @75
    @78
    @26
    c0
    @25
    vv
    csu
    cc0
    @23
    c0
    @25
    vv
    sumeq1
    @25
    vv
    sum0
    syl6eq
    adantl
    3eqtr4rd
    sylan2b
    a1d
    vy
    cv
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    @75
    @76
    @88
    wceq
    #
    @33
    @23
    wcel
    #
    w3a
    #
    wa
    @49
    @30
    @92
    @89
    @49
    @30
    wi
    #
    @92
    @89
    @76
    cn0
    wcel
    #
    @93
    @90
    @75
    @89
    @94
    wb
    #
    @91
    @95
    @88
    @76
    @88
    @76
    cn0
    eleq1
    eqcoms
    3ad2ant2
    @94
    @23
    cfn
    wcel
    #
    @92
    @93
    @79
    @94
    @96
    wi
    @68
    @79
    @96
    @94
    @23
    cvv
    hashclb
    biimprd
    ax-mp
    @75
    @91
    @96
    @93
    wi
    @90
    @75
    @91
    wa
    #
    @96
    @22
    @49
    @29
    @97
    @96
    @22
    @49
    @29
    wi
    @97
    @96
    @22
    wa
    wa
    @49
    @23
    @3
    @31
    cvtxdg
    cfv
    #
    cfv
    #
    vv
    csu
    #
    @28
    wceq
    @29
    vv
    @39
    @42
    vi
    @21
    @31
    @33
    @34
    @21
    cfv
    #
    wnel
    #
    vi
    @21
    cdm
    #
    crab
    #
    @41
    @33
    @23
    @70
    @85
    @41
    eqid
    @104
    eqid
    @32
    @21
    @38
    @104
    @84
    @38
    @36
    vi
    @103
    crab
    @104
    @36
    vi
    @37
    @103
    @32
    @21
    @84
    dmeqi
    rabeqi
    @36
    @102
    vi
    @103
    @34
    @103
    wcel
    #
    @33
    @33
    @35
    @101
    @105
    @33
    eqidd
    @105
    @34
    @32
    @21
    @32
    @21
    wceq
    @105
    @84
    a1i
    fveq1d
    neleq12d
    rabbiia
    eqtri
    reseq12i
    @71
    finsumvtxdg2sstep
    @26
    @100
    @28
    @23
    @25
    @99
    vv
    @25
    @99
    wceq
    @63
    @3
    @24
    @98
    @23
    @21
    cvtxdg
    df-ov
    fveq1i
    a1i
    sumeq2i
    eqeq1i
    syl6ibr
    exp32
    com34
    3adant2
    syl5
    sylbid
    impcom
    imp
    opfi1ind
    ex
    syl
    @1
    @10
    wb
    @0
    cV
    @9
    cfn
    sumvtxdg2size.v
    eleq1i
    a1i
    @0
    @2
    @12
    @8
    @18
    @2
    @12
    wb
    @0
    cI
    @11
    cfn
    sumvtxdg2size.i
    eleq1i
    a1i
    @0
    @5
    @15
    @7
    @17
    @0
    cV
    @9
    @4
    @14
    vv
    cV
    @9
    wceq
    @0
    sumvtxdg2size.v
    a1i
    @0
    @4
    @14
    wceq
    @3
    cV
    wcel
    @0
    @3
    cD
    @13
    @0
    cD
    cG
    cvtxdg
    cfv
    @13
    sumvtxdg2size.d
    cG
    cupgr
    vtxdgop
    syl5eq
    fveq1d
    adantr
    sumeq12dv
    @7
    @17
    wceq
    @0
    @6
    @16
    c2
    cmul
    cI
    @11
    chash
    sumvtxdg2size.i
    fveq2i
    oveq2i
    a1i
    eqeq12d
    imbi12d
    3imtr4d
    3imp
end
