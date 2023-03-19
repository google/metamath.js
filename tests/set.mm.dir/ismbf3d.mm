include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "wf.mm"
include "wceq.mm"
include "fimacnv.mm"
include "syl.mm"
include "cn.mm"
include "cv.mm"
include "cneg.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "ciun.mm"
include "imaiun.mm"
include "wss.mm"
include "wral.mm"
include "ioossre.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "wcel.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "renegcl.mm"
include "arch.mm"
include "wa.mm"
include "simpl.mm"
include "biantrurd.mm"
include "wb.mm"
include "nnre.mm"
include "ltnegcon1.mm"
include "sylan2.mm"
include "cxr.mm"
include "adantl.mm"
include "renegcld.mm"
include "rexrd.mm"
include "elioopnf.mm"
include "3bitr4d.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "eliun.mm"
include "sylibr.mm"
include "ssriv.mm"
include "eqssi.mm"
include "imaeq2i.mm"
include "eqtr3i.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "iunmbl.mm"
include "syl5eqelr.mm"
include "eqeltrrd.mm"
include "cmnf.mm"
include "c1.mm"
include "cdiv.mm"
include "cmin.mm"
include "cioc.mm"
include "cle.mm"
include "w3a.mm"
include "3simpb.mm"
include "wi.mm"
include "simplr.mm"
include "crp.mm"
include "nnrp.mm"
include "ad2antrl.mm"
include "rpreccld.mm"
include "ltsubrpd.mm"
include "simprr.mm"
include "simpr.mm"
include "nnrecre.mm"
include "resubcl.mm"
include "adantrr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "anassrs.mm"
include "imdistanda.mm"
include "syl5.mm"
include "mnfxr.mm"
include "elioc2.mm"
include "sylancr.mm"
include "rexr.mm"
include "elioomnf.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "rexlimdva.mm"
include "sylibd.mm"
include "simprl.mm"
include "mnflt.mm"
include "ad2ant2r.mm"
include "ltsub13d.mm"
include "ltled.mm"
include "mpbir3and.mm"
include "cc0.mm"
include "resubcld.mm"
include "posdifd.mm"
include "nnrecl.mm"
include "syl2anc.mm"
include "reximddv.mm"
include "ex.mm"
include "impbid.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "syl5eqr.mm"
include "cdif.mm"
include "wfun.mm"
include "ad2antrr.mm"
include "ffun.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "4syl.mm"
include "cun.mm"
include "a1i.mm"
include "pnfxr.mm"
include "ltpnf.mm"
include "df-ioc.mm"
include "df-ioo.mm"
include "xrltnle.mm"
include "xrlelttr.mm"
include "xrlttr.mm"
include "ixxun.mm"
include "syl32anc.mm"
include "uncom.mm"
include "ioomax.mm"
include "3eqtr3g.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "ixxdisj.mm"
include "mp3an13.mm"
include "syl5eq.mm"
include "uneqdifeq.mm"
include "eqtr3d.mm"
include "rspcv.mm"
include "sylc.mm"
include "difmbl.mm"
include "oveq2.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "ismbf2d.mm"

theorem ismbf3d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume ismbf3d.1: |- ( ph -> F : A --> RR )
  assume ismbf3d.2: |- ( ( ph /\ x e. RR ) -> ( `' F " ( x (,) +oo ) ) e. dom vol )

  disjoint F x
  disjoint ph x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> F e. MblFn )

  proof
    wph
    vx
    cA
    cF
    ismbf3d.1
    wph
    cF
    ccnv
    #
    cr
    cima
    #
    cA
    cvol
    cdm
    #
    wph
    cA
    cr
    cF
    wf
    #
    @1
    cA
    wceq
    ismbf3d.1
    cA
    cr
    cF
    fimacnv
    syl
    wph
    @1
    vy
    cn
    @0
    vy
    cv
    #
    cneg
    #
    cpnf
    cioo
    co
    #
    cima
    #
    ciun
    #
    @2
    @0
    vy
    cn
    @6
    ciun
    #
    cima
    @8
    @1
    vy
    @0
    cn
    @6
    imaiun
    @9
    cr
    @0
    @9
    cr
    @9
    cr
    wss
    @6
    cr
    wss
    #
    vy
    cn
    wral
    @10
    vy
    cn
    @5
    cpnf
    ioossre
    rgenw
    vy
    cn
    @6
    cr
    iunss
    mpbir
    vz
    cr
    @9
    vz
    cv
    #
    cr
    wcel
    #
    @11
    @6
    wcel
    #
    vy
    cn
    wrex
    #
    @11
    @9
    wcel
    @12
    @11
    cneg
    #
    @4
    clt
    wbr
    #
    vy
    cn
    wrex
    #
    @14
    @12
    @15
    cr
    wcel
    @17
    @11
    renegcl
    @15
    vy
    arch
    syl
    @12
    @16
    @13
    vy
    cn
    @12
    @4
    cn
    wcel
    #
    wa
    #
    @5
    @11
    clt
    wbr
    #
    @12
    @20
    wa
    #
    @16
    @13
    @19
    @12
    @20
    @12
    @18
    simpl
    biantrurd
    @18
    @12
    @4
    cr
    wcel
    #
    @16
    @20
    wb
    @4
    nnre
    #
    @11
    @4
    ltnegcon1
    sylan2
    @19
    @5
    cxr
    wcel
    @13
    @21
    wb
    @19
    @5
    @19
    @4
    @18
    @22
    @12
    @23
    adantl
    renegcld
    rexrd
    @5
    @11
    elioopnf
    syl
    3bitr4d
    rexbidva
    mpbid
    vy
    @11
    cn
    @6
    eliun
    sylibr
    ssriv
    eqssi
    imaeq2i
    eqtr3i
    wph
    @7
    @2
    wcel
    #
    vy
    cn
    wral
    @8
    @2
    wcel
    wph
    @24
    vy
    cn
    wph
    @0
    vx
    cv
    #
    cpnf
    cioo
    co
    #
    cima
    #
    @2
    wcel
    #
    vx
    cr
    wral
    #
    @5
    cr
    wcel
    @24
    @18
    wph
    @28
    vx
    cr
    ismbf3d.2
    ralrimiva
    #
    @18
    @4
    @23
    renegcld
    @28
    @24
    vx
    @5
    cr
    @25
    @5
    wceq
    #
    @27
    @7
    @2
    @31
    @26
    @6
    @0
    @25
    @5
    cpnf
    cioo
    oveq1
    imaeq2d
    eleq1d
    rspccva
    syl2an
    ralrimiva
    @7
    vy
    iunmbl
    syl
    syl5eqelr
    #
    eqeltrrd
    ismbf3d.2
    wph
    @0
    cmnf
    @25
    cioo
    co
    #
    cima
    #
    @2
    wcel
    #
    vx
    cr
    wph
    @0
    cmnf
    @11
    cioo
    co
    #
    cima
    #
    @2
    wcel
    #
    vz
    cr
    wral
    @35
    vx
    cr
    wral
    wph
    @38
    vz
    cr
    wph
    @12
    wa
    #
    vy
    cn
    @0
    cmnf
    @11
    c1
    @4
    cdiv
    co
    #
    cmin
    co
    #
    cioc
    co
    #
    cima
    #
    ciun
    #
    @37
    @2
    @39
    @44
    @0
    vy
    cn
    @42
    ciun
    #
    cima
    @37
    vy
    @0
    cn
    @42
    imaiun
    @39
    @45
    @36
    @0
    @39
    vx
    @45
    @36
    @25
    @45
    wcel
    @25
    @42
    wcel
    #
    vy
    cn
    wrex
    #
    @39
    @25
    @36
    wcel
    #
    vy
    @25
    cn
    @42
    eliun
    @39
    @47
    @25
    cr
    wcel
    #
    @25
    @11
    clt
    wbr
    #
    wa
    #
    @48
    @39
    @47
    @51
    @39
    @47
    @48
    @51
    @39
    @46
    @48
    vy
    cn
    @39
    @18
    wa
    #
    @49
    cmnf
    @25
    clt
    wbr
    #
    @25
    @41
    cle
    wbr
    #
    w3a
    #
    @51
    @46
    @48
    @55
    @49
    @54
    wa
    @52
    @51
    @49
    @53
    @54
    3simpb
    @52
    @49
    @54
    @50
    @39
    @18
    @49
    @54
    @50
    wi
    @39
    @18
    @49
    wa
    #
    wa
    #
    @54
    @41
    @11
    clt
    wbr
    #
    @50
    @57
    @11
    @40
    wph
    @12
    @56
    simplr
    #
    @57
    @4
    @18
    @4
    crp
    wcel
    @39
    @49
    @4
    nnrp
    ad2antrl
    rpreccld
    ltsubrpd
    @57
    @49
    @41
    cr
    wcel
    #
    @12
    @54
    @58
    wa
    @50
    wi
    @39
    @18
    @49
    simprr
    @39
    @18
    @60
    @49
    @39
    @12
    @40
    cr
    wcel
    #
    @60
    @18
    wph
    @12
    simpr
    @4
    nnrecre
    #
    @11
    @40
    resubcl
    syl2an
    #
    adantrr
    @59
    @25
    @41
    @11
    lelttr
    syl3anc
    mpan2d
    anassrs
    imdistanda
    syl5
    @52
    cmnf
    cxr
    wcel
    #
    @60
    @46
    @55
    wb
    #
    mnfxr
    @63
    cmnf
    @41
    @25
    elioc2
    sylancr
    #
    @39
    @48
    @51
    wb
    #
    @18
    @39
    @11
    cxr
    wcel
    #
    @67
    @12
    @68
    wph
    @11
    rexr
    adantl
    @11
    @25
    elioomnf
    syl
    #
    adantr
    3imtr4d
    rexlimdva
    @69
    sylibd
    @39
    @51
    @47
    @39
    @51
    wa
    #
    @40
    @11
    @25
    cmin
    co
    #
    clt
    wbr
    #
    @46
    vy
    cn
    @70
    @18
    @72
    wa
    #
    wa
    #
    @46
    @49
    @53
    @54
    @70
    @49
    @73
    @39
    @49
    @50
    simprl
    #
    adantr
    #
    @74
    @49
    @53
    @76
    @25
    mnflt
    syl
    @74
    @25
    @41
    @76
    @39
    @18
    @60
    @51
    @72
    @63
    ad2ant2r
    @74
    @40
    @11
    @25
    @18
    @61
    @70
    @72
    @62
    ad2antrl
    @70
    @12
    @73
    wph
    @12
    @51
    simplr
    #
    adantr
    @76
    @70
    @18
    @72
    simprr
    ltsub13d
    ltled
    @39
    @18
    @65
    @51
    @72
    @66
    ad2ant2r
    mpbir3and
    @70
    @71
    cr
    wcel
    cc0
    @71
    clt
    wbr
    #
    @72
    vy
    cn
    wrex
    @70
    @11
    @25
    @77
    @75
    resubcld
    @70
    @50
    @78
    @39
    @49
    @50
    simprr
    @70
    @25
    @11
    @75
    @77
    posdifd
    mpbid
    @71
    vy
    nnrecl
    syl2anc
    reximddv
    ex
    impbid
    @69
    bitr4d
    syl5bb
    eqrdv
    imaeq2d
    syl5eqr
    @39
    @43
    @2
    wcel
    #
    vy
    cn
    wral
    @44
    @2
    wcel
    @39
    @79
    vy
    cn
    @52
    @1
    @0
    @41
    cpnf
    cioo
    co
    #
    cima
    #
    cdif
    #
    @43
    @2
    @52
    @0
    cr
    @80
    cdif
    #
    cima
    #
    @82
    @43
    @52
    @3
    cF
    wfun
    @0
    ccnv
    wfun
    @84
    @82
    wceq
    wph
    @3
    @12
    @18
    ismbf3d.1
    ad2antrr
    cA
    cr
    cF
    ffun
    cF
    funcnvcnv
    cr
    @80
    @0
    imadif
    4syl
    @52
    @83
    @42
    @0
    @52
    @80
    @42
    cun
    #
    cr
    wceq
    #
    @83
    @42
    wceq
    #
    @52
    @42
    @80
    cun
    #
    cmnf
    cpnf
    cioo
    co
    #
    @85
    cr
    @52
    @64
    @41
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cmnf
    @41
    clt
    wbr
    #
    @41
    cpnf
    clt
    wbr
    #
    @88
    @89
    wceq
    @64
    @52
    mnfxr
    a1i
    @52
    @41
    @63
    rexrd
    #
    @91
    @52
    pnfxr
    a1i
    @52
    @60
    @92
    @63
    @41
    mnflt
    syl
    @52
    @60
    @93
    @63
    @41
    ltpnf
    syl
    vu
    vv
    vw
    vx
    cmnf
    @41
    cpnf
    cioo
    cioo
    clt
    cle
    clt
    clt
    cioc
    clt
    clt
    vu
    vv
    vw
    df-ioc
    #
    vu
    vv
    vw
    df-ioo
    #
    @41
    @25
    xrltnle
    #
    @96
    @25
    @41
    cpnf
    xrlelttr
    cmnf
    @41
    @25
    xrlttr
    ixxun
    syl32anc
    @42
    @80
    uncom
    ioomax
    3eqtr3g
    @52
    @80
    cr
    wss
    @80
    @42
    cin
    #
    c0
    wceq
    @86
    @87
    wb
    @41
    cpnf
    ioossre
    @52
    @98
    @42
    @80
    cin
    #
    c0
    @80
    @42
    incom
    @52
    @90
    @99
    c0
    wceq
    #
    @94
    @64
    @90
    @91
    @100
    mnfxr
    pnfxr
    vu
    vv
    vw
    vx
    cmnf
    @41
    cpnf
    cioo
    clt
    cle
    clt
    clt
    cioc
    @95
    @96
    @97
    ixxdisj
    mp3an13
    syl
    syl5eq
    @80
    @42
    cr
    uneqdifeq
    sylancr
    mpbid
    imaeq2d
    eqtr3d
    @52
    @1
    @2
    wcel
    #
    @81
    @2
    wcel
    #
    @82
    @2
    wcel
    wph
    @101
    @12
    @18
    @32
    ad2antrr
    @52
    @60
    @29
    @102
    @63
    wph
    @29
    @12
    @18
    @30
    ad2antrr
    @28
    @102
    vx
    @41
    cr
    @25
    @41
    wceq
    #
    @27
    @81
    @2
    @103
    @26
    @80
    @0
    @25
    @41
    cpnf
    cioo
    oveq1
    imaeq2d
    eleq1d
    rspcv
    sylc
    @1
    @81
    difmbl
    syl2anc
    eqeltrrd
    ralrimiva
    @43
    vy
    iunmbl
    syl
    eqeltrrd
    ralrimiva
    @38
    @35
    vz
    vx
    cr
    @11
    @25
    wceq
    #
    @37
    @34
    @2
    @104
    @36
    @33
    @0
    @11
    @25
    cmnf
    cioo
    oveq2
    imaeq2d
    eleq1d
    cbvralv
    sylib
    r19.21bi
    ismbf2d
end
