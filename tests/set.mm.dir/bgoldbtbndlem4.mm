include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "codd.mm"
include "cfv.mm"
include "caddc.mm"
include "cico.mm"
include "cmin.mm"
include "c4.mm"
include "cle.mm"
include "wbr.mm"
include "ceven.mm"
include "clt.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "wi.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "eqid.mm"
include "bgoldbtbndlem2.mm"
include "syl3anc.mm"
include "cgbe.mm"
include "wral.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "rspcv.mm"
include "syl5bi.mm"
include "id.mm"
include "isgbe.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "simp1.mm"
include "ralimi.mm"
include "cn0.mm"
include "cn.mm"
include "c3.mm"
include "cuz.mm"
include "elfzo1.mm"
include "nnm1nn0.mm"
include "3ad2ant1.mm"
include "sylbi.mm"
include "a1i.mm"
include "eluzge3nn.mm"
include "a1d.mm"
include "cz.mm"
include "elfzo2.mm"
include "cr.mm"
include "eluzelre.mm"
include "adantr.mm"
include "ltm1d.mm"
include "1red.mm"
include "resubcld.mm"
include "zre.mm"
include "adantl.mm"
include "lttr.mm"
include "mpand.mm"
include "3impia.mm"
include "3jcad.mm"
include "syl.mm"
include "imp.mm"
include "elfzo0.mm"
include "sylibr.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "eldifi.mm"
include "syl6.mm"
include "expcom.mm"
include "com13.mm"
include "mpcom.mm"
include "ad2antrr.mm"
include "wb.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "oddprmALTV.mm"
include "ad3antrrr.mm"
include "3simpa.mm"
include "anim12ci.mm"
include "df-3an.mm"
include "cc.mm"
include "oddz.mm"
include "zcnd.mm"
include "prmz.mm"
include "npcand.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "exp31.mm"
include "com23.mm"
include "impcom.mm"
include "jca.mm"
include "rspcedvd.mm"
include "ex.mm"
include "reximdva.mm"
include "exp41.mm"
include "com25.mm"
include "syl6com.mm"
include "ancoms.mm"
include "syld.mm"
include "3impib.mm"
include "com15.mm"
include "mpd.mm"
include "imp31.mm"

theorem bgoldbtbndlem4
  let wph: wff ph
  let cD: class D
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume bgoldbtbnd.m: |- ( ph -> M e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.n: |- ( ph -> N e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.b: |- ( ph -> A. n e. Even ( ( 4 < n /\ n < N ) -> n e. GoldbachEven ) )
  assume bgoldbtbnd.d: |- ( ph -> D e. ( ZZ>= ` 3 ) )
  assume bgoldbtbnd.f: |- ( ph -> F e. ( RePart ` D ) )
  assume bgoldbtbnd.i: |- ( ph -> A. i e. ( 0 ..^ D ) ( ( F ` i ) e. ( Prime \ { 2 } ) /\ ( ( F ` ( i + 1 ) ) - ( F ` i ) ) < ( N - 4 ) /\ 4 < ( ( F ` ( i + 1 ) ) - ( F ` i ) ) ) )
  assume bgoldbtbnd.0: |- ( ph -> ( F ` 0 ) = 7 )
  assume bgoldbtbnd.1: |- ( ph -> ( F ` 1 ) = ; 1 3 )
  assume bgoldbtbnd.l: |- ( ph -> M < ( F ` D ) )
  assume bgoldbtbnd.r: |- ( ph -> ( F ` D ) e. RR )

  disjoint D i
  disjoint F i
  disjoint I i
  disjoint N i
  disjoint D p
  disjoint D q
  disjoint D r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint F p
  disjoint F q
  disjoint F r
  disjoint I p
  disjoint I q
  disjoint I r
  disjoint N n
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint F m
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint I m
  disjoint N m
  disjoint m n
  disjoint X m
  disjoint k x
  assert |- ( ( ( ph /\ I e. ( 1 ..^ D ) ) /\ X e. Odd ) -> ( ( X e. ( ( F ` I ) [,) ( F ` ( I + 1 ) ) ) /\ ( X - ( F ` I ) ) <_ 4 ) -> E. p e. Prime E. q e. Prime E. r e. Prime ( ( p e. Odd /\ q e. Odd /\ r e. Odd ) /\ X = ( ( p + q ) + r ) ) ) )

  proof
    wph
    cI
    c1
    cD
    cfzo
    co
    wcel
    #
    wa
    #
    cX
    codd
    wcel
    #
    wa
    #
    cX
    cI
    cF
    cfv
    #
    cI
    c1
    caddc
    co
    cF
    cfv
    cico
    co
    wcel
    cX
    @4
    cmin
    co
    c4
    cle
    wbr
    wa
    #
    cX
    cI
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cmin
    co
    #
    ceven
    wcel
    #
    @8
    cN
    clt
    wbr
    #
    c4
    @8
    clt
    wbr
    #
    w3a
    #
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    vr
    cv
    #
    codd
    wcel
    #
    w3a
    #
    cX
    @13
    @15
    caddc
    co
    #
    @17
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    @3
    wph
    @2
    @0
    @5
    @12
    wi
    wph
    @0
    @2
    simpll
    @1
    @2
    simpr
    wph
    @0
    @2
    simplr
    wph
    cD
    @8
    vi
    vn
    cF
    cI
    cM
    cN
    cX
    bgoldbtbnd.m
    bgoldbtbnd.n
    bgoldbtbnd.b
    bgoldbtbnd.d
    bgoldbtbnd.f
    bgoldbtbnd.i
    bgoldbtbnd.0
    bgoldbtbnd.1
    bgoldbtbnd.l
    @8
    eqid
    bgoldbtbndlem2
    syl3anc
    wph
    @0
    @2
    @12
    @26
    wi
    #
    wph
    c4
    vn
    cv
    #
    clt
    wbr
    #
    @28
    cN
    clt
    wbr
    #
    wa
    #
    @28
    cgbe
    wcel
    #
    wi
    #
    vn
    ceven
    wral
    #
    @0
    @2
    @27
    wi
    wi
    bgoldbtbnd.b
    @12
    @34
    @0
    @2
    wph
    @26
    @9
    @10
    @11
    @34
    @0
    @2
    wph
    @26
    wi
    wi
    wi
    #
    wi
    @9
    @34
    @10
    @11
    wa
    #
    @35
    @9
    @34
    @11
    @10
    wa
    #
    @8
    cgbe
    wcel
    #
    wi
    #
    @36
    @35
    wi
    @34
    c4
    vm
    cv
    #
    clt
    wbr
    #
    @40
    cN
    clt
    wbr
    #
    wa
    #
    @40
    cgbe
    wcel
    #
    wi
    #
    vm
    ceven
    wral
    @9
    @39
    @33
    @45
    vn
    vm
    ceven
    @28
    @40
    wceq
    #
    @31
    @43
    @32
    @44
    @46
    @29
    @41
    @30
    @42
    @28
    @40
    c4
    clt
    breq2
    @28
    @40
    cN
    clt
    breq1
    anbi12d
    @28
    @40
    cgbe
    eleq1
    imbi12d
    cbvralv
    @45
    @39
    vm
    @8
    ceven
    @40
    @8
    wceq
    #
    @43
    @37
    @44
    @38
    @47
    @41
    @11
    @42
    @10
    @40
    @8
    c4
    clt
    breq2
    @40
    @8
    cN
    clt
    breq1
    anbi12d
    @40
    @8
    cgbe
    eleq1
    imbi12d
    rspcv
    syl5bi
    @36
    @39
    @9
    @35
    @11
    @10
    @39
    @9
    @35
    wi
    #
    wi
    @39
    @37
    @38
    @48
    @39
    id
    @38
    @35
    @9
    @38
    @9
    @14
    @16
    @8
    @20
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @35
    @8
    vq
    vp
    isgbe
    @9
    @52
    @35
    @9
    wph
    @0
    @2
    @52
    @26
    @9
    wph
    @0
    @2
    @52
    @26
    wi
    @9
    wph
    wa
    #
    @0
    wa
    #
    @2
    wa
    #
    @51
    @25
    vp
    cprime
    @55
    @13
    cprime
    wcel
    #
    wa
    #
    @50
    @24
    vq
    cprime
    @57
    @15
    cprime
    wcel
    #
    wa
    #
    @50
    @24
    @59
    @50
    wa
    #
    @23
    @14
    @16
    @7
    codd
    wcel
    #
    w3a
    #
    cX
    @20
    @7
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    @7
    cprime
    @57
    @7
    cprime
    wcel
    #
    @58
    @50
    @54
    @66
    @2
    @56
    @53
    @0
    @66
    wph
    @0
    @66
    wi
    #
    @9
    vi
    cv
    #
    cF
    cfv
    #
    cprime
    c2
    csn
    #
    cdif
    #
    wcel
    #
    @68
    c1
    caddc
    co
    cF
    cfv
    @69
    cmin
    co
    #
    cN
    c4
    cmin
    co
    clt
    wbr
    #
    c4
    @73
    clt
    wbr
    #
    w3a
    #
    vi
    cc0
    cD
    cfzo
    co
    #
    wral
    #
    wph
    @67
    bgoldbtbnd.i
    @78
    @72
    vi
    @77
    wral
    #
    wph
    @67
    wi
    @76
    @72
    vi
    @77
    @72
    @74
    @75
    simp1
    ralimi
    #
    @0
    wph
    @79
    @66
    wph
    @0
    @79
    @66
    wi
    @1
    @79
    @7
    @71
    wcel
    #
    @66
    @1
    @6
    @77
    wcel
    #
    @79
    @81
    wi
    @1
    @6
    cn0
    wcel
    #
    cD
    cn
    wcel
    #
    @6
    cD
    clt
    wbr
    #
    w3a
    #
    @82
    wph
    @0
    @86
    wph
    cD
    c3
    cuz
    cfv
    wcel
    #
    @0
    @86
    wi
    bgoldbtbnd.d
    @87
    @0
    @83
    @84
    @85
    @0
    @83
    wi
    @87
    @0
    cI
    cn
    wcel
    #
    @84
    cI
    cD
    clt
    wbr
    #
    w3a
    @83
    cD
    cI
    elfzo1
    @88
    @84
    @83
    @89
    cI
    nnm1nn0
    3ad2ant1
    sylbi
    a1i
    @87
    @84
    @0
    cD
    eluzge3nn
    a1d
    @0
    @85
    wi
    @87
    @0
    cI
    c1
    cuz
    cfv
    wcel
    #
    cD
    cz
    wcel
    #
    @89
    w3a
    @85
    cI
    c1
    cD
    elfzo2
    @90
    @91
    @89
    @85
    @90
    @91
    wa
    #
    @6
    cI
    clt
    wbr
    #
    @89
    @85
    @92
    cI
    @90
    cI
    cr
    wcel
    #
    @91
    c1
    cI
    eluzelre
    adantr
    #
    ltm1d
    @92
    @6
    cr
    wcel
    @94
    cD
    cr
    wcel
    #
    @93
    @89
    wa
    @85
    wi
    @92
    cI
    c1
    @95
    @92
    1red
    resubcld
    @95
    @91
    @96
    @90
    cD
    zre
    adantl
    @6
    cI
    cD
    lttr
    syl3anc
    mpand
    3impia
    sylbi
    a1i
    3jcad
    syl
    imp
    @6
    cD
    elfzo0
    sylibr
    @72
    @81
    vi
    @6
    @77
    @68
    @6
    wceq
    @69
    @7
    @71
    @68
    @6
    cF
    fveq2
    eleq1d
    rspcv
    syl
    #
    @7
    cprime
    @70
    eldifi
    #
    syl6
    expcom
    com13
    syl
    mpcom
    adantl
    imp
    ad2antrr
    ad2antrr
    @17
    @7
    wceq
    #
    @23
    @65
    wb
    @60
    @99
    @19
    @62
    @22
    @64
    @99
    @18
    @61
    @14
    @16
    @17
    @7
    codd
    eleq1
    3anbi3d
    @99
    @21
    @63
    cX
    @17
    @7
    @20
    caddc
    oveq2
    eqeq2d
    anbi12d
    adantl
    @60
    @62
    @64
    @60
    @14
    @16
    wa
    #
    @61
    wa
    @62
    @59
    @61
    @50
    @100
    @54
    @61
    @2
    @56
    @58
    @53
    @0
    @61
    wph
    @0
    @61
    wi
    #
    @9
    @78
    wph
    @101
    bgoldbtbnd.i
    @78
    @79
    wph
    @101
    wi
    @80
    @0
    wph
    @79
    @61
    wph
    @0
    @79
    @61
    wi
    @1
    @79
    @81
    @61
    @97
    @7
    oddprmALTV
    syl6
    expcom
    com13
    syl
    mpcom
    adantl
    imp
    ad3antrrr
    @14
    @16
    @49
    3simpa
    anim12ci
    @14
    @16
    @61
    df-3an
    sylibr
    @50
    @59
    @64
    @14
    @16
    @49
    @59
    @64
    wi
    @100
    @59
    @49
    @64
    @100
    @59
    @49
    @64
    @100
    @59
    wa
    #
    @49
    cX
    @8
    @7
    caddc
    co
    @63
    @102
    cX
    @7
    @59
    cX
    cc
    wcel
    #
    @100
    @55
    @103
    @56
    @58
    @2
    @103
    @54
    @2
    cX
    cX
    oddz
    zcnd
    adantl
    ad2antrr
    adantl
    @59
    @7
    cc
    wcel
    #
    @100
    @54
    @104
    @2
    @56
    @58
    @53
    @0
    @104
    wph
    @0
    @104
    wi
    #
    @9
    @78
    wph
    @105
    bgoldbtbnd.i
    @78
    @79
    wph
    @105
    wi
    @80
    @0
    wph
    @79
    @104
    wph
    @0
    @79
    @104
    wi
    @1
    @79
    @81
    @104
    @97
    @81
    @66
    @104
    @98
    @66
    @7
    @7
    prmz
    zcnd
    syl
    syl6
    expcom
    com13
    syl
    mpcom
    adantl
    imp
    ad3antrrr
    adantl
    npcand
    @8
    @20
    @7
    caddc
    oveq1
    sylan9req
    exp31
    com23
    3impia
    impcom
    jca
    rspcedvd
    ex
    reximdva
    reximdva
    exp41
    com25
    imp
    sylbi
    a1d
    syl6com
    ancoms
    com13
    syld
    com23
    3impib
    com15
    mpd
    imp31
    syld
end
