include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cotp.mm"
include "cmmul.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cfn.mm"
include "snfi.mm"
include "simpl.mm"
include "eqid.mm"
include "matmulr.mm"
include "eqcomd.mm"
include "sylancr.mm"
include "adantr.mm"
include "oveqd.mm"
include "a1i.mm"
include "cxp.mm"
include "cmap.mm"
include "wf.mm"
include "cvv.mm"
include "opex.mm"
include "adantl.mm"
include "fsnd.mm"
include "wb.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "xpsng.mm"
include "anidms.mm"
include "feq12d.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snex.mm"
include "xpex.mm"
include "elmapd.mm"
include "simpr.mm"
include "mamuval.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "ad2antrr.mm"
include "wral.mm"
include "df-ov.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "anim2i.mm"
include "ancomd.mm"
include "fvsng.mm"
include "syl.mm"
include "syl5eq.mm"
include "eqeltrd.mm"
include "sylan.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqcomi.mm"
include "eleq12d.mm"
include "ralsng.mm"
include "gsummptcl.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "mpt2sn.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "gsumsn.mm"
include "opeq12d.mm"
include "sneqd.mm"
include "opeq2d.mm"
include "3eqtrd.mm"

theorem mat1dimmul
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cO: class O
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume mat1dim.a: |- A = ( { E } Mat R )
  assume mat1dim.b: |- B = ( Base ` R )
  assume mat1dim.o: |- O = <. E , E >.


  assert |- ( ( ( R e. Ring /\ E e. V ) /\ ( X e. B /\ Y e. B ) ) -> ( { <. O , X >. } ( .r ` A ) { <. O , Y >. } ) = { <. O , ( X ( .r ` R ) Y ) >. } )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cO
    cX
    cop
    #
    csn
    #
    cO
    cY
    cop
    #
    csn
    #
    cA
    cmulr
    cfv
    #
    co
    @8
    @10
    cR
    cE
    csn
    #
    @12
    @12
    cotp
    cmmul
    co
    #
    co
    vx
    vy
    @12
    @12
    cR
    vk
    @12
    vx
    cv
    #
    vk
    cv
    #
    @8
    co
    #
    @15
    vy
    cv
    #
    @10
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cO
    cX
    cY
    @19
    co
    #
    cop
    #
    csn
    #
    @6
    @11
    @13
    @8
    @10
    @2
    @11
    @13
    wceq
    #
    @5
    @2
    @12
    cfn
    wcel
    #
    @0
    @27
    cE
    snfi
    #
    @0
    @1
    simpl
    #
    @28
    @0
    wa
    @13
    @11
    cA
    cR
    @13
    @12
    crg
    mat1dim.a
    @13
    eqid
    #
    matmulr
    eqcomd
    sylancr
    adantr
    oveqd
    @6
    cB
    @12
    cR
    @19
    vx
    vk
    vy
    @13
    @12
    @12
    crg
    @8
    @10
    @31
    mat1dim.b
    @19
    eqid
    #
    @2
    @0
    @5
    @30
    adantr
    #
    @28
    @6
    @29
    a1i
    #
    @34
    @34
    @6
    @8
    cB
    @12
    @12
    cxp
    #
    cmap
    co
    #
    wcel
    @35
    cB
    @8
    wf
    #
    @6
    @37
    cE
    cE
    cop
    #
    csn
    #
    cB
    @38
    cX
    cop
    #
    csn
    #
    wf
    #
    @6
    @38
    cX
    cvv
    cB
    @38
    cvv
    wcel
    #
    @6
    cE
    cE
    opex
    #
    a1i
    #
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    #
    fsnd
    @1
    @37
    @42
    wb
    @0
    @5
    @1
    @35
    @39
    cB
    @8
    @41
    @8
    @41
    wceq
    @1
    @7
    @40
    cO
    @38
    cX
    mat1dim.o
    opeq1i
    sneqi
    #
    a1i
    @1
    @35
    @39
    wceq
    cE
    cE
    cV
    cV
    xpsng
    anidms
    #
    feq12d
    ad2antlr
    mpbird
    @6
    cB
    @35
    @8
    cvv
    cvv
    cB
    cvv
    wcel
    @6
    cB
    cR
    cbs
    cfv
    #
    cvv
    mat1dim.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    #
    @35
    cvv
    wcel
    @6
    @12
    @12
    cE
    snex
    #
    @51
    xpex
    a1i
    #
    elmapd
    mpbird
    @6
    @10
    @36
    wcel
    @35
    cB
    @10
    wf
    #
    @6
    @53
    @39
    cB
    @38
    cY
    cop
    #
    csn
    #
    wf
    #
    @6
    @38
    cY
    cvv
    cB
    @45
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    #
    fsnd
    @1
    @53
    @56
    wb
    @0
    @5
    @1
    @35
    @39
    cB
    @10
    @55
    @10
    @55
    wceq
    @1
    @9
    @54
    cO
    @38
    cY
    mat1dim.o
    opeq1i
    sneqi
    #
    a1i
    @48
    feq12d
    ad2antlr
    mpbird
    @6
    cB
    @35
    @10
    cvv
    cvv
    @50
    @52
    elmapd
    mpbird
    mamuval
    @6
    @23
    @38
    cR
    vk
    @12
    cE
    @15
    @8
    co
    #
    @15
    cE
    @10
    co
    #
    @19
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cop
    #
    csn
    #
    cO
    cE
    cE
    @8
    co
    #
    cE
    cE
    @10
    co
    #
    @19
    co
    #
    cop
    #
    csn
    @26
    @6
    @1
    @1
    @63
    @49
    wcel
    @23
    @65
    wceq
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    #
    @70
    @6
    @49
    vk
    cR
    @12
    @61
    @49
    eqid
    @0
    cR
    ccmn
    wcel
    @1
    @5
    cR
    ringcmn
    ad2antrr
    @34
    @6
    @61
    @49
    wcel
    #
    vk
    @12
    wral
    #
    @68
    cB
    wcel
    #
    @6
    @0
    @66
    cB
    wcel
    @67
    cB
    wcel
    @73
    @33
    @6
    @66
    cX
    cB
    @6
    @66
    @38
    @41
    cfv
    #
    cX
    @66
    @38
    @8
    cfv
    @74
    cE
    cE
    @8
    df-ov
    @38
    @8
    @41
    @47
    fveq1i
    eqtri
    @5
    @74
    cX
    wceq
    #
    @2
    @5
    @43
    @3
    wa
    @75
    @5
    @3
    @43
    @4
    @43
    @3
    @43
    @4
    @44
    a1i
    anim2i
    ancomd
    @38
    cX
    cvv
    cB
    fvsng
    syl
    adantl
    syl5eq
    #
    @46
    eqeltrd
    @6
    @67
    cY
    cB
    @6
    @67
    @38
    @55
    cfv
    #
    cY
    @67
    @38
    @10
    cfv
    @77
    cE
    cE
    @10
    df-ov
    @38
    @10
    @55
    @58
    fveq1i
    eqtri
    @5
    @77
    cY
    wceq
    #
    @2
    @3
    @43
    @4
    @78
    @43
    @3
    @44
    a1i
    @38
    cY
    cvv
    cB
    fvsng
    sylan
    adantl
    syl5eq
    #
    @57
    eqeltrd
    cB
    cR
    @19
    @66
    @67
    mat1dim.b
    @32
    ringcl
    syl3anc
    #
    @1
    @72
    @73
    wb
    @0
    @5
    @71
    @73
    vk
    cE
    cV
    @15
    cE
    wceq
    #
    @61
    @68
    @49
    cB
    @81
    @59
    @66
    @60
    @67
    @19
    @15
    cE
    cE
    @8
    oveq2
    @15
    cE
    cE
    @10
    oveq1
    oveq12d
    #
    @49
    cB
    wceq
    @81
    cB
    @49
    mat1dim.b
    eqcomi
    a1i
    eleq12d
    ralsng
    ad2antlr
    mpbird
    gsummptcl
    vx
    vy
    cE
    cE
    @22
    cR
    vk
    @12
    @59
    @18
    @19
    co
    #
    cmpt
    #
    cgsu
    co
    @49
    @63
    @23
    cV
    cV
    @23
    eqid
    @14
    cE
    wceq
    #
    @21
    @84
    cR
    cgsu
    @85
    vk
    @12
    @20
    @83
    @85
    @16
    @59
    @18
    @19
    @14
    cE
    @15
    @8
    oveq1
    oveq1d
    mpteq2dv
    oveq2d
    @17
    cE
    wceq
    #
    @84
    @62
    cR
    cgsu
    @86
    vk
    @12
    @83
    @61
    @86
    @18
    @60
    @59
    @19
    @17
    cE
    @15
    @10
    oveq2
    oveq2d
    mpteq2dv
    oveq2d
    mpt2sn
    syl3anc
    @6
    @64
    @69
    @6
    @38
    cO
    @63
    @68
    @38
    cO
    wceq
    @6
    cO
    @38
    mat1dim.o
    eqcomi
    a1i
    @6
    cR
    cmnd
    wcel
    #
    @1
    @73
    @63
    @68
    wceq
    @0
    @87
    @1
    @5
    cR
    ringmnd
    ad2antrr
    @70
    @80
    @61
    cB
    @68
    vk
    cR
    cE
    cV
    mat1dim.b
    @82
    gsumsn
    syl3anc
    opeq12d
    sneqd
    @6
    @69
    @25
    @6
    @68
    @24
    cO
    @6
    @66
    cX
    @67
    cY
    @19
    @76
    @79
    oveq12d
    opeq2d
    sneqd
    3eqtrd
    3eqtrd
end
