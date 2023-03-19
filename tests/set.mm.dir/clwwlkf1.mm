include "cn.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "clwwlkf.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "wb.mm"
include "clwwlkfv.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "cwwlksn.mm"
include "clsw.mm"
include "fveq2.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "elrab2.mm"
include "anbi12i.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cfzo.mm"
include "w3a.mm"
include "eqid.mm"
include "wwlknp.mm"
include "cmin.mm"
include "simprlr.mm"
include "simpllr.mm"
include "eqtr4d.mm"
include "ad2antlr.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "eqcomd.mm"
include "sylancl.mm"
include "oveq1.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "ex.mm"
include "impcom.mm"
include "biimpa.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "simpll.mm"
include "anim12ci.mm"
include "nnnn0.mm"
include "0nn0.mm"
include "jctil.mm"
include "adantr.mm"
include "nnre.mm"
include "lep1d.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "swrdspsleq.mm"
include "syl112anc.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "rspcv.mm"
include "syl.mm"
include "sylbid.mm"
include "imp.mm"
include "simpr.mm"
include "eqeqan12rd.mm"
include "mpbird.mm"
include "jca32.mm"
include "clt.mm"
include "1red.mm"
include "nngt0.mm"
include "0lt1.mm"
include "a1i.mm"
include "addgt0d.mm"
include "3jca.mm"
include "2swrd1eqwrdeq.mm"
include "exp31.mm"
include "expdcom.mm"
include "3adant3.mm"
include "imp31.mm"
include "com12.mm"
include "syl5bi.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem clwwlkf1
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vi: setvar i
  let cP: class P
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume clwwlkbij.d: |- D = { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) }
  assume clwwlkbij.f: |- F = ( t e. D |-> ( t substr <. 0 , N >. ) )

  disjoint G w
  disjoint N w
  disjoint D t
  disjoint G t
  disjoint t w
  disjoint N t
  disjoint G i
  disjoint N i
  disjoint P i
  disjoint P w
  disjoint i t
  disjoint W t
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint i x
  disjoint i y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  assert |- ( N e. NN -> F : D -1-1-> ( N ClWWalksN G ) )

  proof
    cN
    cn
    wcel
    #
    cD
    cN
    cG
    cclwwlkn
    co
    #
    cF
    wf
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vy
    cD
    wral
    vx
    cD
    wral
    cD
    @1
    cF
    wf1
    vw
    vt
    cD
    cF
    cG
    cN
    clwwlkbij.d
    clwwlkbij.f
    clwwlkf
    @0
    @8
    vx
    vy
    cD
    cD
    @0
    @2
    cD
    wcel
    #
    @4
    cD
    wcel
    #
    wa
    #
    wa
    @6
    @2
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    @4
    @12
    csubstr
    co
    #
    wceq
    #
    @7
    @11
    @6
    @15
    wb
    @0
    @9
    @10
    @3
    @13
    @5
    @14
    vw
    vt
    cD
    cF
    cG
    cN
    @2
    clwwlkbij.d
    clwwlkbij.f
    clwwlkfv
    vw
    vt
    cD
    cF
    cG
    cN
    @4
    clwwlkbij.d
    clwwlkbij.f
    clwwlkfv
    eqeqan12d
    adantl
    @0
    @11
    @15
    @7
    wi
    #
    @11
    @2
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    @2
    clsw
    cfv
    #
    cc0
    @2
    cfv
    #
    wceq
    #
    wa
    #
    @4
    @17
    wcel
    #
    @4
    clsw
    cfv
    #
    cc0
    @4
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    @0
    @16
    @9
    @22
    @10
    @27
    vw
    cv
    #
    clsw
    cfv
    #
    cc0
    @29
    cfv
    #
    wceq
    #
    @21
    vw
    @2
    @17
    cD
    @29
    @2
    wceq
    @30
    @19
    @31
    @20
    @29
    @2
    clsw
    fveq2
    cc0
    @29
    @2
    fveq1
    eqeq12d
    clwwlkbij.d
    elrab2
    @32
    @26
    vw
    @4
    @17
    cD
    @29
    @4
    wceq
    @30
    @24
    @31
    @25
    @29
    @4
    clsw
    fveq2
    cc0
    @29
    @4
    fveq1
    eqeq12d
    clwwlkbij.d
    elrab2
    anbi12i
    @28
    @0
    @16
    @18
    @21
    @27
    @0
    @16
    wi
    #
    @18
    @2
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @2
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    @2
    cfv
    #
    @40
    c1
    caddc
    co
    #
    @2
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    w3a
    @21
    @27
    @33
    wi
    wi
    #
    vi
    @43
    cG
    cN
    @34
    @2
    @34
    eqid
    #
    @43
    eqid
    #
    wwlknp
    @36
    @39
    @46
    @45
    @27
    @36
    @39
    wa
    #
    @21
    @33
    @23
    @26
    @49
    @21
    wa
    #
    @33
    wi
    #
    @23
    @4
    @35
    wcel
    #
    @4
    chash
    cfv
    #
    @38
    wceq
    #
    @40
    @4
    cfv
    #
    @42
    @4
    cfv
    cpr
    @43
    wcel
    vi
    @44
    wral
    #
    w3a
    @26
    @51
    wi
    #
    vi
    @43
    cG
    cN
    @34
    @4
    @47
    @48
    wwlknp
    @52
    @54
    @57
    @56
    @52
    @54
    wa
    #
    @26
    @51
    @0
    @58
    @26
    wa
    #
    @50
    @16
    @0
    @59
    @50
    wa
    #
    @15
    @7
    @0
    @60
    wa
    #
    @15
    wa
    #
    @7
    @37
    @53
    wceq
    #
    @2
    cc0
    @37
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @4
    @65
    csubstr
    co
    #
    wceq
    #
    @19
    @24
    wceq
    #
    wa
    wa
    #
    @62
    @63
    @68
    @69
    @60
    @63
    @0
    @15
    @60
    @37
    @38
    @53
    @59
    @36
    @39
    @21
    simprlr
    @52
    @54
    @26
    @50
    simpllr
    eqtr4d
    ad2antlr
    @61
    @15
    @68
    @60
    @0
    @15
    @68
    wb
    #
    @50
    @0
    @71
    wi
    #
    @59
    @39
    @72
    @36
    @21
    @39
    @0
    @71
    @39
    @0
    wa
    #
    @13
    @66
    @14
    @67
    @73
    @12
    @65
    @2
    csubstr
    @73
    cN
    @64
    cc0
    @0
    @39
    cN
    @38
    c1
    cmin
    co
    #
    @64
    @0
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    cN
    @74
    wceq
    cN
    nncn
    ax-1cn
    @75
    @76
    wa
    @74
    cN
    cN
    c1
    pncan
    eqcomd
    sylancl
    @39
    @64
    @74
    @37
    @38
    c1
    cmin
    oveq1
    eqcomd
    sylan9eqr
    opeq2d
    #
    oveq2d
    @73
    @12
    @65
    @4
    csubstr
    @77
    oveq2d
    eqeq12d
    ex
    ad2antlr
    adantl
    impcom
    biimpa
    @62
    @69
    @20
    @25
    wceq
    #
    @61
    @15
    @78
    @61
    @15
    @41
    @55
    wceq
    #
    vi
    @44
    wral
    #
    @78
    @61
    @36
    @52
    wa
    #
    cc0
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    @37
    cle
    wbr
    #
    cN
    @53
    cle
    wbr
    #
    @15
    @80
    wb
    @60
    @81
    @0
    @59
    @52
    @50
    @36
    @52
    @54
    @26
    simpll
    #
    @36
    @39
    @21
    simpll
    #
    anim12ci
    adantl
    @0
    @84
    @60
    @0
    @83
    @82
    cN
    nnnn0
    0nn0
    jctil
    adantr
    @60
    @0
    @85
    @50
    @0
    @85
    wi
    #
    @59
    @39
    @89
    @36
    @21
    @0
    @85
    @39
    cN
    @38
    cle
    wbr
    #
    @0
    cN
    cN
    nnre
    #
    lep1d
    #
    @37
    @38
    cN
    cle
    breq2
    syl5ibr
    ad2antlr
    adantl
    impcom
    @60
    @0
    @86
    @59
    @0
    @86
    wi
    #
    @50
    @54
    @93
    @52
    @26
    @0
    @86
    @54
    @90
    @92
    @53
    @38
    cN
    cle
    breq2
    syl5ibr
    ad2antlr
    adantr
    impcom
    @4
    vi
    cc0
    cN
    @34
    @2
    swrdspsleq
    syl112anc
    @61
    cc0
    @44
    wcel
    #
    @80
    @78
    wi
    @0
    @94
    @60
    @94
    @0
    cN
    lbfzo0
    biimpri
    adantr
    @79
    @78
    vi
    cc0
    @44
    @40
    cc0
    wceq
    @41
    @20
    @55
    @25
    @40
    cc0
    @2
    fveq2
    @40
    cc0
    @4
    fveq2
    eqeq12d
    rspcv
    syl
    sylbid
    imp
    @60
    @69
    @78
    wb
    @0
    @15
    @50
    @59
    @19
    @20
    @24
    @25
    @49
    @21
    simpr
    @58
    @26
    simpr
    eqeqan12rd
    ad2antlr
    mpbird
    jca32
    @62
    @36
    @52
    cc0
    @37
    clt
    wbr
    #
    w3a
    #
    @7
    @70
    wb
    @61
    @96
    @15
    @61
    @36
    @52
    @95
    @60
    @36
    @0
    @50
    @36
    @59
    @88
    adantl
    adantl
    @60
    @52
    @0
    @59
    @52
    @50
    @87
    adantr
    adantl
    @60
    @0
    @95
    @50
    @0
    @95
    wi
    #
    @59
    @39
    @97
    @36
    @21
    @0
    @95
    @39
    cc0
    @38
    clt
    wbr
    @0
    cN
    c1
    @91
    @0
    1red
    cN
    nngt0
    cc0
    c1
    clt
    wbr
    @0
    0lt1
    a1i
    addgt0d
    @37
    @38
    cc0
    clt
    breq2
    syl5ibr
    ad2antlr
    adantl
    impcom
    3jca
    adantr
    @4
    @34
    @2
    2swrd1eqwrdeq
    syl
    mpbird
    exp31
    expdcom
    ex
    3adant3
    syl
    imp
    expdcom
    3adant3
    syl
    imp31
    com12
    syl5bi
    imp
    sylbid
    ralrimivva
    vx
    vy
    cD
    @1
    cF
    dff13
    sylanbrc
end
