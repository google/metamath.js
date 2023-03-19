include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "wwlksnextfun.mm"
include "wa.mm"
include "clsw.mm"
include "wb.mm"
include "fveq2.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "cword.mm"
include "chash.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "cpr.mm"
include "w3a.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "preq2d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "elrab2.mm"
include "cmin.mm"
include "eqtr3.mm"
include "expcom.mm"
include "3ad2ant1.mm"
include "com12.mm"
include "imp.mm"
include "adantr.mm"
include "simpr.mm"
include "1e2m1.mm"
include "a1i.mm"
include "oveq2d.mm"
include "nn0cn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "eqtr4d.mm"
include "eqeq2d.mm"
include "mpbird.mm"
include "opeq2.mm"
include "eqeq12d.mm"
include "syl.mm"
include "biimpd.mm"
include "ex.mm"
include "com13.mm"
include "com23.mm"
include "impcom.mm"
include "3ad2ant2.mm"
include "3adant3.mm"
include "imp31.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "anim12i.mm"
include "clt.mm"
include "wbr.mm"
include "nn0re.mm"
include "cr.mm"
include "2re.mm"
include "nn0ge0.mm"
include "2pos.mm"
include "addgegt0d.mm"
include "breq2.mm"
include "hashgt0n0.mm"
include "sylan2.mm"
include "exp32.mm"
include "jca32.mm"
include "hashneq0.mm"
include "biimprd.mm"
include "2swrd1eqwrdeq.mm"
include "syl3anc.mm"
include "ancom.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "mpbir3and.mm"
include "exp31.mm"
include "syl2anb.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem wwlksnextinj
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cR: class R
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vd: setvar d
  let vx: setvar x
  assume wwlksnextbij0.v: |- V = ( Vtx ` G )
  assume wwlksnextbij0.e: |- E = ( Edg ` G )
  assume wwlksnextbij0.d: |- D = { w e. Word V | ( ( # ` w ) = ( N + 2 ) /\ ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) }
  assume wwlksnextbij.r: |- R = { n e. V | { ( lastS ` W ) , n } e. E }
  assume wwlksnextbij.f: |- F = ( t e. D |-> ( lastS ` t ) )

  disjoint G w
  disjoint N w
  disjoint W w
  disjoint D t
  disjoint E n
  disjoint E w
  disjoint N t
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V w
  disjoint W n
  disjoint n t
  disjoint G i
  disjoint i w
  disjoint N i
  disjoint D d
  disjoint D x
  disjoint d x
  disjoint F d
  disjoint F x
  disjoint N d
  disjoint N x
  disjoint d t
  disjoint d w
  disjoint t x
  disjoint w x
  assert |- ( N e. NN0 -> F : D -1-1-> R )

  proof
    cN
    cn0
    wcel
    #
    cD
    cR
    cF
    wf
    vd
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wi
    #
    vx
    cD
    wral
    vd
    cD
    wral
    cD
    cR
    cF
    wf1
    vw
    vt
    cD
    cR
    vn
    cE
    cF
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnextbij0.d
    wwlksnextbij.r
    wwlksnextbij.f
    wwlksnextfun
    @0
    @7
    vd
    vx
    cD
    cD
    @0
    @1
    cD
    wcel
    #
    @3
    cD
    wcel
    #
    wa
    #
    wa
    @5
    @1
    clsw
    cfv
    #
    @3
    clsw
    cfv
    #
    wceq
    #
    @6
    @10
    @5
    @13
    wb
    @0
    @8
    @9
    @2
    @11
    @4
    @12
    vt
    @1
    vt
    cv
    #
    clsw
    cfv
    #
    @11
    cD
    cF
    @14
    @1
    clsw
    fveq2
    wwlksnextbij.f
    @1
    clsw
    fvex
    fvmpt
    vt
    @3
    @15
    @12
    cD
    cF
    @14
    @3
    clsw
    fveq2
    wwlksnextbij.f
    @3
    clsw
    fvex
    fvmpt
    eqeqan12d
    adantl
    @10
    @0
    @13
    @6
    wi
    #
    @8
    @1
    cV
    cword
    #
    wcel
    #
    @1
    chash
    cfv
    #
    cN
    c2
    caddc
    co
    #
    wceq
    #
    @1
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    cW
    clsw
    cfv
    #
    @11
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    wa
    #
    @3
    @17
    wcel
    #
    @3
    chash
    cfv
    #
    @20
    wceq
    #
    @3
    @23
    csubstr
    co
    #
    cW
    wceq
    #
    @26
    @12
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    wa
    #
    @0
    @16
    wi
    @9
    vw
    cv
    #
    chash
    cfv
    #
    @20
    wceq
    #
    @40
    @23
    csubstr
    co
    #
    cW
    wceq
    #
    @26
    @40
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @29
    vw
    @1
    @17
    cD
    @40
    @1
    wceq
    #
    @42
    @21
    @44
    @25
    @47
    @28
    @49
    @41
    @19
    @20
    @40
    @1
    chash
    fveq2
    eqeq1d
    @49
    @43
    @24
    cW
    @40
    @1
    @23
    csubstr
    oveq1
    eqeq1d
    @49
    @46
    @27
    cE
    @49
    @45
    @11
    @26
    @40
    @1
    clsw
    fveq2
    preq2d
    eleq1d
    3anbi123d
    wwlksnextbij0.d
    elrab2
    @48
    @38
    vw
    @3
    @17
    cD
    @40
    @3
    wceq
    #
    @42
    @33
    @44
    @35
    @47
    @37
    @50
    @41
    @32
    @20
    @40
    @3
    chash
    fveq2
    eqeq1d
    @50
    @43
    @34
    cW
    @40
    @3
    @23
    csubstr
    oveq1
    eqeq1d
    @50
    @46
    @36
    cE
    @50
    @45
    @12
    @26
    @40
    @3
    clsw
    fveq2
    preq2d
    eleq1d
    3anbi123d
    wwlksnextbij0.d
    elrab2
    @30
    @39
    wa
    #
    @0
    @13
    @6
    @51
    @0
    wa
    #
    @13
    wa
    #
    @6
    @19
    @32
    wceq
    #
    @13
    @1
    cc0
    @19
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @3
    @56
    csubstr
    co
    #
    wceq
    #
    @52
    @54
    @13
    @51
    @54
    @0
    @30
    @39
    @54
    @29
    @39
    @54
    wi
    #
    @18
    @21
    @25
    @60
    @28
    @39
    @21
    @54
    @38
    @21
    @54
    wi
    #
    @31
    @33
    @35
    @61
    @37
    @21
    @33
    @54
    @19
    @32
    @20
    eqtr3
    expcom
    3ad2ant1
    adantl
    com12
    3ad2ant1
    adantl
    imp
    adantr
    adantr
    @52
    @13
    simpr
    @52
    @59
    @13
    @30
    @39
    @0
    @59
    @29
    @39
    @0
    @59
    wi
    #
    wi
    #
    @18
    @21
    @25
    @63
    @28
    @39
    @21
    @25
    wa
    #
    @62
    @38
    @64
    @62
    wi
    #
    @31
    @35
    @33
    @65
    @37
    @64
    @35
    @62
    @25
    @21
    @35
    @62
    wi
    @25
    @35
    @21
    @62
    @25
    @35
    @21
    @62
    wi
    #
    @25
    @35
    wa
    @24
    @34
    wceq
    #
    @66
    @24
    @34
    cW
    eqtr3
    @0
    @21
    @67
    @59
    @0
    @21
    @67
    @59
    wi
    @0
    @21
    wa
    #
    @67
    @59
    @68
    @22
    @55
    wceq
    #
    @67
    @59
    wb
    @68
    @69
    @22
    @20
    c1
    cmin
    co
    #
    wceq
    #
    @0
    @71
    @21
    @0
    @22
    cN
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @70
    @0
    c1
    @72
    cN
    caddc
    c1
    @72
    wceq
    @0
    1e2m1
    a1i
    oveq2d
    @0
    cN
    c2
    c1
    cN
    nn0cn
    @0
    2cnd
    @0
    1cnd
    addsubassd
    eqtr4d
    adantr
    @21
    @69
    @71
    wb
    @0
    @21
    @55
    @70
    @22
    @19
    @20
    c1
    cmin
    oveq1
    eqeq2d
    adantl
    mpbird
    @69
    @24
    @57
    @34
    @58
    @69
    @23
    @56
    @1
    csubstr
    @22
    @55
    cc0
    opeq2
    #
    oveq2d
    @69
    @23
    @56
    @3
    csubstr
    @73
    oveq2d
    eqeq12d
    syl
    biimpd
    ex
    com13
    syl
    ex
    com23
    impcom
    com12
    3ad2ant2
    adantl
    com12
    3adant3
    adantl
    imp31
    adantr
    @53
    @18
    @31
    wa
    #
    @1
    c0
    wne
    #
    @3
    c0
    wne
    #
    wa
    #
    wa
    #
    @6
    @54
    @13
    @59
    w3a
    #
    wb
    @52
    @78
    @13
    @52
    @74
    @75
    @76
    @51
    @74
    @0
    @30
    @18
    @39
    @31
    @18
    @29
    simpl
    @31
    @38
    simpl
    anim12i
    adantr
    @51
    @0
    @75
    @30
    @0
    @75
    wi
    #
    @39
    @29
    @18
    @80
    @21
    @25
    @18
    @80
    wi
    @28
    @18
    @21
    @80
    @18
    @21
    @0
    @75
    @21
    @0
    wa
    #
    @18
    cc0
    @19
    clt
    wbr
    #
    @75
    @81
    @82
    cc0
    @20
    clt
    wbr
    #
    @0
    @83
    @21
    @0
    cN
    c2
    cN
    nn0re
    c2
    cr
    wcel
    @0
    2re
    a1i
    cN
    nn0ge0
    cc0
    c2
    clt
    wbr
    @0
    2pos
    a1i
    addgegt0d
    #
    adantl
    @21
    @82
    @83
    wb
    @0
    @19
    @20
    cc0
    clt
    breq2
    adantr
    mpbird
    @1
    @17
    hashgt0n0
    sylan2
    exp32
    com12
    3ad2ant1
    impcom
    adantr
    imp
    @51
    @0
    @76
    @39
    @0
    @76
    wi
    #
    @30
    @38
    @31
    @85
    @33
    @35
    @31
    @85
    wi
    @37
    @31
    @33
    @85
    @31
    @33
    @0
    @76
    @33
    @0
    wa
    #
    @31
    cc0
    @32
    clt
    wbr
    #
    @76
    @86
    @87
    @83
    @0
    @83
    @33
    @84
    adantl
    @33
    @87
    @83
    wb
    @0
    @32
    @20
    cc0
    clt
    breq2
    adantr
    mpbird
    @3
    @17
    hashgt0n0
    sylan2
    exp32
    com12
    3ad2ant1
    impcom
    adantl
    imp
    jca32
    adantr
    @78
    @6
    @54
    @59
    @13
    wa
    #
    wa
    #
    @79
    @78
    @18
    @31
    @82
    @6
    @89
    wb
    @74
    @18
    @77
    @18
    @31
    simpl
    adantr
    @74
    @31
    @77
    @18
    @31
    simpr
    adantr
    @77
    @74
    @82
    @75
    @74
    @82
    wi
    @76
    @74
    @75
    @82
    @18
    @75
    @82
    wi
    @31
    @18
    @82
    @75
    @1
    @17
    hashneq0
    biimprd
    adantr
    com12
    adantr
    impcom
    @3
    cV
    @1
    2swrd1eqwrdeq
    syl3anc
    @89
    @54
    @13
    @59
    wa
    #
    wa
    @79
    @88
    @90
    @54
    @59
    @13
    ancom
    anbi2i
    @54
    @13
    @59
    3anass
    bitr4i
    syl6bb
    syl
    mpbir3and
    exp31
    syl2anb
    impcom
    sylbid
    ralrimivva
    vd
    vx
    cD
    cR
    cF
    dff13
    sylanbrc
end
