include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "opex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "df-cgr.mm"
include "brab.mm"
include "wb.mm"
include "opelxp2.mm"
include "ad2antll.mm"
include "simplrr.mm"
include "eedimeq.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "eqeq12d.mm"
include "syl.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "eqeqan12d.mm"
include "ad2antrr.mm"
include "bitrd.mm"
include "biimpd.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "wi.mm"
include "eleenn.mm"
include "opelxpi.mm"
include "anim12i.mm"
include "adantr.mm"
include "biimpar.mm"
include "jca.mm"
include "sqxpeqd.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "sylan2.mm"
include "exp32.mm"
include "mpcom.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem brcgr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint N i
  disjoint A i
  disjoint B i
  disjoint C i
  disjoint D i
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint i n
  disjoint n x
  disjoint n y
  disjoint i x
  disjoint i y
  disjoint x y
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint D n
  disjoint D x
  disjoint D y
  assert |- ( ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. <-> sum_ i e. ( 1 ... N ) ( ( ( A ` i ) - ( B ` i ) ) ^ 2 ) = sum_ i e. ( 1 ... N ) ( ( ( C ` i ) - ( D ` i ) ) ^ 2 ) ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    ccgr
    wbr
    @0
    vn
    cv
    #
    cee
    cfv
    #
    @3
    cxp
    #
    wcel
    #
    @1
    @4
    wcel
    #
    wa
    #
    c1
    @2
    cfz
    co
    #
    vi
    cv
    #
    @0
    c1st
    cfv
    #
    cfv
    #
    @9
    @0
    c2nd
    cfv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @8
    @9
    @1
    c1st
    cfv
    #
    cfv
    #
    @9
    @1
    c2nd
    cfv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @27
    wcel
    wa
    #
    cC
    @27
    wcel
    #
    cD
    @27
    wcel
    #
    wa
    #
    wa
    #
    c1
    cN
    cfz
    co
    #
    @9
    cA
    cfv
    #
    @9
    cB
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @33
    @9
    cC
    cfv
    #
    @9
    cD
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    wceq
    #
    vx
    cv
    #
    @4
    wcel
    #
    vy
    cv
    #
    @4
    wcel
    #
    wa
    #
    @8
    @9
    @45
    c1st
    cfv
    #
    cfv
    #
    @9
    @45
    c2nd
    cfv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @8
    @9
    @47
    c1st
    cfv
    #
    cfv
    #
    @9
    @47
    c2nd
    cfv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @5
    @48
    wa
    #
    @16
    @63
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @26
    vx
    vy
    @0
    @1
    ccgr
    cA
    cB
    opex
    cC
    cD
    opex
    @45
    @0
    wceq
    #
    @65
    @68
    vn
    cn
    @69
    @49
    @66
    @64
    @67
    @69
    @46
    @5
    @48
    @45
    @0
    @4
    eleq1
    anbi1d
    @69
    @56
    @16
    @63
    @69
    @8
    @55
    @15
    vi
    @69
    @54
    @14
    c2
    cexp
    @69
    @51
    @11
    @53
    @13
    cmin
    @69
    @9
    @50
    @10
    @45
    @0
    c1st
    fveq2
    fveq1d
    @69
    @9
    @52
    @12
    @45
    @0
    c2nd
    fveq2
    fveq1d
    oveq12d
    oveq1d
    sumeq2sdv
    eqeq1d
    anbi12d
    rexbidv
    @47
    @1
    wceq
    #
    @68
    @25
    vn
    cn
    @70
    @66
    @7
    @67
    @24
    @70
    @48
    @6
    @5
    @47
    @1
    @4
    eleq1
    anbi2d
    @70
    @63
    @23
    @16
    @70
    @8
    @62
    @22
    vi
    @70
    @61
    @21
    c2
    cexp
    @70
    @58
    @18
    @60
    @20
    cmin
    @70
    @9
    @57
    @17
    @47
    @1
    c1st
    fveq2
    fveq1d
    @70
    @9
    @59
    @19
    @47
    @1
    c2nd
    fveq2
    fveq1d
    oveq12d
    oveq1d
    sumeq2sdv
    eqeq2d
    anbi12d
    rexbidv
    vx
    vy
    vi
    vn
    df-cgr
    brab
    @32
    @26
    @44
    @32
    @25
    @44
    vn
    cn
    @32
    @2
    cn
    wcel
    #
    wa
    #
    @7
    @24
    @44
    @72
    @7
    wa
    #
    @24
    @44
    @73
    @24
    @33
    @15
    vi
    csu
    #
    @33
    @22
    vi
    csu
    #
    wceq
    #
    @44
    @73
    @2
    cN
    wceq
    #
    @24
    @76
    wb
    @32
    @7
    @77
    @71
    @32
    @7
    wa
    cD
    @3
    wcel
    #
    @30
    @77
    @6
    @78
    @32
    @5
    cC
    cD
    @3
    @3
    opelxp2
    ad2antll
    @28
    @29
    @30
    @7
    simplrr
    cD
    cN
    @2
    eedimeq
    syl2anc
    adantlr
    @77
    @16
    @74
    @23
    @75
    @77
    @8
    @33
    @15
    vi
    @2
    cN
    c1
    cfz
    oveq2
    #
    sumeq1d
    @77
    @8
    @33
    @22
    vi
    @79
    sumeq1d
    eqeq12d
    #
    syl
    @32
    @76
    @44
    wb
    @71
    @7
    @28
    @31
    @74
    @38
    @75
    @43
    @28
    @33
    @15
    @37
    vi
    @28
    @14
    @36
    c2
    cexp
    @28
    @11
    @34
    @13
    @35
    cmin
    @28
    @9
    @10
    cA
    cA
    cB
    @27
    @27
    op1stg
    fveq1d
    @28
    @9
    @12
    cB
    cA
    cB
    @27
    @27
    op2ndg
    fveq1d
    oveq12d
    oveq1d
    sumeq2sdv
    @31
    @33
    @22
    @42
    vi
    @31
    @21
    @41
    c2
    cexp
    @31
    @18
    @39
    @20
    @40
    cmin
    @31
    @9
    @17
    cC
    cC
    cD
    @27
    @27
    op1stg
    fveq1d
    @31
    @9
    @19
    cD
    cC
    cD
    @27
    @27
    op2ndg
    fveq1d
    oveq12d
    oveq1d
    sumeq2sdv
    eqeqan12d
    #
    ad2antrr
    bitrd
    biimpd
    expimpd
    rexlimdva
    cN
    cn
    wcel
    #
    @32
    @44
    @26
    wi
    @30
    @82
    @28
    @29
    cD
    cN
    eleenn
    ad2antll
    @82
    @32
    @44
    @26
    @32
    @44
    wa
    #
    @82
    @0
    @27
    @27
    cxp
    #
    wcel
    #
    @1
    @84
    wcel
    #
    wa
    #
    @76
    wa
    #
    @26
    @83
    @87
    @76
    @32
    @87
    @44
    @28
    @85
    @31
    @86
    cA
    cB
    @27
    @27
    opelxpi
    cC
    cD
    @27
    @27
    opelxpi
    anim12i
    adantr
    @32
    @76
    @44
    @81
    biimpar
    jca
    @25
    @88
    vn
    cN
    cn
    @77
    @7
    @87
    @24
    @76
    @77
    @5
    @85
    @6
    @86
    @77
    @4
    @84
    @0
    @77
    @3
    @27
    @2
    cN
    cee
    fveq2
    sqxpeqd
    #
    eleq2d
    @77
    @4
    @84
    @1
    @89
    eleq2d
    anbi12d
    @80
    anbi12d
    rspcev
    sylan2
    exp32
    mpcom
    impbid
    syl5bb
end
