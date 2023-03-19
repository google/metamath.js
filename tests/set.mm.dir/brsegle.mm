include "cop.mm"
include "csegle.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "cbtwn.mm"
include "ccgr.mm"
include "wa.mm"
include "cee.mm"
include "cfv.mm"
include "wrex.mm"
include "w3a.mm"
include "cn.mm"
include "wcel.mm"
include "opex.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "3anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "3anbi2d.mm"
include "df-segle.mm"
include "brab.mm"
include "vex.mm"
include "opth.mm"
include "biid.mm"
include "3anbi123i.mm"
include "2rexbii.mm"
include "rexbii.mm"
include "wi.mm"
include "simpl2l.mm"
include "ad2antrl.mm"
include "eleenn.mm"
include "syl.mm"
include "simprlr.mm"
include "simprll.mm"
include "adantl.mm"
include "axdimuniq.mm"
include "syl22anc.mm"
include "fveq2d.mm"
include "rexeqdv.mm"
include "exbiri.mm"
include "anassrs.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "anbi2d.mm"
include "opeq12.mm"
include "breq1d.mm"
include "breq2d.mm"
include "wb.mm"
include "opeq1.mm"
include "adantr.mm"
include "anbi12d.mm"
include "sylan9bb.mm"
include "imbi1d.mm"
include "3imtr4d.mm"
include "com12.mm"
include "expd.mm"
include "3impd.mm"
include "expr.mm"
include "rexlimdvv.mm"
include "rexlimdvva.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "eqidd.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "3anbi23d.mm"
include "opeq2.mm"
include "anbi1d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "3anbi13d.mm"
include "syl3anc.mm"
include "fveq2.mm"
include "3anbi3d.mm"
include "rexeqbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem brsegle
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q

  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint N y
  disjoint A a
  disjoint a b
  disjoint A b
  disjoint a c
  disjoint A c
  disjoint a d
  disjoint A d
  disjoint a n
  disjoint A n
  disjoint a p
  disjoint A p
  disjoint a q
  disjoint A q
  disjoint a y
  disjoint B a
  disjoint B b
  disjoint b c
  disjoint B c
  disjoint b d
  disjoint B d
  disjoint b n
  disjoint B n
  disjoint b p
  disjoint B p
  disjoint b q
  disjoint B q
  disjoint b y
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint c d
  disjoint C d
  disjoint c n
  disjoint C n
  disjoint c p
  disjoint C p
  disjoint c q
  disjoint C q
  disjoint c y
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint d n
  disjoint D n
  disjoint d p
  disjoint D p
  disjoint d q
  disjoint D q
  disjoint d y
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N n
  disjoint n p
  disjoint n q
  disjoint n y
  disjoint p q
  disjoint p y
  disjoint q y
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Seg<_ <. C , D >. <-> E. y e. ( EE ` N ) ( y Btwn <. C , D >. /\ <. A , B >. Cgr <. C , y >. ) ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    csegle
    wbr
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    @0
    wceq
    #
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    @1
    wceq
    #
    vy
    cv
    #
    @8
    cbtwn
    wbr
    #
    @4
    @6
    @10
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vy
    vn
    cv
    #
    cee
    cfv
    #
    wrex
    #
    w3a
    #
    vd
    @16
    wrex
    #
    vc
    @16
    wrex
    #
    vb
    @16
    wrex
    #
    va
    @16
    wrex
    #
    vn
    cn
    wrex
    #
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @25
    wcel
    #
    wa
    #
    cC
    @25
    wcel
    #
    cD
    @25
    wcel
    #
    wa
    #
    w3a
    #
    @10
    @1
    cbtwn
    wbr
    #
    @0
    cC
    @10
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vy
    @25
    wrex
    #
    vp
    cv
    #
    @4
    wceq
    #
    vq
    cv
    #
    @8
    wceq
    #
    @17
    w3a
    #
    vd
    @16
    wrex
    #
    vc
    @16
    wrex
    vb
    @16
    wrex
    #
    va
    @16
    wrex
    vn
    cn
    wrex
    @5
    @41
    @17
    w3a
    #
    vd
    @16
    wrex
    #
    vc
    @16
    wrex
    vb
    @16
    wrex
    #
    va
    @16
    wrex
    vn
    cn
    wrex
    @23
    vp
    vq
    @0
    @1
    csegle
    cA
    cB
    opex
    cC
    cD
    opex
    @38
    @0
    wceq
    #
    @44
    @47
    vn
    va
    cn
    @16
    @48
    @43
    @46
    vb
    vc
    @16
    @16
    @48
    @42
    @45
    vd
    @16
    @48
    @39
    @5
    @41
    @17
    @48
    @39
    @0
    @4
    wceq
    @5
    @38
    @0
    @4
    eqeq1
    @0
    @4
    eqcom
    syl6bb
    3anbi1d
    rexbidv
    2rexbidv
    2rexbidv
    @40
    @1
    wceq
    #
    @47
    @21
    vn
    va
    cn
    @16
    @49
    @46
    @19
    vb
    vc
    @16
    @16
    @49
    @45
    @18
    vd
    @16
    @49
    @41
    @9
    @5
    @17
    @49
    @41
    @1
    @8
    wceq
    @9
    @40
    @1
    @8
    eqeq1
    @1
    @8
    eqcom
    syl6bb
    3anbi2d
    rexbidv
    2rexbidv
    2rexbidv
    vy
    vn
    vq
    vp
    va
    vb
    vc
    vd
    df-segle
    brab
    @32
    @23
    @37
    @23
    @2
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wa
    #
    @6
    cC
    wceq
    #
    @7
    cD
    wceq
    #
    wa
    #
    @17
    w3a
    #
    vd
    @16
    wrex
    vc
    @16
    wrex
    #
    vb
    @16
    wrex
    va
    @16
    wrex
    #
    vn
    cn
    wrex
    @32
    @37
    @22
    @58
    vn
    cn
    @20
    @57
    va
    vb
    @16
    @16
    @18
    @56
    vc
    vd
    @16
    @16
    @5
    @52
    @9
    @55
    @17
    @17
    @2
    @3
    cA
    cB
    va
    vex
    vb
    vex
    opth
    @6
    @7
    cC
    cD
    vc
    vex
    vd
    vex
    opth
    @17
    biid
    3anbi123i
    2rexbii
    2rexbii
    rexbii
    @32
    @58
    @37
    vn
    cn
    @32
    @15
    cn
    wcel
    #
    wa
    #
    @57
    @37
    va
    vb
    @16
    @16
    @60
    @2
    @16
    wcel
    #
    @3
    @16
    wcel
    #
    wa
    #
    wa
    @56
    @37
    vc
    vd
    @16
    @16
    @60
    @63
    @6
    @16
    wcel
    #
    @7
    @16
    wcel
    #
    wa
    #
    @56
    @37
    wi
    @60
    @63
    @66
    wa
    #
    wa
    #
    @52
    @55
    @17
    @37
    @68
    @52
    @55
    @17
    @37
    wi
    #
    @52
    @55
    wa
    #
    @68
    @69
    @70
    @60
    cA
    @16
    wcel
    #
    cB
    @16
    wcel
    #
    wa
    #
    cC
    @16
    wcel
    #
    cD
    @16
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    @36
    vy
    @16
    wrex
    #
    @37
    wi
    #
    @68
    @69
    @50
    @51
    @55
    @78
    @80
    wi
    @50
    @51
    @55
    wa
    wa
    #
    @78
    @37
    @79
    @81
    @78
    wa
    #
    @36
    vy
    @25
    @16
    @82
    cN
    @15
    cee
    @82
    @24
    @26
    @59
    @71
    cN
    @15
    wceq
    @82
    @26
    @24
    @60
    @26
    @81
    @77
    @26
    @27
    @24
    @31
    @59
    simpl2l
    ad2antrl
    #
    cA
    cN
    eleenn
    syl
    @83
    @81
    @32
    @59
    @77
    simprlr
    @78
    @71
    @81
    @60
    @71
    @72
    @76
    simprll
    adantl
    cA
    @15
    cN
    axdimuniq
    syl22anc
    fveq2d
    rexeqdv
    exbiri
    anassrs
    @70
    @67
    @77
    @60
    @52
    @63
    @73
    @55
    @66
    @76
    @50
    @61
    @71
    @51
    @62
    @72
    @2
    cA
    @16
    eleq1
    @3
    cB
    @16
    eleq1
    bi2anan9
    @53
    @64
    @74
    @54
    @65
    @75
    @6
    cC
    @16
    eleq1
    @7
    cD
    @16
    eleq1
    bi2anan9
    bi2anan9
    anbi2d
    @70
    @17
    @79
    @37
    @70
    @14
    @36
    vy
    @16
    @52
    @14
    @11
    @0
    @12
    ccgr
    wbr
    #
    wa
    #
    @55
    @36
    @52
    @13
    @84
    @11
    @52
    @4
    @0
    @12
    ccgr
    @2
    @3
    cA
    cB
    opeq12
    breq1d
    anbi2d
    @55
    @11
    @33
    @84
    @35
    @55
    @8
    @1
    @10
    cbtwn
    @6
    @7
    cC
    cD
    opeq12
    breq2d
    @53
    @84
    @35
    wb
    @54
    @53
    @12
    @34
    @0
    ccgr
    @6
    cC
    @10
    opeq1
    breq2d
    #
    adantr
    anbi12d
    sylan9bb
    rexbidv
    imbi1d
    3imtr4d
    com12
    expd
    3impd
    expr
    rexlimdvv
    rexlimdvva
    rexlimdva
    syl5bi
    @32
    @37
    @23
    @32
    @37
    wa
    #
    @24
    @5
    @9
    @14
    vy
    @25
    wrex
    #
    w3a
    #
    vd
    @25
    wrex
    #
    vc
    @25
    wrex
    #
    vb
    @25
    wrex
    #
    va
    @25
    wrex
    #
    @23
    @24
    @28
    @31
    @37
    simpl1
    @87
    @26
    @27
    @0
    @0
    wceq
    #
    @9
    @85
    vy
    @25
    wrex
    #
    w3a
    #
    vd
    @25
    wrex
    vc
    @25
    wrex
    #
    @93
    @26
    @27
    @24
    @31
    @37
    simpl2l
    @26
    @27
    @24
    @31
    @37
    simpl2r
    @87
    @29
    @30
    @94
    @1
    @1
    wceq
    #
    @37
    @97
    @29
    @30
    @24
    @28
    @37
    simpl3l
    @29
    @30
    @24
    @28
    @37
    simpl3r
    @87
    @0
    eqidd
    @87
    @1
    eqidd
    @32
    @37
    simpr
    @96
    @94
    @98
    @37
    w3a
    @94
    cC
    @7
    cop
    #
    @1
    wceq
    #
    @10
    @99
    cbtwn
    wbr
    #
    @35
    wa
    #
    vy
    @25
    wrex
    #
    w3a
    vc
    vd
    cC
    cD
    @25
    @25
    @53
    @9
    @100
    @95
    @103
    @94
    @53
    @8
    @99
    @1
    @6
    cC
    @7
    opeq1
    #
    eqeq1d
    @53
    @85
    @102
    vy
    @25
    @53
    @11
    @101
    @84
    @35
    @53
    @8
    @99
    @10
    cbtwn
    @104
    breq2d
    @86
    anbi12d
    rexbidv
    3anbi23d
    @54
    @100
    @98
    @103
    @37
    @94
    @54
    @99
    @1
    @1
    @7
    cD
    cC
    opeq2
    #
    eqeq1d
    @54
    @102
    @36
    vy
    @25
    @54
    @101
    @33
    @35
    @54
    @99
    @1
    @10
    cbtwn
    @105
    breq2d
    anbi1d
    rexbidv
    3anbi23d
    rspc2ev
    syl113anc
    @91
    @97
    cA
    @3
    cop
    #
    @0
    wceq
    #
    @9
    @11
    @106
    @12
    ccgr
    wbr
    #
    wa
    #
    vy
    @25
    wrex
    #
    w3a
    #
    vd
    @25
    wrex
    vc
    @25
    wrex
    va
    vb
    cA
    cB
    @25
    @25
    @50
    @89
    @111
    vc
    vd
    @25
    @25
    @50
    @5
    @107
    @88
    @110
    @9
    @50
    @4
    @106
    @0
    @2
    cA
    @3
    opeq1
    #
    eqeq1d
    @50
    @14
    @109
    vy
    @25
    @50
    @13
    @108
    @11
    @50
    @4
    @106
    @12
    ccgr
    @112
    breq1d
    anbi2d
    rexbidv
    3anbi13d
    2rexbidv
    @51
    @111
    @96
    vc
    vd
    @25
    @25
    @51
    @107
    @94
    @110
    @95
    @9
    @51
    @106
    @0
    @0
    @3
    cB
    cA
    opeq2
    #
    eqeq1d
    @51
    @109
    @85
    vy
    @25
    @51
    @108
    @84
    @11
    @51
    @106
    @0
    @12
    ccgr
    @113
    breq1d
    anbi2d
    rexbidv
    3anbi13d
    2rexbidv
    rspc2ev
    syl3anc
    @22
    @93
    vn
    cN
    cn
    @15
    cN
    wceq
    #
    @21
    @92
    va
    @16
    @25
    @15
    cN
    cee
    fveq2
    #
    @114
    @20
    @91
    vb
    @16
    @25
    @115
    @114
    @19
    @90
    vc
    @16
    @25
    @115
    @114
    @18
    @89
    vd
    @16
    @25
    @115
    @114
    @17
    @88
    @5
    @9
    @114
    @14
    vy
    @16
    @25
    @115
    rexeqdv
    3anbi3d
    rexeqbidv
    rexeqbidv
    rexeqbidv
    rexeqbidv
    rspcev
    syl2anc
    ex
    impbid
    syl5bb
end
