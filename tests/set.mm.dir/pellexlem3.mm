include "cn.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "copab.mm"
include "cvv.mm"
include "cdenom.mm"
include "cneg.mm"
include "crab.mm"
include "cdom.mm"
include "cxp.mm"
include "nnex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "cnumer.mm"
include "cop.mm"
include "simprl.mm"
include "simprrl.mm"
include "qgt0numnn.mm"
include "syl2anc.mm"
include "qdencl.mm"
include "syl.mm"
include "jca.mm"
include "simpll.mm"
include "simplr.mm"
include "pellexlem1.mm"
include "syl31anc.mm"
include "cdiv.mm"
include "simprrr.mm"
include "wb.mm"
include "qeqnumdivden.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "mpbid.mm"
include "pellexlem2.mm"
include "jca32.mm"
include "ex.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "fvex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "neeq1d.mm"
include "anbi2d.mm"
include "oveq2d.mm"
include "opelopab.mm"
include "3imtr4g.mm"
include "ssrab2.mm"
include "sseldi.mm"
include "simprr.mm"
include "opth.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "syl5bi.mm"
include "opeq12d.mm"
include "impbid1.mm"
include "dom2d.mm"
include "mpi.mm"

theorem pellexlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let wph: wff ph

  disjoint D x
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint A e
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint g x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint g y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint g z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  assert |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> { x e. QQ | ( 0 < x /\ ( abs ` ( x - ( sqrt ` D ) ) ) < ( ( denom ` x ) ^ -u 2 ) ) } ~<_ { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) =/= 0 /\ ( abs ` ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) ) < ( 1 + ( 2 x. ( sqrt ` D ) ) ) ) ) } )

  proof
    cD
    cn
    wcel
    #
    cD
    csqrt
    cfv
    #
    cq
    wcel
    wn
    #
    wa
    #
    vy
    cv
    #
    cn
    wcel
    #
    vz
    cv
    #
    cn
    wcel
    #
    wa
    #
    @4
    c2
    cexp
    co
    #
    cD
    @6
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wne
    #
    @12
    cabs
    cfv
    #
    c1
    c2
    @1
    cmul
    co
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    wa
    #
    vy
    vz
    copab
    #
    cvv
    wcel
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    @20
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @20
    cdenom
    cfv
    #
    c2
    cneg
    #
    cexp
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cq
    crab
    #
    @19
    cdom
    wbr
    @19
    cn
    cn
    cxp
    cn
    cn
    nnex
    nnex
    xpex
    @17
    vy
    vz
    cn
    cn
    opabssxp
    ssexi
    @3
    va
    vb
    @29
    @19
    va
    cv
    #
    cnumer
    cfv
    #
    @30
    cdenom
    cfv
    #
    cop
    #
    vb
    cv
    #
    cnumer
    cfv
    #
    @34
    cdenom
    cfv
    #
    cop
    #
    cvv
    @3
    @30
    cq
    wcel
    #
    cc0
    @30
    clt
    wbr
    #
    @30
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @32
    @25
    cexp
    co
    #
    clt
    wbr
    #
    wa
    #
    wa
    #
    @31
    cn
    wcel
    #
    @32
    cn
    wcel
    #
    wa
    #
    @31
    c2
    cexp
    co
    #
    cD
    @32
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wne
    #
    @52
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    wa
    #
    wa
    #
    @30
    @29
    wcel
    #
    @33
    @19
    wcel
    @3
    @45
    @57
    @3
    @45
    wa
    #
    @48
    @53
    @55
    @59
    @46
    @47
    @59
    @38
    @39
    @46
    @3
    @38
    @44
    simprl
    #
    @3
    @38
    @39
    @43
    simprrl
    @30
    qgt0numnn
    syl2anc
    #
    @59
    @38
    @47
    @60
    @30
    qdencl
    syl
    #
    jca
    @59
    @0
    @46
    @47
    @2
    @53
    @0
    @2
    @45
    simpll
    #
    @61
    @62
    @0
    @2
    @45
    simplr
    @31
    @32
    cD
    pellexlem1
    syl31anc
    @59
    @0
    @46
    @47
    @31
    @32
    cdiv
    co
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @42
    clt
    wbr
    #
    @55
    @63
    @61
    @62
    @59
    @43
    @67
    @3
    @38
    @39
    @43
    simprrr
    @59
    @38
    @43
    @67
    wb
    @60
    @38
    @41
    @66
    @42
    clt
    @38
    @40
    @65
    cabs
    @38
    @30
    @64
    @1
    cmin
    @30
    qeqnumdivden
    #
    oveq1d
    fveq2d
    breq1d
    syl
    mpbid
    @31
    @32
    cD
    pellexlem2
    syl31anc
    jca32
    ex
    @28
    @44
    vx
    @30
    cq
    @20
    @30
    wceq
    #
    @21
    @39
    @27
    @43
    @20
    @30
    cc0
    clt
    breq2
    @69
    @23
    @41
    @26
    @42
    clt
    @69
    @22
    @40
    cabs
    @20
    @30
    @1
    cmin
    oveq1
    fveq2d
    @69
    @24
    @32
    @25
    cexp
    @20
    @30
    cdenom
    fveq2
    oveq1d
    breq12d
    anbi12d
    elrab
    @18
    @46
    @7
    wa
    #
    @49
    @11
    cmin
    co
    #
    cc0
    wne
    #
    @71
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    wa
    #
    wa
    @57
    vy
    vz
    @31
    @32
    @30
    cnumer
    fvex
    #
    @30
    cdenom
    fvex
    #
    @4
    @31
    wceq
    #
    @8
    @70
    @17
    @75
    @78
    @5
    @46
    @7
    @4
    @31
    cn
    eleq1
    anbi1d
    @78
    @13
    @72
    @16
    @74
    @78
    @12
    @71
    cc0
    @78
    @9
    @49
    @11
    cmin
    @4
    @31
    c2
    cexp
    oveq1
    oveq1d
    #
    neeq1d
    @78
    @14
    @73
    @15
    clt
    @78
    @12
    @71
    cabs
    @79
    fveq2d
    breq1d
    anbi12d
    anbi12d
    @6
    @32
    wceq
    #
    @70
    @48
    @75
    @56
    @80
    @7
    @47
    @46
    @6
    @32
    cn
    eleq1
    anbi2d
    @80
    @72
    @53
    @74
    @55
    @80
    @71
    @52
    cc0
    @80
    @11
    @51
    @49
    cmin
    @80
    @10
    @50
    cD
    cmul
    @6
    @32
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    #
    neeq1d
    @80
    @73
    @54
    @15
    clt
    @80
    @71
    @52
    cabs
    @81
    fveq2d
    breq1d
    anbi12d
    anbi12d
    opelopab
    3imtr4g
    @3
    @58
    @34
    @29
    wcel
    #
    wa
    #
    @33
    @37
    wceq
    #
    @30
    @34
    wceq
    #
    wb
    #
    @3
    @83
    wa
    #
    @38
    @34
    cq
    wcel
    #
    @86
    @87
    @29
    cq
    @30
    @28
    vx
    cq
    ssrab2
    #
    @3
    @58
    @82
    simprl
    sseldi
    @87
    @29
    cq
    @34
    @89
    @3
    @58
    @82
    simprr
    sseldi
    @38
    @88
    wa
    #
    @84
    @85
    @84
    @31
    @35
    wceq
    #
    @32
    @36
    wceq
    #
    wa
    #
    @90
    @85
    @31
    @32
    @35
    @36
    @76
    @77
    opth
    @90
    @93
    @85
    @90
    @93
    wa
    #
    @64
    @35
    @36
    cdiv
    co
    #
    @30
    @34
    @94
    @31
    @35
    @32
    @36
    cdiv
    @90
    @91
    @92
    simprl
    @90
    @91
    @92
    simprr
    oveq12d
    @94
    @38
    @30
    @64
    wceq
    @38
    @88
    @93
    simpll
    @68
    syl
    @94
    @88
    @34
    @95
    wceq
    @38
    @88
    @93
    simplr
    @34
    qeqnumdivden
    syl
    3eqtr4d
    ex
    syl5bi
    @85
    @31
    @35
    @32
    @36
    @30
    @34
    cnumer
    fveq2
    @30
    @34
    cdenom
    fveq2
    opeq12d
    impbid1
    syl2anc
    ex
    dom2d
    mpi
end
