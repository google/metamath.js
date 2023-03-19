include "wceq.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cfz.mm"
include "wral.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "w3a.mm"
include "cmpt.mm"
include "cr.mm"
include "fveere.mm"
include "3ad2antl1.mm"
include "3ad2antl2.mm"
include "3ad2antl3.mm"
include "resubcld.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cn.mm"
include "eleenn.mm"
include "mptelee.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "cc.mm"
include "fveecn.mm"
include "1m0e1.mm"
include "oveq1i.mm"
include "mulid2.mm"
include "syl5eq.mm"
include "subcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "mul02d.mm"
include "oveq12d.mm"
include "addid1.mm"
include "eqtr2d.mm"
include "syl3anc.mm"
include "subcld.mm"
include "nncand.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "0elunit.mm"
include "fveq1.mm"
include "weq.mm"
include "fveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "ralbidva.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "anbi1d.mm"
include "rspc2ev.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "3expb.mm"
include "adantll.mm"
include "2rexbidv.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem axsegconlem1
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cN: class N
  let vk: setvar k

  disjoint N t
  disjoint N i
  disjoint N x
  disjoint i t
  disjoint t x
  disjoint i x
  disjoint A t
  disjoint A i
  disjoint A x
  disjoint B t
  disjoint B i
  disjoint B x
  disjoint C t
  disjoint C i
  disjoint C x
  disjoint D t
  disjoint D i
  disjoint D x
  disjoint N k
  disjoint k t
  disjoint i k
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  assert |- ( ( A = B /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ) -> E. x e. ( EE ` N ) E. t e. ( 0 [,] 1 ) ( A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - t ) x. ( A ` i ) ) + ( t x. ( x ` i ) ) ) /\ sum_ i e. ( 1 ... N ) ( ( ( B ` i ) - ( x ` i ) ) ^ 2 ) = sum_ i e. ( 1 ... N ) ( ( ( C ` i ) - ( D ` i ) ) ^ 2 ) ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    wa
    #
    vi
    cv
    #
    cB
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @8
    cA
    cfv
    #
    cmul
    co
    #
    @10
    @8
    vx
    cv
    #
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    @19
    @9
    @15
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
    @19
    @8
    cC
    cfv
    #
    @8
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
    wa
    #
    vt
    cc0
    c1
    cicc
    co
    #
    wrex
    vx
    @1
    wrex
    #
    @7
    @32
    @0
    @9
    @11
    @9
    cmul
    co
    #
    @16
    caddc
    co
    #
    wceq
    #
    vi
    @19
    wral
    #
    @29
    wa
    #
    vt
    @31
    wrex
    vx
    @1
    wrex
    #
    @3
    @6
    @38
    @2
    @3
    @4
    @5
    @38
    @3
    @4
    @5
    w3a
    #
    vk
    @19
    vk
    cv
    #
    cB
    cfv
    #
    @40
    cC
    cfv
    #
    @40
    cD
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    cmpt
    #
    @1
    wcel
    #
    @9
    c1
    cc0
    cmin
    co
    #
    @9
    cmul
    co
    #
    cc0
    @9
    @26
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @19
    wral
    #
    @19
    @9
    @50
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
    @28
    wceq
    #
    @38
    @39
    @47
    @45
    cr
    wcel
    #
    vk
    @19
    wral
    #
    @39
    @59
    vk
    @19
    @39
    @40
    @19
    wcel
    #
    wa
    #
    @41
    @44
    @3
    @4
    @61
    @41
    cr
    wcel
    @5
    cB
    @40
    cN
    fveere
    3ad2antl1
    @62
    @42
    @43
    @4
    @3
    @61
    @42
    cr
    wcel
    @5
    cC
    @40
    cN
    fveere
    3ad2antl2
    @5
    @3
    @61
    @43
    cr
    wcel
    @4
    cD
    @40
    cN
    fveere
    3ad2antl3
    resubcld
    resubcld
    ralrimiva
    @3
    @4
    @47
    @60
    wb
    #
    @5
    @3
    cN
    cn
    wcel
    @63
    cB
    cN
    eleenn
    @41
    @44
    vk
    cmin
    cN
    mptelee
    syl
    3ad2ant1
    mpbird
    @39
    @53
    vi
    @19
    @39
    @8
    @19
    wcel
    #
    wa
    #
    @9
    cc
    wcel
    #
    @24
    cc
    wcel
    #
    @25
    cc
    wcel
    #
    @53
    @3
    @4
    @64
    @66
    @5
    cB
    @8
    cN
    fveecn
    3ad2antl1
    #
    @4
    @3
    @64
    @67
    @5
    cC
    @8
    cN
    fveecn
    3ad2antl2
    #
    @5
    @3
    @64
    @68
    @4
    cD
    @8
    cN
    fveecn
    3ad2antl3
    #
    @66
    @67
    @68
    w3a
    #
    @52
    @9
    cc0
    caddc
    co
    #
    @9
    @72
    @49
    @9
    @51
    cc0
    caddc
    @72
    @49
    c1
    @9
    cmul
    co
    #
    @9
    @48
    c1
    @9
    cmul
    1m0e1
    oveq1i
    @66
    @67
    @74
    @9
    wceq
    @68
    @9
    mulid2
    3ad2ant1
    syl5eq
    @72
    @50
    @66
    @67
    @68
    @50
    cc
    wcel
    #
    @67
    @68
    wa
    @66
    @26
    cc
    wcel
    @75
    @24
    @25
    subcl
    @9
    @26
    subcl
    sylan2
    3impb
    mul02d
    oveq12d
    @66
    @67
    @73
    @9
    wceq
    @68
    @9
    addid1
    3ad2ant1
    eqtr2d
    syl3anc
    ralrimiva
    @39
    @19
    @56
    @27
    vi
    @65
    @55
    @26
    c2
    cexp
    @65
    @9
    @26
    @69
    @65
    @24
    @25
    @70
    @71
    subcld
    nncand
    oveq1d
    sumeq2dv
    @47
    cc0
    @31
    wcel
    @54
    @58
    wa
    #
    @38
    0elunit
    @37
    @76
    @9
    @33
    @10
    @50
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @19
    wral
    #
    @58
    wa
    vx
    vt
    @46
    cc0
    @1
    @31
    @14
    @46
    wceq
    #
    @36
    @80
    @29
    @58
    @81
    @35
    @79
    vi
    @19
    @81
    @64
    wa
    #
    @34
    @78
    @9
    @82
    @16
    @77
    @33
    caddc
    @82
    @15
    @50
    @10
    cmul
    @81
    @64
    @15
    @8
    @46
    cfv
    @50
    @8
    @14
    @46
    fveq1
    vk
    @8
    @45
    @50
    @19
    @46
    vk
    vi
    weq
    #
    @41
    @9
    @44
    @26
    cmin
    @40
    @8
    cB
    fveq2
    @83
    @42
    @24
    @43
    @25
    cmin
    @40
    @8
    cC
    fveq2
    @40
    @8
    cD
    fveq2
    oveq12d
    oveq12d
    @46
    eqid
    @9
    @26
    cmin
    ovex
    fvmpt
    sylan9eq
    #
    oveq2d
    oveq2d
    eqeq2d
    ralbidva
    @81
    @23
    @57
    @28
    @81
    @19
    @22
    @56
    vi
    @82
    @21
    @55
    c2
    cexp
    @82
    @15
    @50
    @9
    cmin
    @84
    oveq2d
    oveq1d
    sumeq2dv
    eqeq1d
    anbi12d
    @10
    cc0
    wceq
    #
    @80
    @54
    @58
    @85
    @79
    @53
    vi
    @19
    @85
    @78
    @52
    @9
    @85
    @33
    @49
    @77
    @51
    caddc
    @85
    @11
    @48
    @9
    cmul
    @10
    cc0
    c1
    cmin
    oveq2
    oveq1d
    @10
    cc0
    @50
    cmul
    oveq1
    oveq12d
    eqeq2d
    ralbidv
    anbi1d
    rspc2ev
    mp3an2
    syl12anc
    3expb
    adantll
    @0
    @30
    @37
    vx
    vt
    @1
    @31
    @0
    @20
    @36
    @29
    @0
    @18
    @35
    vi
    @19
    @0
    @17
    @34
    @9
    @0
    @13
    @33
    @16
    caddc
    @0
    @12
    @9
    @11
    cmul
    @8
    cA
    cB
    fveq1
    oveq2d
    oveq1d
    eqeq2d
    ralbidv
    anbi1d
    2rexbidv
    syl5ibr
    imp
end
