include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "csqrt.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "cfz.mm"
include "cr.mm"
include "axsegconlem4.mm"
include "ad2antlr.mm"
include "simpl1.mm"
include "fveere.mm"
include "sylan.mm"
include "remulcld.mm"
include "recnd.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "axsegconlem8.mm"
include "readdcl.mm"
include "syl2an.mm"
include "adantr.mm"
include "cc0.mm"
include "0red.mm"
include "clt.mm"
include "wbr.mm"
include "axsegconlem6.mm"
include "cle.mm"
include "axsegconlem5.mm"
include "adantl.mm"
include "wb.mm"
include "addge01.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "divdird.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "simpl2.mm"
include "resubcld.mm"
include "divcan2d.mm"
include "eqtrd.mm"
include "pncan3d.mm"
include "readdcld.mm"
include "divmul2d.mm"
include "mpbird.mm"
include "cc.mm"
include "div23d.mm"
include "divsubdird.mm"
include "pncan2.mm"
include "dividd.mm"
include "3eqtr3d.mm"
include "ralrimiva.mm"

theorem axsegconlem10
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vp: setvar p
  assume axsegconlem2.1: |- S = sum_ p e. ( 1 ... N ) ( ( ( A ` p ) - ( B ` p ) ) ^ 2 )
  assume axsegconlem7.2: |- T = sum_ p e. ( 1 ... N ) ( ( ( C ` p ) - ( D ` p ) ) ^ 2 )
  assume axsegconlem8.3: |- F = ( k e. ( 1 ... N ) |-> ( ( ( ( ( sqrt ` S ) + ( sqrt ` T ) ) x. ( B ` k ) ) - ( ( sqrt ` T ) x. ( A ` k ) ) ) / ( sqrt ` S ) ) )

  disjoint A i
  disjoint A k
  disjoint i k
  disjoint B i
  disjoint B k
  disjoint C i
  disjoint C k
  disjoint D i
  disjoint D k
  disjoint N i
  disjoint N k
  disjoint S i
  disjoint S k
  disjoint T i
  disjoint T k
  disjoint i p
  disjoint A p
  disjoint B p
  disjoint C p
  disjoint D p
  disjoint N p
  assert |- ( ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - ( ( sqrt ` S ) / ( ( sqrt ` S ) + ( sqrt ` T ) ) ) ) x. ( A ` i ) ) + ( ( ( sqrt ` S ) / ( ( sqrt ` S ) + ( sqrt ` T ) ) ) x. ( F ` i ) ) ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cC
    @0
    wcel
    cD
    @0
    wcel
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
    cS
    csqrt
    cfv
    #
    @9
    cT
    csqrt
    cfv
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @7
    cA
    cfv
    #
    cmul
    co
    #
    @12
    @7
    cF
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    vi
    c1
    cN
    cfz
    co
    #
    @6
    @7
    @19
    wcel
    #
    wa
    #
    @10
    @14
    cmul
    co
    #
    @9
    @16
    cmul
    co
    #
    caddc
    co
    #
    @11
    cdiv
    co
    #
    @22
    @11
    cdiv
    co
    #
    @23
    @11
    cdiv
    co
    #
    caddc
    co
    @8
    @18
    @21
    @22
    @23
    @11
    @21
    @22
    @21
    @10
    @14
    @5
    @10
    cr
    wcel
    #
    @4
    @20
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem4
    #
    ad2antlr
    @6
    @1
    @20
    @14
    cr
    wcel
    @1
    @2
    @3
    @5
    simpl1
    cA
    @7
    cN
    fveere
    sylan
    #
    remulcld
    #
    recnd
    #
    @21
    @23
    @21
    @9
    @16
    @4
    @9
    cr
    wcel
    #
    @5
    @20
    @1
    @2
    @33
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem4
    3adant3
    #
    ad2antrr
    #
    @6
    cF
    @0
    wcel
    @20
    @16
    cr
    wcel
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cF
    cN
    vp
    axsegconlem2.1
    axsegconlem7.2
    axsegconlem8.3
    axsegconlem8
    cF
    @7
    cN
    fveere
    sylan
    #
    remulcld
    #
    recnd
    @21
    @11
    @6
    @11
    cr
    wcel
    #
    @20
    @4
    @33
    @28
    @38
    @5
    @34
    @29
    @9
    @10
    readdcl
    syl2an
    #
    adantr
    #
    recnd
    #
    @6
    @11
    cc0
    wne
    @20
    @6
    @11
    @6
    cc0
    @9
    @11
    @6
    0red
    @4
    @33
    @5
    @34
    adantr
    @39
    @4
    cc0
    @9
    clt
    wbr
    @5
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem6
    #
    adantr
    @6
    cc0
    @10
    cle
    wbr
    #
    @9
    @11
    cle
    wbr
    #
    @5
    @43
    @4
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem5
    adantl
    @4
    @33
    @28
    @43
    @44
    wb
    @5
    @34
    @29
    @9
    @10
    addge01
    syl2an
    mpbid
    ltletrd
    gt0ne0d
    adantr
    #
    divdird
    @21
    @25
    @8
    wceq
    @24
    @11
    @8
    cmul
    co
    #
    wceq
    @21
    @24
    @22
    @46
    @22
    cmin
    co
    #
    caddc
    co
    @46
    @21
    @23
    @47
    @22
    caddc
    @21
    @23
    @9
    @47
    @9
    cdiv
    co
    #
    cmul
    co
    @47
    @21
    @16
    @48
    @9
    cmul
    @20
    @16
    @48
    wceq
    @6
    vk
    @7
    @11
    vk
    cv
    #
    cB
    cfv
    #
    cmul
    co
    #
    @10
    @49
    cA
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @9
    cdiv
    co
    @48
    @19
    cF
    vk
    vi
    weq
    #
    @54
    @47
    @9
    cdiv
    @55
    @51
    @46
    @53
    @22
    cmin
    @55
    @50
    @8
    @11
    cmul
    @49
    @7
    cB
    fveq2
    oveq2d
    @55
    @52
    @14
    @10
    cmul
    @49
    @7
    cA
    fveq2
    oveq2d
    oveq12d
    oveq1d
    axsegconlem8.3
    @47
    @9
    cdiv
    ovex
    fvmpt
    adantl
    oveq2d
    @21
    @47
    @9
    @21
    @47
    @21
    @46
    @22
    @21
    @11
    @8
    @40
    @6
    @2
    @20
    @8
    cr
    wcel
    @1
    @2
    @3
    @5
    simpl2
    cB
    @7
    cN
    fveere
    sylan
    #
    remulcld
    #
    @31
    resubcld
    recnd
    @21
    @9
    @35
    recnd
    #
    @4
    @9
    cc0
    wne
    @5
    @20
    @4
    @9
    @42
    gt0ne0d
    ad2antrr
    divcan2d
    eqtrd
    oveq2d
    @21
    @22
    @46
    @32
    @21
    @46
    @57
    recnd
    pncan3d
    eqtrd
    @21
    @24
    @8
    @11
    @21
    @24
    @21
    @22
    @23
    @31
    @37
    readdcld
    recnd
    @21
    @8
    @56
    recnd
    @41
    @45
    divmul2d
    mpbird
    @21
    @26
    @15
    @27
    @17
    caddc
    @21
    @26
    @10
    @11
    cdiv
    co
    #
    @14
    cmul
    co
    @15
    @21
    @10
    @14
    @11
    @5
    @10
    cc
    wcel
    #
    @4
    @20
    @5
    @10
    @29
    recnd
    #
    ad2antlr
    @21
    @14
    @30
    recnd
    @41
    @45
    div23d
    @21
    @59
    @13
    @14
    cmul
    @21
    @11
    @9
    cmin
    co
    #
    @11
    cdiv
    co
    @11
    @11
    cdiv
    co
    #
    @12
    cmin
    co
    @59
    @13
    @21
    @11
    @9
    @11
    @41
    @58
    @41
    @45
    divsubdird
    @21
    @62
    @10
    @11
    cdiv
    @6
    @62
    @10
    wceq
    #
    @20
    @4
    @9
    cc
    wcel
    @60
    @64
    @5
    @4
    @9
    @34
    recnd
    @61
    @9
    @10
    pncan2
    syl2an
    adantr
    oveq1d
    @21
    @63
    c1
    @12
    cmin
    @21
    @11
    @41
    @45
    dividd
    oveq1d
    3eqtr3d
    oveq1d
    eqtrd
    @21
    @9
    @16
    @11
    @58
    @21
    @16
    @36
    recnd
    @41
    @45
    div23d
    oveq12d
    3eqtr3d
    ralrimiva
end
