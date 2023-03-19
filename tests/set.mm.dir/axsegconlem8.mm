include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csqrt.mm"
include "caddc.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cr.mm"
include "wral.mm"
include "axsegconlem4.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "readdcld.mm"
include "simpl2.mm"
include "fveere.mm"
include "sylan.mm"
include "remulcld.mm"
include "simpl1.mm"
include "resubcld.mm"
include "cc0.mm"
include "axsegconlem6.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "ralrimiva.mm"
include "cn.mm"
include "wb.mm"
include "eleenn.mm"
include "ad2antll.mm"
include "mptelee.mm"
include "syl.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem axsegconlem8
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vp: setvar p
  let vi: setvar i
  assume axsegconlem2.1: |- S = sum_ p e. ( 1 ... N ) ( ( ( A ` p ) - ( B ` p ) ) ^ 2 )
  assume axsegconlem7.2: |- T = sum_ p e. ( 1 ... N ) ( ( ( C ` p ) - ( D ` p ) ) ^ 2 )
  assume axsegconlem8.3: |- F = ( k e. ( 1 ... N ) |-> ( ( ( ( ( sqrt ` S ) + ( sqrt ` T ) ) x. ( B ` k ) ) - ( ( sqrt ` T ) x. ( A ` k ) ) ) / ( sqrt ` S ) ) )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint N k
  disjoint S k
  disjoint T k
  disjoint A p
  disjoint B p
  disjoint C p
  disjoint D p
  disjoint N p
  disjoint A i
  disjoint i k
  disjoint B i
  disjoint C i
  disjoint D i
  disjoint N i
  disjoint S i
  disjoint T i
  disjoint i p
  assert |- ( ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> F e. ( EE ` N ) )

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
    #
    cD
    @0
    wcel
    #
    wa
    #
    wa
    #
    cF
    vk
    c1
    cN
    cfz
    co
    #
    cS
    csqrt
    cfv
    #
    cT
    csqrt
    cfv
    #
    caddc
    co
    #
    vk
    cv
    #
    cB
    cfv
    #
    cmul
    co
    #
    @11
    @13
    cA
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @10
    cdiv
    co
    #
    cmpt
    #
    @0
    axsegconlem8.3
    @8
    @20
    @0
    wcel
    #
    @19
    cr
    wcel
    #
    vk
    @9
    wral
    #
    @8
    @22
    vk
    @9
    @8
    @13
    @9
    wcel
    #
    wa
    #
    @18
    @10
    @25
    @15
    @17
    @25
    @12
    @14
    @25
    @10
    @11
    @4
    @10
    cr
    wcel
    #
    @7
    @24
    @1
    @2
    @26
    @3
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem4
    3adant3
    ad2antrr
    #
    @7
    @11
    cr
    wcel
    @4
    @24
    cC
    cD
    cT
    cN
    vp
    axsegconlem7.2
    axsegconlem4
    ad2antlr
    #
    readdcld
    @8
    @2
    @24
    @14
    cr
    wcel
    @1
    @2
    @3
    @7
    simpl2
    cB
    @13
    cN
    fveere
    sylan
    remulcld
    @25
    @11
    @16
    @28
    @8
    @1
    @24
    @16
    cr
    wcel
    @1
    @2
    @3
    @7
    simpl1
    cA
    @13
    cN
    fveere
    sylan
    remulcld
    resubcld
    @27
    @4
    @10
    cc0
    wne
    @7
    @24
    @4
    @10
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem6
    gt0ne0d
    ad2antrr
    redivcld
    ralrimiva
    @8
    cN
    cn
    wcel
    #
    @21
    @23
    wb
    @6
    @29
    @4
    @5
    cD
    cN
    eleenn
    ad2antll
    @18
    @10
    vk
    cdiv
    cN
    mptelee
    syl
    mpbird
    syl5eqel
end
