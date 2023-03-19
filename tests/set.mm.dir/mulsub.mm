include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "negsub.mm"
include "oveqan12d.mm"
include "wceq.mm"
include "negcl.mm"
include "muladd.mm"
include "sylanr2.mm"
include "sylanl2.mm"
include "mul2neg.mm"
include "ancoms.mm"
include "oveq2d.mm"
include "ad2ant2l.mm"
include "mulneg2.mm"
include "mulcl.mm"
include "negdi.mm"
include "syl2an.mm"
include "eqtr4d.mm"
include "ancom2s.mm"
include "an42s.mm"
include "oveq12d.mm"
include "addcl.mm"
include "an4s.mm"
include "negsubd.mm"
include "3eqtrd.mm"
include "eqtr3d.mm"

theorem mulsub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A - B ) x. ( C - D ) ) = ( ( ( A x. C ) + ( D x. B ) ) - ( ( A x. D ) + ( C x. B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cC
    cD
    cneg
    #
    caddc
    co
    #
    cmul
    co
    #
    cA
    cB
    cmin
    co
    #
    cC
    cD
    cmin
    co
    #
    cmul
    co
    cA
    cC
    cmul
    co
    #
    cD
    cB
    cmul
    co
    #
    caddc
    co
    #
    cA
    cD
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    caddc
    co
    #
    cmin
    co
    #
    @2
    @5
    @8
    @12
    @10
    @13
    cmul
    cA
    cB
    negsub
    cC
    cD
    negsub
    oveqan12d
    @6
    @11
    @14
    @9
    @7
    cmul
    co
    #
    caddc
    co
    #
    cA
    @9
    cmul
    co
    #
    cC
    @7
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @16
    @19
    cneg
    #
    caddc
    co
    @20
    @1
    @0
    @7
    cc
    wcel
    #
    @5
    @11
    @26
    wceq
    #
    cB
    negcl
    @4
    @0
    @28
    wa
    @3
    @9
    cc
    wcel
    @29
    cD
    negcl
    cA
    @7
    cC
    @9
    muladd
    sylanr2
    sylanl2
    @6
    @22
    @16
    @25
    @27
    caddc
    @1
    @4
    @22
    @16
    wceq
    @0
    @3
    @1
    @4
    wa
    #
    @21
    @15
    @14
    caddc
    @4
    @1
    @21
    @15
    wceq
    cD
    cB
    mul2neg
    ancoms
    oveq2d
    ad2ant2l
    @0
    @4
    @1
    @3
    @25
    @27
    wceq
    #
    @0
    @4
    wa
    #
    @3
    @1
    @31
    @32
    @3
    @1
    wa
    #
    wa
    @25
    @17
    cneg
    #
    @18
    cneg
    #
    caddc
    co
    #
    @27
    @32
    @33
    @23
    @34
    @24
    @35
    caddc
    cA
    cD
    mulneg2
    cC
    cB
    mulneg2
    oveqan12d
    @32
    @17
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @27
    @36
    wceq
    @33
    cA
    cD
    mulcl
    #
    cC
    cB
    mulcl
    #
    @17
    @18
    negdi
    syl2an
    eqtr4d
    ancom2s
    an42s
    oveq12d
    @6
    @16
    @19
    @0
    @3
    @1
    @4
    @16
    cc
    wcel
    #
    @0
    @3
    wa
    @14
    cc
    wcel
    @15
    cc
    wcel
    #
    @41
    @30
    cA
    cC
    mulcl
    @4
    @1
    @42
    cD
    cB
    mulcl
    ancoms
    @14
    @15
    addcl
    syl2an
    an4s
    @0
    @4
    @1
    @3
    @19
    cc
    wcel
    #
    @32
    @37
    @38
    @43
    @1
    @3
    wa
    @39
    @3
    @1
    @38
    @40
    ancoms
    @17
    @18
    addcl
    syl2an
    an42s
    negsubd
    3eqtrd
    eqtr3d
end
