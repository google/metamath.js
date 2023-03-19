include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "divadddiv.mm"
include "sylanl2.mm"
include "simplr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "divneg.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simpll.mm"
include "simprll.mm"
include "simprlr.mm"
include "divcl.mm"
include "negsubd.mm"
include "eqtr3d.mm"
include "mulneg1d.mm"
include "mulcld.mm"
include "eqtrd.mm"
include "oveq1d.mm"

theorem divsubdiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / C ) - ( B / D ) ) = ( ( ( A x. D ) - ( B x. C ) ) / ( C x. D ) ) )

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
    cC
    cc0
    wne
    #
    wa
    #
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    #
    wa
    #
    wa
    #
    cA
    cD
    cmul
    co
    #
    cB
    cneg
    #
    cC
    cmul
    co
    #
    caddc
    co
    #
    cC
    cD
    cmul
    co
    #
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cD
    cdiv
    co
    #
    cmin
    co
    #
    @11
    cB
    cC
    cmul
    co
    #
    cmin
    co
    #
    @15
    cdiv
    co
    @10
    @17
    @12
    cD
    cdiv
    co
    #
    caddc
    co
    #
    @16
    @19
    @1
    @0
    @12
    cc
    wcel
    @9
    @23
    @16
    wceq
    cB
    negcl
    cA
    @12
    cC
    cD
    divadddiv
    sylanl2
    @10
    @17
    @18
    cneg
    #
    caddc
    co
    @23
    @19
    @10
    @24
    @22
    @17
    caddc
    @10
    @1
    @6
    @7
    @24
    @22
    wceq
    @0
    @1
    @9
    simplr
    #
    @2
    @5
    @6
    @7
    simprrl
    #
    @2
    @5
    @6
    @7
    simprrr
    #
    cB
    cD
    divneg
    syl3anc
    oveq2d
    @10
    @17
    @18
    @10
    @0
    @3
    @4
    @17
    cc
    wcel
    @0
    @1
    @9
    simpll
    #
    @2
    @3
    @4
    @8
    simprll
    #
    @2
    @3
    @4
    @8
    simprlr
    cA
    cC
    divcl
    syl3anc
    @10
    @1
    @6
    @7
    @18
    cc
    wcel
    @25
    @26
    @27
    cB
    cD
    divcl
    syl3anc
    negsubd
    eqtr3d
    eqtr3d
    @10
    @14
    @21
    @15
    cdiv
    @10
    @14
    @11
    @20
    cneg
    #
    caddc
    co
    @21
    @10
    @13
    @30
    @11
    caddc
    @10
    cB
    cC
    @25
    @29
    mulneg1d
    oveq2d
    @10
    @11
    @20
    @10
    cA
    cD
    @28
    @26
    mulcld
    @10
    cB
    cC
    @25
    @29
    mulcld
    negsubd
    eqtrd
    oveq1d
    eqtr3d
end
