include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cneg.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "mulneg2.mm"
include "adantl.mm"
include "oveq2d.mm"
include "mulcl.mm"
include "negsub.mm"
include "sylan2.mm"
include "eqtr2d.mm"
include "3impb.mm"

theorem submul2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A - ( B x. C ) ) = ( A + ( B x. -u C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cA
    cB
    cC
    cmul
    co
    #
    cmin
    co
    #
    cA
    cB
    cC
    cneg
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @0
    @1
    @2
    wa
    #
    wa
    #
    @6
    cA
    @3
    cneg
    #
    caddc
    co
    #
    @4
    @8
    @5
    @9
    cA
    caddc
    @7
    @5
    @9
    wceq
    @0
    cB
    cC
    mulneg2
    adantl
    oveq2d
    @7
    @0
    @3
    cc
    wcel
    @10
    @4
    wceq
    cB
    cC
    mulcl
    cA
    @3
    negsub
    sylan2
    eqtr2d
    3impb
end
