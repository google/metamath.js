include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cneg.mm"
include "cmin.mm"
include "negdi.mm"
include "wceq.mm"
include "negcl.mm"
include "negsub.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem negdi2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> -u ( A + B ) = ( -u A - B ) )

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
    cA
    cB
    caddc
    co
    cneg
    cA
    cneg
    #
    cB
    cneg
    caddc
    co
    #
    @2
    cB
    cmin
    co
    #
    cA
    cB
    negdi
    @0
    @2
    cc
    wcel
    @1
    @3
    @4
    wceq
    cA
    negcl
    @2
    cB
    negsub
    sylan
    eqtrd
end
