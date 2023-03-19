include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "negsubdi.mm"
include "wceq.mm"
include "negcl.mm"
include "addcom.mm"
include "sylan.mm"
include "negsub.mm"
include "ancoms.mm"
include "3eqtrd.mm"

theorem negsubdi2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> -u ( A - B ) = ( B - A ) )

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
    cmin
    co
    cneg
    cA
    cneg
    #
    cB
    caddc
    co
    #
    cB
    @2
    caddc
    co
    #
    cB
    cA
    cmin
    co
    #
    cA
    cB
    negsubdi
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
    addcom
    sylan
    @1
    @0
    @4
    @5
    wceq
    cB
    cA
    negsub
    ancoms
    3eqtrd
end
