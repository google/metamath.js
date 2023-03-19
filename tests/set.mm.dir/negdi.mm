include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subneg.mm"
include "negeqd.mm"
include "wceq.mm"
include "negcl.mm"
include "negsubdi.mm"
include "sylan2.mm"
include "eqtr3d.mm"

theorem negdi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> -u ( A + B ) = ( -u A + -u B ) )

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
    cA
    cB
    cneg
    #
    cmin
    co
    #
    cneg
    #
    cA
    cB
    caddc
    co
    #
    cneg
    cA
    cneg
    @3
    caddc
    co
    #
    @2
    @4
    @6
    cA
    cB
    subneg
    negeqd
    @1
    @0
    @3
    cc
    wcel
    @5
    @7
    wceq
    cB
    negcl
    cA
    @3
    negsubdi
    sylan2
    eqtr3d
end
