include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "negcl.mm"
include "subneg.mm"
include "sylan.mm"
include "negsubdi.mm"
include "negsubdi2.mm"
include "3eqtr2d.mm"

theorem neg2sub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( -u A - -u B ) = ( B - A ) )

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
    cneg
    #
    cB
    cneg
    cmin
    co
    #
    @2
    cB
    caddc
    co
    #
    cA
    cB
    cmin
    co
    cneg
    cB
    cA
    cmin
    co
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
    subneg
    sylan
    cA
    cB
    negsubdi
    cA
    cB
    negsubdi2
    3eqtr2d
end
