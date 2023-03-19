include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulneg1.mm"
include "ancoms.mm"
include "negcl.mm"
include "mulcom.mm"
include "sylan2.mm"
include "negeqd.mm"
include "3eqtr4d.mm"

theorem mulneg2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A x. -u B ) = -u ( A x. B ) )

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
    cB
    cneg
    #
    cA
    cmul
    co
    #
    cB
    cA
    cmul
    co
    #
    cneg
    #
    cA
    @3
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    cneg
    @1
    @0
    @4
    @6
    wceq
    cB
    cA
    mulneg1
    ancoms
    @1
    @0
    @3
    cc
    wcel
    @7
    @4
    wceq
    cB
    negcl
    cA
    @3
    mulcom
    sylan2
    @2
    @8
    @5
    cA
    cB
    mulcom
    negeqd
    3eqtr4d
end
