include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "wo.mm"
include "mulcom.mm"
include "3adant2.mm"
include "3adant1.mm"
include "eqeq12d.mm"
include "wb.mm"
include "mulcan1g.mm"
include "3coml.mm"
include "orcom.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem mulcan2g
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A x. C ) = ( B x. C ) <-> ( A = B \/ C = 0 ) ) )

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
    w3a
    #
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    wceq
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    cC
    cc0
    wceq
    #
    wo
    #
    @3
    @4
    @6
    @5
    @7
    @0
    @2
    @4
    @6
    wceq
    @1
    cA
    cC
    mulcom
    3adant2
    @1
    @2
    @5
    @7
    wceq
    @0
    cB
    cC
    mulcom
    3adant1
    eqeq12d
    @3
    @8
    @10
    @9
    wo
    #
    @11
    @2
    @0
    @1
    @8
    @12
    wb
    cC
    cA
    cB
    mulcan1g
    3coml
    @10
    @9
    orcom
    syl6bb
    bitrd
end
