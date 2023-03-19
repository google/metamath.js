include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "addcom.mm"
include "3adant1.mm"
include "eqeq1d.mm"
include "subadd.mm"
include "wb.mm"
include "3com23.mm"
include "3bitr4d.mm"

theorem subsub23
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) = C <-> ( A - C ) = B ) )

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
    cB
    cC
    caddc
    co
    #
    cA
    wceq
    cC
    cB
    caddc
    co
    #
    cA
    wceq
    #
    cA
    cB
    cmin
    co
    cC
    wceq
    cA
    cC
    cmin
    co
    cB
    wceq
    #
    @3
    @4
    @5
    cA
    @1
    @2
    @4
    @5
    wceq
    @0
    cB
    cC
    addcom
    3adant1
    eqeq1d
    cA
    cB
    cC
    subadd
    @0
    @2
    @1
    @7
    @6
    wb
    cA
    cC
    cB
    subadd
    3com23
    3bitr4d
end
