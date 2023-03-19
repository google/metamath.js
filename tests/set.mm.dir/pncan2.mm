include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "addcom.mm"
include "oveq1d.mm"
include "pncan.mm"
include "eqtr3d.mm"
include "ancoms.mm"

theorem pncan2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A + B ) - A ) = B )

  proof
    cB
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    cB
    caddc
    co
    #
    cA
    cmin
    co
    #
    cB
    wceq
    @0
    @1
    wa
    #
    cB
    cA
    caddc
    co
    #
    cA
    cmin
    co
    @3
    cB
    @4
    @5
    @2
    cA
    cmin
    cB
    cA
    addcom
    oveq1d
    cB
    cA
    pncan
    eqtr3d
    ancoms
end
