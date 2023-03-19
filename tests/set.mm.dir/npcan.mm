include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subcl.mm"
include "simpr.mm"
include "addcomd.mm"
include "wceq.mm"
include "pncan3.mm"
include "ancoms.mm"
include "eqtrd.mm"

theorem npcan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A - B ) + B ) = A )

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
    cmin
    co
    #
    cB
    caddc
    co
    cB
    @3
    caddc
    co
    #
    cA
    @2
    @3
    cB
    cA
    cB
    subcl
    @0
    @1
    simpr
    addcomd
    @1
    @0
    @4
    cA
    wceq
    cB
    cA
    pncan3
    ancoms
    eqtrd
end
