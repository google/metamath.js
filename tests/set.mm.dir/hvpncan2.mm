include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "cmv.mm"
include "wceq.mm"
include "wa.mm"
include "ax-hvcom.mm"
include "oveq1d.mm"
include "hvpncan.mm"
include "eqtr3d.mm"
include "ancoms.mm"

theorem hvpncan2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A +h B ) -h A ) = B )

  proof
    cB
    chil
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cB
    cva
    co
    #
    cA
    cmv
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
    cva
    co
    #
    cA
    cmv
    co
    @3
    cB
    @4
    @5
    @2
    cA
    cmv
    cB
    cA
    ax-hvcom
    oveq1d
    cB
    cA
    hvpncan
    eqtr3d
    ancoms
end
