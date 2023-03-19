include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "ax-hvcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "ax-hvass.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem hvadd12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( A +h ( B +h C ) ) = ( B +h ( A +h C ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    cA
    cB
    cva
    co
    #
    cC
    cva
    co
    #
    cB
    cA
    cva
    co
    #
    cC
    cva
    co
    #
    cA
    cB
    cC
    cva
    co
    cva
    co
    cB
    cA
    cC
    cva
    co
    cva
    co
    #
    @0
    @1
    @4
    @6
    wceq
    @2
    @0
    @1
    wa
    @3
    @5
    cC
    cva
    cA
    cB
    ax-hvcom
    oveq1d
    3adant3
    cA
    cB
    cC
    ax-hvass
    @1
    @0
    @2
    @6
    @7
    wceq
    cB
    cA
    cC
    ax-hvass
    3com12
    3eqtr3d
end
