include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "ax-hvcom.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "ax-hvass.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem hvadd32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A +h B ) +h C ) = ( ( A +h C ) +h B ) )

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
    cC
    cva
    co
    #
    cva
    co
    #
    cA
    cC
    cB
    cva
    co
    #
    cva
    co
    #
    cA
    cB
    cva
    co
    cC
    cva
    co
    cA
    cC
    cva
    co
    cB
    cva
    co
    #
    @1
    @2
    @4
    @6
    wceq
    @0
    @1
    @2
    wa
    @3
    @5
    cA
    cva
    cB
    cC
    ax-hvcom
    oveq2d
    3adant1
    cA
    cB
    cC
    ax-hvass
    @0
    @2
    @1
    @7
    @6
    wceq
    cA
    cC
    cB
    ax-hvass
    3com23
    3eqtr4d
end
