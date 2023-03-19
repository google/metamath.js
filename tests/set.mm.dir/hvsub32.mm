include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cva.mm"
include "co.mm"
include "cmv.mm"
include "wceq.mm"
include "ax-hvcom.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "hvsubass.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem hvsub32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A -h B ) -h C ) = ( ( A -h C ) -h B ) )

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
    #
    cA
    cB
    cC
    cva
    co
    #
    cmv
    co
    cA
    cC
    cB
    cva
    co
    #
    cmv
    co
    #
    cA
    cB
    cmv
    co
    cC
    cmv
    co
    cA
    cC
    cmv
    co
    cB
    cmv
    co
    #
    @3
    @4
    @5
    cA
    cmv
    @1
    @2
    @4
    @5
    wceq
    @0
    cB
    cC
    ax-hvcom
    3adant1
    oveq2d
    cA
    cB
    cC
    hvsubass
    @0
    @2
    @1
    @7
    @6
    wceq
    cA
    cC
    cB
    hvsubass
    3com23
    3eqtr4d
end
