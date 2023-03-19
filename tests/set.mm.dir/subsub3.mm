include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subsub2.mm"
include "wceq.mm"
include "addsubass.mm"
include "3com23.mm"
include "eqtr4d.mm"

theorem subsub3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A - ( B - C ) ) = ( ( A + C ) - B ) )

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
    cA
    cB
    cC
    cmin
    co
    cmin
    co
    cA
    cC
    cB
    cmin
    co
    caddc
    co
    #
    cA
    cC
    caddc
    co
    cB
    cmin
    co
    #
    cA
    cB
    cC
    subsub2
    @0
    @2
    @1
    @4
    @3
    wceq
    cA
    cC
    cB
    addsubass
    3com23
    eqtr4d
end
