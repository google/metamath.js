include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "addsub.mm"
include "addsubass.mm"
include "eqtr3d.mm"
include "3com23.mm"

theorem subadd23
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) + C ) = ( A + ( C - B ) ) )

  proof
    cA
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cB
    cmin
    co
    cC
    caddc
    co
    #
    cA
    cC
    cB
    cmin
    co
    caddc
    co
    #
    wceq
    @0
    @1
    @2
    w3a
    cA
    cC
    caddc
    co
    cB
    cmin
    co
    @3
    @4
    cA
    cC
    cB
    addsub
    cA
    cC
    cB
    addsubass
    eqtr3d
    3com23
end
