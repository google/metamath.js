include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subsub2.mm"
include "wceq.mm"
include "addsubass.mm"
include "addsub.mm"
include "eqtr3d.mm"
include "3com23.mm"
include "eqtrd.mm"

theorem subsub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A - ( B - C ) ) = ( ( A - B ) + C ) )

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
    cB
    cmin
    co
    cC
    caddc
    co
    #
    cA
    cB
    cC
    subsub2
    @0
    @2
    @1
    @3
    @4
    wceq
    @0
    @2
    @1
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
    addsubass
    cA
    cC
    cB
    addsub
    eqtr3d
    3com23
    eqtrd
end
