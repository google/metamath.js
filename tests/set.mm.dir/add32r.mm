include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "addass.mm"
include "add32.mm"
include "eqtr3d.mm"

theorem add32r
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A + ( B + C ) ) = ( ( A + C ) + B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    w3a
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    cA
    cB
    cC
    caddc
    co
    caddc
    co
    cA
    cC
    caddc
    co
    cB
    caddc
    co
    cA
    cB
    cC
    addass
    cA
    cB
    cC
    add32
    eqtr3d
end
