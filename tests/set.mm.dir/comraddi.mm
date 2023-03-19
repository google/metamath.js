include "caddc.mm"
include "co.mm"
include "addcomi.mm"
include "eqtri.mm"

theorem comraddi
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume comraddi.1: |- B e. CC
  assume comraddi.2: |- C e. CC
  assume comraddi.3: |- A = ( B + C )


  assert |- A = ( C + B )

  proof
    cA
    cB
    cC
    caddc
    co
    cC
    cB
    caddc
    co
    comraddi.3
    cB
    cC
    comraddi.1
    comraddi.2
    addcomi
    eqtri
end
