include "caddc.mm"
include "co.mm"
include "addcomi.mm"
include "eqtri.mm"

theorem addcomli
  let cA: class A
  let cB: class B
  let cC: class C
  assume mul.1: |- A e. CC
  assume mul.2: |- B e. CC
  assume addcomli.2: |- ( A + B ) = C


  assert |- ( B + A ) = C

  proof
    cB
    cA
    caddc
    co
    cA
    cB
    caddc
    co
    cC
    cB
    cA
    mul.2
    mul.1
    addcomi
    addcomli.2
    eqtri
end
