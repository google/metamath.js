include "necomi.mm"
include "neii.mm"

theorem nesymi
  let cA: class A
  let cB: class B
  assume nesymi.1: |- A =/= B


  assert |- -. B = A

  proof
    cB
    cA
    cA
    cB
    nesymi.1
    necomi
    neii
end
