include "gtneii.mm"
include "necomi.mm"

theorem ltneii
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume ltneii.2: |- A < B


  assert |- A =/= B

  proof
    cB
    cA
    cA
    cB
    lt.1
    ltneii.2
    gtneii
    necomi
end
