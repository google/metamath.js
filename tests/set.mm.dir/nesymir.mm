include "neir.mm"
include "necomi.mm"

theorem nesymir
  let cA: class A
  let cB: class B
  assume nesymir.1: |- -. A = B


  assert |- B =/= A

  proof
    cA
    cB
    cA
    cB
    nesymir.1
    neir
    necomi
end
