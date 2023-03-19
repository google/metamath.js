include "wne.mm"
include "necom.mm"
include "mpbi.mm"

theorem necomi
  let cA: class A
  let cB: class B
  assume necomi.1: |- A =/= B


  assert |- B =/= A

  proof
    cA
    cB
    wne
    cB
    cA
    wne
    necomi.1
    cA
    cB
    necom
    mpbi
end
