include "wss.mm"
include "wcel.mm"
include "onirri.mm"
include "ssel.mm"
include "mtoi.mm"

theorem onssnel2i
  let cA: class A
  let cB: class B
  assume on.1: |- A e. On


  assert |- ( B C_ A -> -. A e. B )

  proof
    cB
    cA
    wss
    cA
    cB
    wcel
    cA
    cA
    wcel
    cA
    on.1
    onirri
    cB
    cA
    cA
    ssel
    mtoi
end
