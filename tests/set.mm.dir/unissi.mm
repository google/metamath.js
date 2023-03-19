include "wss.mm"
include "cuni.mm"
include "uniss.mm"
include "ax-mp.mm"

theorem unissi
  let cA: class A
  let cB: class B
  assume unissi.1: |- A C_ B


  assert |- U. A C_ U. B

  proof
    cA
    cB
    wss
    cA
    cuni
    cB
    cuni
    wss
    unissi.1
    cA
    cB
    uniss
    ax-mp
end
