include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "ssex.mm"
include "ax-mp.mm"

theorem ssexi
  let cA: class A
  let cB: class B
  assume ssexi.1: |- B e. _V
  assume ssexi.2: |- A C_ B


  assert |- A e. _V

  proof
    cA
    cB
    wss
    cA
    cvv
    wcel
    ssexi.2
    cA
    cB
    ssexi.1
    ssex
    ax-mp
end
