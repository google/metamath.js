include "wcel.mm"
include "cima.mm"
include "cvv.mm"
include "imaexg.mm"
include "ax-mp.mm"

theorem imaexi
  let cA: class A
  let cB: class B
  let cV: class V
  assume imaexi.1: |- A e. V


  assert |- ( A " B ) e. _V

  proof
    cA
    cV
    wcel
    cA
    cB
    cima
    cvv
    wcel
    imaexi.1
    cA
    cB
    cV
    imaexg
    ax-mp
end
