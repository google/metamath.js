include "cvv.mm"
include "wcel.mm"
include "cdif.mm"
include "difexg.mm"
include "ax-mp.mm"

theorem difexi
  let cA: class A
  let cB: class B
  assume difexi.1: |- A e. _V


  assert |- ( A \ B ) e. _V

  proof
    cA
    cvv
    wcel
    cA
    cB
    cdif
    cvv
    wcel
    difexi.1
    cA
    cB
    cvv
    difexg
    ax-mp
end
