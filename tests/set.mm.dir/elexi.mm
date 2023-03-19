include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "ax-mp.mm"

theorem elexi
  let cA: class A
  let cB: class B
  assume elexi.1: |- A e. B


  assert |- A e. _V

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    elexi.1
    cA
    cB
    elex
    ax-mp
end
