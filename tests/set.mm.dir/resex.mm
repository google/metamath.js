include "cvv.mm"
include "wcel.mm"
include "cres.mm"
include "resexg.mm"
include "ax-mp.mm"

theorem resex
  let cA: class A
  let cB: class B
  assume resex.1: |- A e. _V


  assert |- ( A |` B ) e. _V

  proof
    cA
    cvv
    wcel
    cA
    cB
    cres
    cvv
    wcel
    resex.1
    cA
    cB
    cvv
    resexg
    ax-mp
end
