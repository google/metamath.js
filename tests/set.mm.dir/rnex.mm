include "cvv.mm"
include "wcel.mm"
include "crn.mm"
include "rnexg.mm"
include "ax-mp.mm"

theorem rnex
  let cA: class A
  assume dmex.1: |- A e. _V


  assert |- ran A e. _V

  proof
    cA
    cvv
    wcel
    cA
    crn
    cvv
    wcel
    dmex.1
    cA
    cvv
    rnexg
    ax-mp
end
