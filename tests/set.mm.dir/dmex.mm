include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "dmexg.mm"
include "ax-mp.mm"

theorem dmex
  let cA: class A
  assume dmex.1: |- A e. _V


  assert |- dom A e. _V

  proof
    cA
    cvv
    wcel
    cA
    cdm
    cvv
    wcel
    dmex.1
    cA
    cvv
    dmexg
    ax-mp
end
