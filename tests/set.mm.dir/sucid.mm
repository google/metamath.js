include "cvv.mm"
include "wcel.mm"
include "csuc.mm"
include "sucidg.mm"
include "ax-mp.mm"

theorem sucid
  let cA: class A
  assume sucid.1: |- A e. _V


  assert |- A e. suc A

  proof
    cA
    cvv
    wcel
    cA
    cA
    csuc
    wcel
    sucid.1
    cA
    cvv
    sucidg
    ax-mp
end
