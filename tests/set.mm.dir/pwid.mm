include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "pwidg.mm"
include "ax-mp.mm"

theorem pwid
  let cA: class A
  assume pwid.1: |- A e. _V


  assert |- A e. ~P A

  proof
    cA
    cvv
    wcel
    cA
    cA
    cpw
    wcel
    pwid.1
    cA
    cvv
    pwidg
    ax-mp
end
