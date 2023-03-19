include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wb.mm"
include "elpw2g.mm"
include "ax-mp.mm"

theorem elpw2
  let cA: class A
  let cB: class B
  assume elpw2.1: |- B e. _V


  assert |- ( A e. ~P B <-> A C_ B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cpw
    wcel
    cA
    cB
    wss
    wb
    elpw2.1
    cA
    cB
    cvv
    elpw2g
    ax-mp
end
