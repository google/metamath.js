include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "wb.mm"
include "elpw2g.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem elpwi2
  let cA: class A
  let cB: class B
  let cV: class V
  assume elpwi2.1: |- B e. V
  assume elpwi2.2: |- A C_ B


  assert |- A e. ~P B

  proof
    cA
    cB
    cpw
    wcel
    #
    cA
    cB
    wss
    #
    elpwi2.2
    cB
    cV
    wcel
    @0
    @1
    wb
    elpwi2.1
    cA
    cB
    cV
    elpw2g
    ax-mp
    mpbir
end
