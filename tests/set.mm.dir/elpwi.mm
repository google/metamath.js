include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "elpwg.mm"
include "ibi.mm"

theorem elpwi
  let cA: class A
  let cB: class B


  assert |- ( A e. ~P B -> A C_ B )

  proof
    cA
    cB
    cpw
    #
    wcel
    cA
    cB
    wss
    cA
    cB
    @0
    elpwg
    ibi
end
