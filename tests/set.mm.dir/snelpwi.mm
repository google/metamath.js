include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "cpw.mm"
include "snssi.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"

theorem snelpwi
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> { A } e. ~P B )

  proof
    cA
    cB
    wcel
    cA
    csn
    #
    cB
    wss
    @0
    cB
    cpw
    wcel
    cA
    cB
    snssi
    @0
    cB
    cA
    snex
    elpw
    sylibr
end
