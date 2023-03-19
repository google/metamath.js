include "wss.mm"
include "wbr.mm"
include "wi.mm"
include "ssbr.mm"
include "ax-mp.mm"

theorem ssbri
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ssbri.1: |- A C_ B


  assert |- ( C A D -> C B D )

  proof
    cA
    cB
    wss
    cC
    cD
    cA
    wbr
    cC
    cD
    cB
    wbr
    wi
    ssbri.1
    cA
    cB
    cC
    cD
    ssbr
    ax-mp
end
