include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "cpw.mm"
include "snss.mm"
include "snex.mm"
include "elpw.mm"
include "bitr4i.mm"

theorem snelpw
  let cA: class A
  let cB: class B
  assume snelpw.1: |- A e. _V


  assert |- ( A e. B <-> { A } e. ~P B )

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
    snelpw.1
    snss
    @0
    cB
    cA
    snex
    elpw
    bitr4i
end
