include "cpw.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "elex.mm"
include "elpwg.mm"
include "biadan2.mm"

theorem elpwb
  let cA: class A
  let cB: class B


  assert |- ( A e. ~P B <-> ( A e. _V /\ A C_ B ) )

  proof
    cA
    cB
    cpw
    #
    wcel
    cA
    cvv
    wcel
    cA
    cB
    wss
    cA
    @0
    elex
    cA
    cB
    cvv
    elpwg
    biadan2
end
