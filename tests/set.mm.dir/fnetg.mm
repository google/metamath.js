include "cfne.mm"
include "wbr.mm"
include "cuni.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "eqid.mm"
include "isfne4.mm"
include "simprbi.mm"

theorem fnetg
  let cA: class A
  let cB: class B


  assert |- ( A Fne B -> A C_ ( topGen ` B ) )

  proof
    cA
    cB
    cfne
    wbr
    cA
    cuni
    #
    cB
    cuni
    #
    wceq
    cA
    cB
    ctg
    cfv
    wss
    cA
    cB
    @0
    @1
    @0
    eqid
    @1
    eqid
    isfne4
    simprbi
end
