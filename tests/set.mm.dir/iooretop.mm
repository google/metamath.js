include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "co.mm"
include "ctb.mm"
include "wcel.mm"
include "wss.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "ioorebas.mm"
include "sselii.mm"

theorem iooretop
  let cA: class A
  let cB: class B


  assert |- ( A (,) B ) e. ( topGen ` ran (,) )

  proof
    cioo
    crn
    #
    @0
    ctg
    cfv
    #
    cA
    cB
    cioo
    co
    @0
    ctb
    wcel
    @0
    @1
    wss
    retopbas
    @0
    ctb
    bastg
    ax-mp
    cA
    cB
    ioorebas
    sselii
end
