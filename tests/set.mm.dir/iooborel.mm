include "cioo.mm"
include "co.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "sssalgen.mm"
include "ax-mp.mm"
include "iooretop.mm"
include "eleqtrri.mm"
include "sselii.mm"

theorem iooborel
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let vk: setvar k
  let vx: setvar x
  assume iooborel.1: |- J = ( topGen ` ran (,) )
  assume iooborel.2: |- B = ( SalGen ` J )


  assert |- ( A (,) C ) e. B

  proof
    cJ
    cB
    cA
    cC
    cioo
    co
    #
    cJ
    ctop
    wcel
    cJ
    cB
    wss
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    iooborel.1
    retop
    eqeltri
    cB
    ctop
    cJ
    iooborel.2
    sssalgen
    ax-mp
    @0
    @1
    cJ
    cA
    cC
    iooretop
    iooborel.1
    eleqtrri
    sselii
end
