include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cre.mm"
include "caddc.mm"
include "wceq.mm"
include "immul.mm"
include "mp2an.mm"

theorem immuli
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( Im ` ( A x. B ) ) = ( ( ( Re ` A ) x. ( Im ` B ) ) + ( ( Im ` A ) x. ( Re ` B ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmul
    co
    cim
    cfv
    cA
    cre
    cfv
    cB
    cim
    cfv
    cmul
    co
    cA
    cim
    cfv
    cB
    cre
    cfv
    cmul
    co
    caddc
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    immul
    mp2an
end
