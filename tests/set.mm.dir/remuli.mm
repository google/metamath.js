include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cmin.mm"
include "wceq.mm"
include "remul.mm"
include "mp2an.mm"

theorem remuli
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( Re ` ( A x. B ) ) = ( ( ( Re ` A ) x. ( Re ` B ) ) - ( ( Im ` A ) x. ( Im ` B ) ) )

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
    cre
    cfv
    cA
    cre
    cfv
    cB
    cre
    cfv
    cmul
    co
    cA
    cim
    cfv
    cB
    cim
    cfv
    cmul
    co
    cmin
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    remul
    mp2an
end
