include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "wceq.mm"
include "ipcnval.mm"
include "mp2an.mm"

theorem ipcni
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( Re ` ( A x. ( * ` B ) ) ) = ( ( ( Re ` A ) x. ( Re ` B ) ) + ( ( Im ` A ) x. ( Im ` B ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    ccj
    cfv
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
    caddc
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    ipcnval
    mp2an
end
