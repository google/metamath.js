include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "readd.mm"
include "mp2an.mm"

theorem readdi
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( Re ` ( A + B ) ) = ( ( Re ` A ) + ( Re ` B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cre
    cfv
    cA
    cre
    cfv
    cB
    cre
    cfv
    caddc
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    readd
    mp2an
end
