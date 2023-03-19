include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjadd.mm"
include "mp2an.mm"

theorem cjaddi
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( * ` ( A + B ) ) = ( ( * ` A ) + ( * ` B ) )

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
    ccj
    cfv
    cA
    ccj
    cfv
    cB
    ccj
    cfv
    caddc
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    cjadd
    mp2an
end
