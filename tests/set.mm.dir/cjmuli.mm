include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjmul.mm"
include "mp2an.mm"

theorem cjmuli
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( * ` ( A x. B ) ) = ( ( * ` A ) x. ( * ` B ) )

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
    ccj
    cfv
    cA
    ccj
    cfv
    cB
    ccj
    cfv
    cmul
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    cjmul
    mp2an
end
