include "cc0.mm"
include "cdp.mm"
include "co.mm"
include "cdp2.mm"
include "0re.mm"
include "dpval3.mm"
include "dp20u.mm"
include "eqtri.mm"

theorem dp0u
  let cA: class A
  assume dp0u.1: |- A e. NN0


  assert |- ( A . 0 ) = A

  proof
    cA
    cc0
    cdp
    co
    cA
    cc0
    cdp2
    cA
    cA
    cc0
    dp0u.1
    0re
    dpval3
    cA
    dp0u.1
    dp20u
    eqtri
end
