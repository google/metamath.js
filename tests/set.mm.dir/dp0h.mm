include "cc0.mm"
include "cdp.mm"
include "co.mm"
include "cdp2.mm"
include "c1.mm"
include "cdc.mm"
include "cdiv.mm"
include "0nn0.mm"
include "dpval3rp.mm"
include "dp20h.mm"
include "eqtri.mm"

theorem dp0h
  let cA: class A
  assume dp0h.1: |- A e. RR+


  assert |- ( 0 . A ) = ( A / ; 1 0 )

  proof
    cc0
    cA
    cdp
    co
    cc0
    cA
    cdp2
    cA
    c1
    cc0
    cdc
    cdiv
    co
    cc0
    cA
    0nn0
    dp0h.1
    dpval3rp
    cA
    dp0h.1
    dp20h
    eqtri
end
