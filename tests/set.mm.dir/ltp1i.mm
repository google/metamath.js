include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ltp1.mm"
include "ax-mp.mm"

theorem ltp1i
  let cA: class A
  assume ltplus1.1: |- A e. RR


  assert |- A < ( A + 1 )

  proof
    cA
    cr
    wcel
    cA
    cA
    c1
    caddc
    co
    clt
    wbr
    ltplus1.1
    cA
    ltp1
    ax-mp
end
