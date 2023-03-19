include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "ltnr.mm"
include "ax-mp.mm"

theorem ltnri
  let cA: class A
  assume lt.1: |- A e. RR


  assert |- -. A < A

  proof
    cA
    cr
    wcel
    cA
    cA
    clt
    wbr
    wn
    lt.1
    cA
    ltnr
    ax-mp
end
