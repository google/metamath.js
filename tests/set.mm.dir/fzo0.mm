include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "fzonel.mm"
include "fzon0.mm"
include "necon1bbii.mm"
include "mpbi.mm"

theorem fzo0
  let cA: class A


  assert |- ( A ..^ A ) = (/)

  proof
    cA
    cA
    cA
    cfzo
    co
    #
    wcel
    #
    wn
    @0
    c0
    wceq
    cA
    cA
    fzonel
    @1
    @0
    c0
    cA
    cA
    fzon0
    necon1bbii
    mpbi
end
