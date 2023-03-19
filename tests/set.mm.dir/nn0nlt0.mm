include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "nn0ge0.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "nn0re.mm"
include "lenlt.mm"
include "sylancr.mm"
include "mpbid.mm"

theorem nn0nlt0
  let cA: class A


  assert |- ( A e. NN0 -> -. A < 0 )

  proof
    cA
    cn0
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    clt
    wbr
    wn
    #
    cA
    nn0ge0
    @0
    cc0
    cr
    wcel
    cA
    cr
    wcel
    @1
    @2
    wb
    0re
    cA
    nn0re
    cc0
    cA
    lenlt
    sylancr
    mpbid
end
