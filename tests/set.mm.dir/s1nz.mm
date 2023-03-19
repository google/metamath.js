include "cs1.mm"
include "cc0.mm"
include "cid.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "c0.mm"
include "df-s1.mm"
include "opex.mm"
include "snnz.mm"
include "eqnetri.mm"

theorem s1nz
  let cA: class A


  assert |- <" A "> =/= (/)

  proof
    cA
    cs1
    cc0
    cA
    cid
    cfv
    #
    cop
    #
    csn
    c0
    cA
    df-s1
    @1
    cc0
    @0
    opex
    snnz
    eqnetri
end
