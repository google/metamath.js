include "c0.mm"
include "csn.mm"
include "con0.mm"
include "wcel.mm"
include "wn.mm"
include "cvv.mm"
include "wne.mm"
include "snsn0non.mm"
include "wceq.mm"
include "snex.mm"
include "id.mm"
include "syl5eleqr.mm"
include "necon3bi.mm"
include "ax-mp.mm"

theorem onnev



  assert |- On =/= _V

  proof
    c0
    csn
    #
    csn
    #
    con0
    wcel
    #
    wn
    con0
    cvv
    wne
    snsn0non
    @2
    con0
    cvv
    con0
    cvv
    wceq
    #
    @1
    cvv
    con0
    @0
    snex
    @3
    id
    syl5eleqr
    necon3bi
    ax-mp
end
