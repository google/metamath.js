include "bj-c1upl.mm"
include "cvv.mm"
include "wcel.mm"
include "bj-cpr1.mm"
include "bj-pr11val.mm"
include "bj-pr1ex.mm"
include "syl5eqelr.mm"
include "c0.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "df-bj-1upl.mm"
include "wi.mm"
include "p0ex.mm"
include "bj-xtagex.mm"
include "ax-mp.mm"
include "syl5eqel.mm"
include "impbii.mm"

theorem bj-1uplex
  let cA: class A


  assert |- ( (| A |) e. _V <-> A e. _V )

  proof
    cA
    bj-c1upl
    #
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @1
    cA
    @0
    bj-cpr1
    cvv
    cA
    bj-pr11val
    @0
    cvv
    bj-pr1ex
    syl5eqelr
    @2
    @0
    c0
    csn
    #
    cA
    bj-ctag
    cxp
    #
    cvv
    cA
    df-bj-1upl
    @3
    cvv
    wcel
    @2
    @4
    cvv
    wcel
    wi
    p0ex
    @3
    cA
    cvv
    cvv
    bj-xtagex
    ax-mp
    syl5eqel
    impbii
end
