include "wcel.mm"
include "bj-ctag.mm"
include "cvv.mm"
include "cxp.mm"
include "elex.mm"
include "bj-tagex.mm"
include "sylib.mm"
include "bj-xpexg2.mm"
include "syl5.mm"

theorem bj-xtagex
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( A e. V -> ( B e. W -> ( A X. tag B ) e. _V ) )

  proof
    cB
    cW
    wcel
    #
    cB
    bj-ctag
    #
    cvv
    wcel
    #
    cA
    cV
    wcel
    cA
    @1
    cxp
    cvv
    wcel
    @0
    cB
    cvv
    wcel
    @2
    cB
    cW
    elex
    cB
    bj-tagex
    sylib
    cA
    @1
    cV
    cvv
    bj-xpexg2
    syl5
end
