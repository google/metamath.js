include "wer.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "erssxp.mm"
include "sqxpexg.mm"
include "ssexg.mm"
include "syl2an.mm"
include "ex.mm"

theorem erex
  let cA: class A
  let cR: class R
  let cV: class V


  assert |- ( R Er A -> ( A e. V -> R e. _V ) )

  proof
    cA
    cR
    wer
    #
    cA
    cV
    wcel
    #
    cR
    cvv
    wcel
    #
    @0
    cR
    cA
    cA
    cxp
    #
    wss
    @3
    cvv
    wcel
    @2
    @1
    cA
    cR
    erssxp
    cA
    cV
    sqxpexg
    cR
    @3
    cvv
    ssexg
    syl2an
    ex
end
