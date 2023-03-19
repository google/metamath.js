include "wer.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "dmexg.mm"
include "erdm.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "erex.mm"
include "impbid.mm"

theorem erexb
  let cA: class A
  let cR: class R


  assert |- ( R Er A -> ( R e. _V <-> A e. _V ) )

  proof
    cA
    cR
    wer
    #
    cR
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @1
    cR
    cdm
    #
    cvv
    wcel
    @0
    @2
    cR
    cvv
    dmexg
    @0
    @3
    cA
    cvv
    cA
    cR
    erdm
    eleq1d
    syl5ib
    cA
    cR
    cvv
    erex
    impbid
end
