include "wcel.mm"
include "cvv.mm"
include "ccrd.mm"
include "cdm.mm"
include "elex.mm"
include "cardeqv.mm"
include "syl6eleqr.mm"

theorem numth3
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A e. dom card )

  proof
    cA
    cV
    wcel
    cA
    cvv
    ccrd
    cdm
    cA
    cV
    elex
    cardeqv
    syl6eleqr
end
