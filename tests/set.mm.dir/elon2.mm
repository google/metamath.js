include "con0.mm"
include "wcel.mm"
include "cvv.mm"
include "word.mm"
include "wa.mm"
include "elex.mm"
include "elong.mm"
include "biadan2.mm"
include "ancom.mm"
include "bitri.mm"

theorem elon2
  let cA: class A


  assert |- ( A e. On <-> ( Ord A /\ A e. _V ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    word
    #
    wa
    @2
    @1
    wa
    @0
    @1
    @2
    cA
    con0
    elex
    cA
    cvv
    elong
    biadan2
    @1
    @2
    ancom
    bitri
end
