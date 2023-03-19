include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "c0.mm"
include "intex.mm"
include "necon1bbii.mm"
include "inteq.mm"
include "int0.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "vprc.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "impbii.mm"

theorem intnex
  let cA: class A


  assert |- ( -. |^| A e. _V <-> |^| A = _V )

  proof
    cA
    cint
    #
    cvv
    wcel
    #
    wn
    #
    @0
    cvv
    wceq
    #
    @2
    cA
    c0
    wceq
    #
    @3
    @1
    cA
    c0
    cA
    intex
    necon1bbii
    @4
    @0
    c0
    cint
    cvv
    cA
    c0
    inteq
    int0
    syl6eq
    sylbi
    @3
    @1
    cvv
    cvv
    wcel
    vprc
    @0
    cvv
    cvv
    eleq1
    mtbiri
    impbii
end
