include "wn.mm"
include "wo.mm"
include "wa.mm"
include "oml.mm"
include "df-le2.mm"
include "lan.mm"
include "lor.mm"
include "3tr2.mm"

theorem oml2
  param wva: term a
  param wvb: term b
  assume oml2.1: |- a =< b


  assert |- ( a v ( a ' ^ b ) ) = b

  proof
    wva
    wva
    wn
    #
    wva
    wvb
    wo
    #
    wa
    #
    wo
    @1
    wva
    @0
    wvb
    wa
    #
    wo
    wvb
    wva
    wvb
    oml
    @2
    @3
    wva
    @1
    wvb
    @0
    wva
    wvb
    oml2.1
    df-le2
    #
    lan
    lor
    @4
    3tr2
end
