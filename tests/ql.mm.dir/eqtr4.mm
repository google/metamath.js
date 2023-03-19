include "tb.mm"
include "wa.mm"
include "mlaoml.mm"
include "leran.mm"
include "letr.mm"

theorem eqtr4
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d


  assert |- ( ( ( a == b ) ^ ( b == c ) ) ^ ( c == d ) ) =< ( a == d )

  proof
    wva
    wvb
    tb
    wvb
    wvc
    tb
    wa
    #
    wvc
    wvd
    tb
    #
    wa
    wva
    wvc
    tb
    #
    @1
    wa
    wva
    wvd
    tb
    @0
    @2
    @1
    wva
    wvb
    wvc
    mlaoml
    leran
    wva
    wvc
    wvd
    mlaoml
    letr
end
