include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "lan.mm"
include "ax-r4.mm"
include "2or.mm"
include "dfb.mm"
include "3tr1.mm"

theorem lbi
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume lbi.1: |- a = b


  assert |- ( c == a ) = ( c == b )

  proof
    wvc
    wva
    wa
    #
    wvc
    wn
    #
    wva
    wn
    #
    wa
    #
    wo
    wvc
    wvb
    wa
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    wvc
    wva
    tb
    wvc
    wvb
    tb
    @0
    @4
    @3
    @6
    wva
    wvb
    wvc
    lbi.1
    lan
    @2
    @5
    @1
    wva
    wvb
    lbi.1
    ax-r4
    lan
    2or
    wvc
    wva
    dfb
    wvc
    wvb
    dfb
    3tr1
end
