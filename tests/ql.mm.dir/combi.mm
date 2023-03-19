include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "comanr1.mm"
include "comcom6.mm"
include "com2or.mm"
include "dfb.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem combi
  param wva: term a
  param wvb: term b


  assert |- a C ( a == b )

  proof
    wva
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    tb
    #
    wva
    @0
    @3
    wva
    wvb
    comanr1
    wva
    @3
    @1
    @2
    comanr1
    comcom6
    com2or
    @5
    @4
    wva
    wvb
    dfb
    ax-r1
    cbtr
end
