include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "comanr2.mm"
include "com2or.mm"
include "comcom6.mm"
include "df-i5.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem u5lemc1b
  param wva: term a
  param wvb: term b


  assert |- b C ( a ->5 b )

  proof
    wvb
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wi5
    #
    wvb
    @3
    @5
    wvb
    @0
    @2
    wva
    wvb
    comanr2
    @1
    wvb
    comanr2
    com2or
    wvb
    @5
    @1
    @4
    comanr2
    comcom6
    com2or
    @7
    @6
    wva
    wvb
    df-i5
    ax-r1
    cbtr
end
