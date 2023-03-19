include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "coman1.mm"
include "comcom.mm"
include "comcom2.mm"
include "comcom5.mm"
include "com2or.mm"
include "df-i3.mm"
include "ax-r1.mm"
include "cbtr.mm"

theorem comi31
  param wva: term a
  param wvb: term b


  assert |- a C ( a ->3 b )

  proof
    wva
    wva
    wn
    #
    wvb
    wa
    #
    @0
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    @0
    wvb
    wo
    #
    wa
    #
    wo
    #
    wva
    wvb
    wi3
    #
    wva
    @4
    @6
    wva
    @1
    @3
    wva
    @1
    @0
    @1
    @1
    @0
    @0
    wvb
    coman1
    comcom
    comcom2
    comcom5
    wva
    @3
    @0
    @3
    @3
    @0
    @0
    @2
    coman1
    comcom
    comcom2
    comcom5
    com2or
    @6
    wva
    wva
    @5
    coman1
    comcom
    com2or
    @8
    @7
    wva
    wvb
    df-i3
    ax-r1
    cbtr
end
