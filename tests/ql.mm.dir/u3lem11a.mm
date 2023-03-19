include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ud3lem1.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "lor.mm"
include "oran1.mm"
include "con2.mm"
include "ud3lem0a.mm"
include "u3lem11.mm"

theorem u3lem11a
  param wva: term a
  param wvb: term b


  assert |- ( a ->3 ( ( b ->3 a ) ->3 ( a ->3 b ) ) ' ) = ( a ->3 b ' )

  proof
    wva
    wvb
    wva
    wi3
    wva
    wvb
    wi3
    wi3
    #
    wn
    #
    wi3
    wva
    wvb
    wn
    #
    wva
    wvb
    wo
    #
    wa
    #
    wi3
    wva
    @2
    wi3
    @1
    @4
    wva
    @0
    @4
    @0
    wvb
    @2
    wva
    wn
    #
    wa
    #
    wo
    #
    @4
    wn
    #
    wvb
    wva
    ud3lem1
    @7
    wvb
    @3
    wn
    #
    wo
    @8
    @6
    @9
    wvb
    @6
    @5
    @2
    wa
    @9
    @2
    @5
    ancom
    wva
    wvb
    anor3
    ax-r2
    lor
    wvb
    @3
    oran1
    ax-r2
    ax-r2
    con2
    ud3lem0a
    wva
    wvb
    u3lem11
    ax-r2
end
