include "wi4.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "u4lem5.mm"
include "anor3.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "oran2.mm"
include "con2.mm"

theorem u4lem5n
  param wva: term a
  param wvb: term b


  assert |- ( a ->4 ( a ->4 b ) ) ' = ( ( a v b ) ^ b ' )

  proof
    wva
    wva
    wvb
    wi4
    wi4
    #
    wva
    wvb
    wo
    #
    wvb
    wn
    #
    wa
    #
    @0
    @1
    wn
    #
    wvb
    wo
    #
    @3
    wn
    @0
    wva
    wn
    @2
    wa
    #
    wvb
    wo
    @5
    wva
    wvb
    u4lem5
    @6
    @4
    wvb
    wva
    wvb
    anor3
    ax-r5
    ax-r2
    @1
    wvb
    oran2
    ax-r2
    con2
end
