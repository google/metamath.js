include "wi4.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor2.mm"
include "u4lemona.mm"
include "ax-r4.mm"
include "anor1.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem u4lemnaa
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) ' ^ a ) = ( a ^ b ' )

  proof
    wva
    wvb
    wi4
    #
    wn
    wva
    wa
    @0
    wva
    wn
    #
    wo
    #
    wn
    #
    wva
    wvb
    wn
    wa
    #
    @0
    wva
    anor2
    @3
    @1
    wvb
    wo
    #
    wn
    #
    @4
    @2
    @5
    wva
    wvb
    u4lemona
    ax-r4
    @4
    @6
    wva
    wvb
    anor1
    ax-r1
    ax-r2
    ax-r2
end
