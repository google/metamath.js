include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor2.mm"
include "u2lemona.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "anor1.mm"
include "ax-r1.mm"

theorem u2lemnaa
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ' ^ a ) = ( a ^ b ' )

  proof
    wva
    wvb
    wi2
    #
    wn
    wva
    wa
    #
    wva
    wn
    #
    wvb
    wo
    #
    wn
    #
    wva
    wvb
    wn
    wa
    #
    @1
    @0
    @2
    wo
    #
    wn
    @4
    @0
    wva
    anor2
    @6
    @3
    wva
    wvb
    u2lemona
    ax-r4
    ax-r2
    @5
    @4
    wva
    wvb
    anor1
    ax-r1
    ax-r2
end
