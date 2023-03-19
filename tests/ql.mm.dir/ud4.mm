include "wi4.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ud4lem1.mm"
include "ud4lem0b.mm"
include "ud4lem2.mm"
include "ax-r2.mm"
include "ud4lem0a.mm"
include "ud4lem3.mm"
include "ax-r1.mm"

theorem ud4
  param wva: term a
  param wvb: term b


  assert |- ( a v b ) = ( ( a ->4 b ) ->4 ( ( ( a ->4 b ) ->4 ( b ->4 a ) ) ->4 a ) )

  proof
    wva
    wvb
    wi4
    #
    @0
    wvb
    wva
    wi4
    wi4
    #
    wva
    wi4
    #
    wi4
    #
    wva
    wvb
    wo
    #
    @3
    @0
    @4
    wi4
    @4
    @2
    @4
    @0
    @2
    wva
    wva
    wn
    wvb
    wn
    wa
    wo
    #
    wva
    wi4
    @4
    @1
    @5
    wva
    wva
    wvb
    ud4lem1
    ud4lem0b
    wva
    wvb
    ud4lem2
    ax-r2
    ud4lem0a
    wva
    wvb
    ud4lem3
    ax-r2
    ax-r1
end
