include "wi5.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ud5lem1.mm"
include "ud5lem0b.mm"
include "ud5lem2.mm"
include "ax-r2.mm"
include "ud5lem0a.mm"
include "ud5lem3.mm"
include "ax-r1.mm"

theorem ud5
  param wva: term a
  param wvb: term b


  assert |- ( a v b ) = ( ( a ->5 b ) ->5 ( ( ( a ->5 b ) ->5 ( b ->5 a ) ) ->5 a ) )

  proof
    wva
    wvb
    wi5
    #
    @0
    wvb
    wva
    wi5
    wi5
    #
    wva
    wi5
    #
    wi5
    #
    wva
    wvb
    wo
    #
    @3
    @0
    wva
    wva
    wn
    wvb
    wa
    wo
    #
    wi5
    @4
    @2
    @5
    @0
    @2
    wva
    wvb
    wn
    wo
    #
    wva
    wi5
    @5
    @1
    @6
    wva
    wva
    wvb
    ud5lem1
    ud5lem0b
    wva
    wvb
    ud5lem2
    ax-r2
    ud5lem0a
    wva
    wvb
    ud5lem3
    ax-r2
    ax-r1
end
