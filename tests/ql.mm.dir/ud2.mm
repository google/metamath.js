include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ud2lem1.mm"
include "ud2lem0b.mm"
include "ud2lem2.mm"
include "ax-r2.mm"
include "ud2lem0a.mm"
include "ud2lem3.mm"
include "ax-r1.mm"

theorem ud2
  param wva: term a
  param wvb: term b


  assert |- ( a v b ) = ( ( a ->2 b ) ->2 ( ( ( a ->2 b ) ->2 ( b ->2 a ) ) ->2 a ) )

  proof
    wva
    wvb
    wi2
    #
    @0
    wvb
    wva
    wi2
    wi2
    #
    wva
    wi2
    #
    wi2
    #
    wva
    wvb
    wo
    #
    @3
    @0
    @4
    wi2
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
    wi2
    @4
    @1
    @5
    wva
    wva
    wvb
    ud2lem1
    ud2lem0b
    wva
    wvb
    ud2lem2
    ax-r2
    ud2lem0a
    wva
    wvb
    ud2lem3
    ax-r2
    ax-r1
end
