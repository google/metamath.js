include "wi4.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "ud4lem1a.mm"
include "dfb.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem u4lembi
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) ^ ( b ->4 a ) ) = ( a == b )

  proof
    wva
    wvb
    wi4
    wvb
    wva
    wi4
    wa
    wva
    wvb
    wa
    wva
    wn
    wvb
    wn
    wa
    wo
    #
    wva
    wvb
    tb
    #
    wva
    wvb
    ud4lem1a
    @1
    @0
    wva
    wvb
    dfb
    ax-r1
    ax-r2
end
