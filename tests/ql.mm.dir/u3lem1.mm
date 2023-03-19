include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "comi31.mm"
include "comcom.mm"
include "u3lemc4.mm"
include "u3lemnoa.mm"
include "ax-r2.mm"

theorem u3lem1
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ->3 a ) = ( ( a v b ) ^ ( a v b ' ) )

  proof
    wva
    wvb
    wi3
    #
    wva
    wi3
    @0
    wn
    wva
    wo
    wva
    wvb
    wo
    wva
    wvb
    wn
    wo
    wa
    @0
    wva
    wva
    @0
    wva
    wvb
    comi31
    comcom
    u3lemc4
    wva
    wvb
    u3lemnoa
    ax-r2
end
