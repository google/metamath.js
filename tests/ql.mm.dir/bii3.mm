include "tb.mm"
include "wi3.mm"
include "wa.mm"
include "i3bi.mm"
include "ax-r1.mm"
include "lea.mm"
include "bltr.mm"
include "lei3.mm"

theorem bii3
  let wva: term a
  let wvb: term b


  assert |- ( ( a == b ) ->3 ( a ->3 b ) ) = 1

  proof
    wva
    wvb
    tb
    #
    wva
    wvb
    wi3
    #
    @0
    @1
    wvb
    wva
    wi3
    #
    wa
    #
    @1
    @3
    @0
    wva
    wvb
    i3bi
    ax-r1
    @1
    @2
    lea
    bltr
    lei3
end
