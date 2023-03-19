include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "ax-a2.mm"
include "ax-a1.mm"
include "2an.mm"
include "lor.mm"
include "ax-r2.mm"
include "dfb.mm"
include "3tr1.mm"

theorem conb
  param wva: term a
  param wvb: term b


  assert |- ( a == b ) = ( a ' == b ' )

  proof
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @3
    @1
    wn
    #
    @2
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    tb
    @1
    @2
    tb
    @4
    @3
    @0
    wo
    @8
    @0
    @3
    ax-a2
    @0
    @7
    @3
    wva
    @5
    wvb
    @6
    wva
    ax-a1
    wvb
    ax-a1
    2an
    lor
    ax-r2
    wva
    wvb
    dfb
    @1
    @2
    dfb
    3tr1
end
