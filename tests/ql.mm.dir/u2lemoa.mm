include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wt.mm"
include "df-i2.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "oran.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r2.mm"

theorem u2lemoa
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) v a ) = 1

  proof
    wva
    wvb
    wi2
    #
    wva
    wo
    wvb
    wva
    wn
    wvb
    wn
    wa
    #
    wo
    #
    wva
    wo
    #
    wt
    @0
    @2
    wva
    wva
    wvb
    df-i2
    ax-r5
    @3
    wva
    @2
    wo
    #
    wt
    @2
    wva
    ax-a2
    @4
    wva
    wvb
    wo
    #
    @1
    wo
    #
    wt
    @6
    @4
    wva
    wvb
    @1
    ax-a3
    ax-r1
    @6
    @1
    @5
    wo
    #
    wt
    @5
    @1
    ax-a2
    @7
    @1
    @1
    wn
    #
    wo
    #
    wt
    @5
    @8
    @1
    wva
    wvb
    oran
    lor
    wt
    @9
    @1
    df-t
    ax-r1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
