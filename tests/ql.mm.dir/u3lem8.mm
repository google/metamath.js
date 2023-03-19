include "wn.mm"
include "wi3.mm"
include "wo.mm"
include "wt.mm"
include "comi31.mm"
include "comcom3.mm"
include "u3lemc4.mm"
include "wa.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "u3lem7.mm"
include "2or.mm"
include "ax-a3.mm"
include "ax-a2.mm"
include "df-t.mm"
include "lor.mm"
include "or1.mm"
include "ax-r2.mm"

theorem u3lem8
  param wva: term a
  param wvb: term b


  assert |- ( a ' ->3 ( a ->3 ( a ' ->3 b ) ) ) = 1

  proof
    wva
    wn
    #
    wva
    @0
    wvb
    wi3
    #
    wi3
    #
    wi3
    @0
    wn
    #
    @2
    wo
    #
    wt
    @0
    @2
    wva
    @2
    wva
    @1
    comi31
    comcom3
    u3lemc4
    @4
    wva
    @0
    wva
    wvb
    wa
    wva
    wvb
    wn
    wa
    wo
    #
    wo
    #
    wo
    #
    wt
    @3
    wva
    @2
    @6
    wva
    @3
    wva
    ax-a1
    ax-r1
    wva
    wvb
    u3lem7
    2or
    @7
    wva
    @0
    wo
    #
    @5
    wo
    #
    wt
    @9
    @7
    wva
    @0
    @5
    ax-a3
    ax-r1
    @9
    @5
    @8
    wo
    #
    wt
    @8
    @5
    ax-a2
    @10
    @5
    wt
    wo
    wt
    @8
    wt
    @5
    wt
    @8
    wva
    df-t
    ax-r1
    lor
    @5
    or1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
