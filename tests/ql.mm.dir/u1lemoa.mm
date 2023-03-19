include "wi1.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wt.mm"
include "df-i1.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "df-t.mm"
include "lor.mm"
include "or1.mm"
include "ax-r2.mm"

theorem u1lemoa
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) v a ) = 1

  proof
    wva
    wvb
    wi1
    #
    wva
    wo
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wva
    wo
    #
    wt
    @0
    @3
    wva
    wva
    wvb
    df-i1
    ax-r5
    @4
    wva
    @3
    wo
    #
    wt
    @3
    wva
    ax-a2
    @5
    wva
    @1
    wo
    #
    @2
    wo
    #
    wt
    @7
    @5
    wva
    @1
    @2
    ax-a3
    ax-r1
    @7
    @2
    @6
    wo
    #
    wt
    @6
    @2
    ax-a2
    @8
    @2
    wt
    wo
    #
    wt
    @9
    @8
    wt
    @6
    @2
    wva
    df-t
    lor
    ax-r1
    @2
    or1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
