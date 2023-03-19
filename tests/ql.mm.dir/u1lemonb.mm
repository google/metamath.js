include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "df-i1.mm"
include "ax-r5.mm"
include "or32.mm"
include "df-a.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem u1lemonb
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->1 b ) v b ' ) = 1

  proof
    wva
    wvb
    wi1
    #
    wvb
    wn
    #
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
    @1
    wo
    #
    wt
    @0
    @4
    @1
    wva
    wvb
    df-i1
    ax-r5
    @5
    @2
    @1
    wo
    #
    @3
    wo
    #
    wt
    @2
    @3
    @1
    or32
    @7
    @6
    @6
    wn
    #
    wo
    #
    wt
    @3
    @8
    @6
    wva
    wvb
    df-a
    lor
    wt
    @9
    @6
    df-t
    ax-r1
    ax-r2
    ax-r2
    ax-r2
end
