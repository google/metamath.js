include "wn.mm"
include "wo.mm"
include "wt.mm"
include "or12.mm"
include "df-t.mm"
include "ax-r5.mm"
include "ax-r1.mm"
include "ax-a3.mm"
include "ax-a2.mm"
include "3tr2.mm"
include "ax-r2.mm"
include "df-le2.mm"
include "lor.mm"
include "or1.mm"

theorem sklem
  param wva: term a
  param wvb: term b
  assume sklem.1: |- a =< b


  assert |- ( a ' v b ) = 1

  proof
    wva
    wn
    #
    wva
    wvb
    wo
    #
    wo
    #
    wvb
    wt
    wo
    #
    @0
    wvb
    wo
    #
    wt
    @2
    wva
    @4
    wo
    #
    @3
    @0
    wva
    wvb
    or12
    wva
    @0
    wo
    #
    wvb
    wo
    #
    wt
    wvb
    wo
    #
    @5
    @3
    @8
    @7
    wt
    @6
    wvb
    wva
    df-t
    ax-r5
    ax-r1
    wva
    @0
    wvb
    ax-a3
    wt
    wvb
    ax-a2
    3tr2
    ax-r2
    @1
    wvb
    @0
    wva
    wvb
    sklem.1
    df-le2
    lor
    wvb
    or1
    3tr2
end
