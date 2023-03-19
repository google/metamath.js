include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "i3lem1.mm"
include "ax-r5.mm"
include "ax-r1.mm"
include "omln.mm"
include "wi3.mm"
include "df-i3.mm"
include "ax-r2.mm"
include "3tr2.mm"

theorem i3lem4
  let wva: term a
  let wvb: term b
  assume i3lem.1: |- ( a ->3 b ) = 1


  assert |- ( a ' v b ) = 1

  proof
    wva
    wn
    #
    wva
    @0
    wvb
    wo
    #
    wa
    #
    wo
    #
    @0
    wvb
    wa
    @0
    wvb
    wn
    wa
    wo
    #
    @2
    wo
    #
    @1
    wt
    @5
    @3
    @4
    @0
    @2
    wva
    wvb
    i3lem.1
    i3lem1
    ax-r5
    ax-r1
    wva
    wvb
    omln
    @5
    wva
    wvb
    wi3
    #
    wt
    @6
    @5
    wva
    wvb
    df-i3
    ax-r1
    i3lem.1
    ax-r2
    3tr2
end
