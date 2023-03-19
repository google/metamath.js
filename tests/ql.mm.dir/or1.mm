include "wt.mm"
include "wo.mm"
include "wn.mm"
include "df-t.mm"
include "lor.mm"
include "ax-a4.mm"
include "ax-r2.mm"
include "ax-r1.mm"

theorem or1
  let wva: term a


  assert |- ( a v 1 ) = 1

  proof
    wva
    wt
    wo
    #
    wva
    wva
    wn
    wo
    #
    wt
    @0
    wva
    @1
    wo
    @1
    wt
    @1
    wva
    wva
    df-t
    #
    lor
    wva
    wva
    ax-a4
    ax-r2
    wt
    @1
    @2
    ax-r1
    ax-r2
end
