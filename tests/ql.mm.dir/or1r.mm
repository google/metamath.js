include "wt.mm"
include "wo.mm"
include "ax-a2.mm"
include "or1.mm"
include "ax-r2.mm"

theorem or1r
  param wva: term a


  assert |- ( 1 v a ) = 1

  proof
    wt
    wva
    wo
    wva
    wt
    wo
    wt
    wt
    wva
    ax-a2
    wva
    or1
    ax-r2
end
