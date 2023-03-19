include "wf.mm"
include "wt.mm"
include "wn.mm"
include "wo.mm"
include "df-f.mm"
include "df-t.mm"
include "ax-r4.mm"
include "ax-r2.mm"

theorem dff2
  param wva: term a


  assert |- 0 = ( a v a ' ) '

  proof
    wf
    wt
    wn
    wva
    wva
    wn
    wo
    #
    wn
    df-f
    wt
    @0
    wva
    df-t
    ax-r4
    ax-r2
end
