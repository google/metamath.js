include "wf.mm"
include "wo.mm"
include "ax-a2.mm"
include "or0.mm"
include "ax-r2.mm"
include "df-le1.mm"

theorem le0
  let wva: term a


  assert |- 0 =< a

  proof
    wf
    wva
    wf
    wva
    wo
    wva
    wf
    wo
    wva
    wf
    wva
    ax-a2
    wva
    or0
    ax-r2
    df-le1
end
