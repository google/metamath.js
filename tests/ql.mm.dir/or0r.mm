include "wf.mm"
include "wo.mm"
include "ax-a2.mm"
include "or0.mm"
include "ax-r2.mm"

theorem or0r
  param wva: term a


  assert |- ( 0 v a ) = a

  proof
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
end
