include "wo.mm"
include "leo.mm"
include "ax-a2.mm"
include "lbtr.mm"

theorem leor
  let wva: term a
  let wvb: term b


  assert |- a =< ( b v a )

  proof
    wva
    wva
    wvb
    wo
    wvb
    wva
    wo
    wva
    wvb
    leo
    wva
    wvb
    ax-a2
    lbtr
end
