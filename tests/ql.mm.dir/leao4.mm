include "wa.mm"
include "wo.mm"
include "lear.mm"
include "leor.mm"
include "letr.mm"

theorem leao4
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( b ^ a ) =< ( c v a )

  proof
    wvb
    wva
    wa
    wva
    wvc
    wva
    wo
    wvb
    wva
    lear
    wva
    wvc
    leor
    letr
end
