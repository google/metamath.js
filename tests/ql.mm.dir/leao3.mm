include "wa.mm"
include "wo.mm"
include "lea.mm"
include "leor.mm"
include "letr.mm"

theorem leao3
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( a ^ b ) =< ( c v a )

  proof
    wva
    wvb
    wa
    wva
    wvc
    wva
    wo
    wva
    wvb
    lea
    wva
    wvc
    leor
    letr
end
