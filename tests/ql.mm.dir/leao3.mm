include "wa.mm"
include "wo.mm"
include "lea.mm"
include "leor.mm"
include "letr.mm"

theorem leao3
  let wva: term a
  let wvb: term b
  let wvc: term c


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
