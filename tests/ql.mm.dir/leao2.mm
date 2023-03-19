include "wa.mm"
include "wo.mm"
include "lear.mm"
include "leo.mm"
include "letr.mm"

theorem leao2
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( b ^ a ) =< ( a v c )

  proof
    wvb
    wva
    wa
    wva
    wva
    wvc
    wo
    wvb
    wva
    lear
    wva
    wvc
    leo
    letr
end
