include "wa.mm"
include "wo.mm"
include "lear.mm"
include "leo.mm"
include "letr.mm"

theorem leao2
  let wva: term a
  let wvb: term b
  let wvc: term c


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
