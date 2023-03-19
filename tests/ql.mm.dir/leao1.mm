include "wa.mm"
include "wo.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"

theorem leao1
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a ^ b ) =< ( a v c )

  proof
    wva
    wvb
    wa
    wva
    wva
    wvc
    wo
    wva
    wvb
    lea
    wva
    wvc
    leo
    letr
end
