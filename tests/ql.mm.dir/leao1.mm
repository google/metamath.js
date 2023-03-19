include "wa.mm"
include "wo.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"

theorem leao1
  param wva: term a
  param wvb: term b
  param wvc: term c


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
