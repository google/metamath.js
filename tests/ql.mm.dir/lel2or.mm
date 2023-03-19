include "wo.mm"
include "le2or.mm"
include "oridm.mm"
include "lbtr.mm"

theorem lel2or
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume lel2.1: |- a =< b
  assume lel2.2: |- c =< b


  assert |- ( a v c ) =< b

  proof
    wva
    wvc
    wo
    wvb
    wvb
    wo
    wvb
    wva
    wvb
    wvc
    wvb
    lel2.1
    lel2.2
    le2or
    wvb
    oridm
    lbtr
end
