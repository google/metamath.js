include "wo.mm"
include "wa.mm"
include "ml3le.mm"
include "lebi.mm"

theorem ml3
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a v ( b ^ ( c v a ) ) ) = ( a v ( c ^ ( b v a ) ) )

  proof
    wva
    wvb
    wvc
    wva
    wo
    wa
    wo
    wva
    wvc
    wvb
    wva
    wo
    wa
    wo
    wva
    wvb
    wvc
    ml3le
    wva
    wvc
    wvb
    ml3le
    lebi
end
