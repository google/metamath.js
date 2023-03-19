include "wo.mm"
include "leror.mm"
include "ax-a2.mm"
include "le3tr1.mm"

theorem lelor
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume lel.1: |- a =< b


  assert |- ( c v a ) =< ( c v b )

  proof
    wva
    wvc
    wo
    wvb
    wvc
    wo
    wvc
    wva
    wo
    wvc
    wvb
    wo
    wva
    wvb
    wvc
    lel.1
    leror
    wvc
    wva
    ax-a2
    wvc
    wvb
    ax-a2
    le3tr1
end
