include "wo.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "3tr1.mm"

theorem lor
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume lor.1: |- a = b


  assert |- ( c v a ) = ( c v b )

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
    lor.1
    ax-r5
    wvc
    wva
    ax-a2
    wvc
    wvb
    ax-a2
    3tr1
end
