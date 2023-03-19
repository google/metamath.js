include "wo.mm"
include "ler.mm"
include "ax-a2.mm"
include "lbtr.mm"

theorem lerr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume le.1: |- a =< b


  assert |- a =< ( c v b )

  proof
    wva
    wvb
    wvc
    wo
    wvc
    wvb
    wo
    wva
    wvb
    wvc
    le.1
    ler
    wvb
    wvc
    ax-a2
    lbtr
end
