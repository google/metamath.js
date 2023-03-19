include "wo.mm"
include "wlor.mm"
include "wr5-2v.mm"
include "wr2.mm"

theorem w2or
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume w2or.1: |- ( a == b ) = 1
  assume w2or.2: |- ( c == d ) = 1


  assert |- ( ( a v c ) == ( b v d ) ) = 1

  proof
    wva
    wvc
    wo
    wva
    wvd
    wo
    wvb
    wvd
    wo
    wvc
    wvd
    wva
    w2or.2
    wlor
    wva
    wvb
    wvd
    w2or.1
    wr5-2v
    wr2
end
