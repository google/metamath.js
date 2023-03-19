include "wo.mm"
include "lor.mm"
include "ax-r5.mm"
include "ax-r2.mm"

theorem 2or
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume 2or.1: |- a = b
  assume 2or.2: |- c = d


  assert |- ( a v c ) = ( b v d )

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
    2or.2
    lor
    wva
    wvb
    wvd
    2or.1
    ax-r5
    ax-r2
end
