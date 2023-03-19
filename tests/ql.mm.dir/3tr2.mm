include "ax-r1.mm"
include "3tr1.mm"

theorem 3tr2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume 3tr2.1: |- a = b
  assume 3tr2.2: |- a = c
  assume 3tr2.3: |- b = d


  assert |- c = d

  proof
    wva
    wvb
    wvc
    wvd
    3tr2.1
    wva
    wvc
    3tr2.2
    ax-r1
    wvb
    wvd
    3tr2.3
    ax-r1
    3tr1
end
