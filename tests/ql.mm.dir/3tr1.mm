include "ax-r1.mm"
include "ax-r2.mm"

theorem 3tr1
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume 3tr1.1: |- a = b
  assume 3tr1.2: |- c = a
  assume 3tr1.3: |- d = b


  assert |- c = d

  proof
    wvc
    wva
    wvd
    3tr1.2
    wva
    wvb
    wvd
    3tr1.1
    wvd
    wvb
    3tr1.3
    ax-r1
    ax-r2
    ax-r2
end
