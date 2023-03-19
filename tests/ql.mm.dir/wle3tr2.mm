include "wr1.mm"
include "wle3tr1.mm"

theorem wle3tr2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume wle3tr2.1: |- ( a =<2 b ) = 1
  assume wle3tr2.2: |- ( a == c ) = 1
  assume wle3tr2.3: |- ( b == d ) = 1


  assert |- ( c =<2 d ) = 1

  proof
    wva
    wvb
    wvc
    wvd
    wle3tr2.1
    wva
    wvc
    wle3tr2.2
    wr1
    wvb
    wvd
    wle3tr2.3
    wr1
    wle3tr1
end
