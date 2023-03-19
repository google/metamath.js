include "wbltr.mm"
include "wr1.mm"
include "wlbtr.mm"

theorem wle3tr1
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume wle3tr1.1: |- ( a =<2 b ) = 1
  assume wle3tr1.2: |- ( c == a ) = 1
  assume wle3tr1.3: |- ( d == b ) = 1


  assert |- ( c =<2 d ) = 1

  proof
    wvc
    wvb
    wvd
    wvc
    wva
    wvb
    wle3tr1.2
    wle3tr1.1
    wbltr
    wvd
    wvb
    wle3tr1.3
    wr1
    wlbtr
end
