include "wbltr.mm"
include "wr1.mm"
include "wlbtr.mm"

theorem wle3tr1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
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
