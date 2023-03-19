include "wr1.mm"
include "wr2.mm"

theorem w3tr1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume w3tr1.1: |- ( a == b ) = 1
  assume w3tr1.2: |- ( c == a ) = 1
  assume w3tr1.3: |- ( d == b ) = 1


  assert |- ( c == d ) = 1

  proof
    wvc
    wva
    wvd
    w3tr1.2
    wva
    wvb
    wvd
    w3tr1.1
    wvd
    wvb
    w3tr1.3
    wr1
    wr2
    wr2
end
