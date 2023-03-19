include "wr1.mm"
include "w3tr1.mm"

theorem w3tr2
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume w3tr2.1: |- ( a == b ) = 1
  assume w3tr2.2: |- ( a == c ) = 1
  assume w3tr2.3: |- ( b == d ) = 1


  assert |- ( c == d ) = 1

  proof
    wva
    wvb
    wvc
    wvd
    w3tr2.1
    wva
    wvc
    w3tr2.2
    wr1
    wvb
    wvd
    w3tr2.3
    wr1
    w3tr1
end
