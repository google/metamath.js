include "bltr.mm"
include "ax-r1.mm"
include "lbtr.mm"

theorem le3tr1
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume le3tr1.1: |- a =< b
  assume le3tr1.2: |- c = a
  assume le3tr1.3: |- d = b


  assert |- c =< d

  proof
    wvc
    wvb
    wvd
    wvc
    wva
    wvb
    le3tr1.2
    le3tr1.1
    bltr
    wvd
    wvb
    le3tr1.3
    ax-r1
    lbtr
end
