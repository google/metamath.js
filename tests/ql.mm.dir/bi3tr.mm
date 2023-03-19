include "wi3.mm"
include "ri3.mm"
include "bi1.mm"
include "wwbmpr.mm"

theorem bi3tr
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume bi3tr.1: |- a = b
  assume bi3tr.2: |- ( b ->3 c ) = 1


  assert |- ( a ->3 c ) = 1

  proof
    wva
    wvc
    wi3
    #
    wvb
    wvc
    wi3
    #
    bi3tr.2
    @0
    @1
    wva
    wvb
    wvc
    bi3tr.1
    ri3
    bi1
    wwbmpr
end
