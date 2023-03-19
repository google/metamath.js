include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wdf-c2.mm"
include "wran.mm"
include "w2or.mm"
include "w3tr1.mm"
include "wdf-c1.mm"

theorem wbctr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wbctr.1: |- ( a == b ) = 1
  assume wbctr.2: |- C ( b , c ) = 1


  assert |- C ( a , c ) = 1

  proof
    wva
    wvc
    wvb
    wvb
    wvc
    wa
    #
    wvb
    wvc
    wn
    #
    wa
    #
    wo
    wva
    wva
    wvc
    wa
    #
    wva
    @1
    wa
    #
    wo
    wvb
    wvc
    wbctr.2
    wdf-c2
    wbctr.1
    @3
    @0
    @4
    @2
    wva
    wvb
    wvc
    wbctr.1
    wran
    wva
    wvb
    @1
    wbctr.1
    wran
    w2or
    w3tr1
    wdf-c1
end
