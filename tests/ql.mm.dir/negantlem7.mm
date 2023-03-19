include "wo.mm"
include "wn.mm"
include "wa.mm"
include "negantlem5.mm"
include "anor3.mm"
include "3tr2.mm"
include "con1.mm"

theorem negantlem7
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a v c ) = ( b v c )

  proof
    wva
    wvc
    wo
    #
    wvb
    wvc
    wo
    #
    wva
    wn
    wvc
    wn
    #
    wa
    wvb
    wn
    @2
    wa
    @0
    wn
    @1
    wn
    wva
    wvb
    wvc
    negant.1
    negantlem5
    wva
    wvc
    anor3
    wvb
    wvc
    anor3
    3tr2
    con1
end
