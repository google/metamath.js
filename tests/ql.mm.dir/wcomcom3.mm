include "wn.mm"
include "wcomcom.mm"
include "wcomcom2.mm"

theorem wcomcom3
  param wva: term a
  param wvb: term b
  assume wcomcom.1: |- C ( a , b ) = 1


  assert |- C ( a ' , b ) = 1

  proof
    wvb
    wva
    wn
    wvb
    wva
    wva
    wvb
    wcomcom.1
    wcomcom
    wcomcom2
    wcomcom
end
