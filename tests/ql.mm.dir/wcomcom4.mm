include "wn.mm"
include "wcomcom3.mm"
include "wcomcom2.mm"

theorem wcomcom4
  let wva: term a
  let wvb: term b
  assume wcomcom.1: |- C ( a , b ) = 1


  assert |- C ( a ' , b ' ) = 1

  proof
    wva
    wn
    wvb
    wva
    wvb
    wcomcom.1
    wcomcom3
    wcomcom2
end
